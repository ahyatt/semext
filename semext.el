;;; semext.el -- Semantic extensions to Emacs functionality -*- lexical-binding: t; -*-

;; Copyright (c) 2025  Andrew Hyatt <ahyatt@gmail.com>

;; Author: Andrew Hyatt <ahyatt@gmail.com>
;; Homepage: https://github.com/ahyatt/ekg
;; Package-Requires: ((llm "0.24.0"))
;; Keywords: replacement
;; Version: 0.0.1
;; SPDX-License-Identifier: GPL-3.0-or-later
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3 of the
;; License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This library provides some extensions to the built-in Emacs, using llm
;; functionality.  The goal is to provide new functions that operate like
;; existing functions, but at a semantic level.

;;; Code:

(require 'llm)
(require 'seq)
(require 'cl-lib)

(defgroup semext nil
  "Semantic extensions to Emacs functionality."
  :group 'convenience)

(defcustom semext-chunk-size 500
  "Number of lines to send to the LLM at once.
Larger values may provide better semantic understanding but require
more LLM context window space."
  :type 'integer
  :group 'semext)

(defcustom semext-chunk-overlap 10
  "Number of lines to overlap between chunks.
This helps maintain context between chunks."
  :type 'integer
  :group 'semext)

(defvar semext-provider nil
  "The LLM provider to use for semext functionality.

This should be a provider that can do json responses, and is relatively
fast.")

(defconst semext--parts-prompt "You will be given the contents of an Emacs buffer.
Divide the buffer into meaningful semantic units, relatively
fine-grained.  For text documents, these may be parts that introduce new
concepts.  For code, these may be significant parts, such as a function,
or within a function, a significant stanza of code, or the start of
documentation.  The goal is to give the user the most useful points to
navigate between.

To specify the divisions between semantic units, you will supply a line
number (we'll provide them in the Emacs buffer), and the characters
immediately after the division.  This will be used to go to the line and
search for the characters to identify the exact point, which is the
start of the characters.

Return the result as a JSON object."
  "The prompt to use for getting the parts of a buffer.")

(defconst semext--parts-json-schema '(:type object
                                            :properties
                                            (:parts
                                             (:type array
                                                    :items
                                                    (:type object
                                                           :properties
                                                           (:line_num (:type integer)
                                                                      :start_chars (:type string))
                                                           :required ["line_num" "start_chars"]
                                                           :additionalProperties :json-false)))
                                            :additionalProperties :json-false
                                            :required  ["parts"])
  "The JSON schema we expect to get back for finding semantic parts.")

(defconst semext--query-replace-prompt "You will be given the contents of an Emacs buffer and a search/replace request.
Identify all occurrences matching the search description. For each
occurrence, specify the exact start and end location and the text to
replace it with, based on the replacement description.  The
`start_chars` is the first few characters (enough to be unique) occuring
at `start_line_num` that start the location.  The start point is the
beginning of those characters.  The `end_chars` is the last few
characters (again, enough to be unique), that end the location, occuring
at `end_line_num`.  The end point is at the last of those characters.

Return the result as a JSON object."
  "The prompt to use for semantic search and replace.")

(defconst semext--query-replace-json-schema
  '(:type object
          :properties
          (:replacements
           (:type array
                  :items
                  (:type object
                         :properties
                         (:start_line_num (:type integer)
                                          :start_chars (:type string)
                                          :end_line_num (:type integer)
                                          :end_chars (:type string)
                                          :replacement_text (:type string))
                         :required ["start_line_num" "start_chars" "end_line_num" "end_chars" "replacement_text"]
                         :additionalProperties :json-false)))
          :additionalProperties :json-false
          :required ["replacements"])
  "The JSON schema for semantic search and replace responses.")

(defconst semext--search-prompt "You will be given the contents of an Emacs buffer and a search description.
Identify all occurrences matching the search description. For each
occurrence, specify the exact start and end location. The `start_chars`
is the first few characters (enough to be unique) occuring at
`start_line_num` that start the location. The start point is the beginning
of those characters. The `end_chars` is the last few characters (again,
enough to be unique), that end the location, occuring at `end_line_num`.
The end point is at the last of those characters.

Return the result as a JSON object."
  "The prompt to use for semantic search.")

(defconst semext--search-json-schema
  '(:type object
          :properties
          (:occurrences
           (:type array
                  :items
                  (:type object
                         :properties
                         (:start_line_num (:type integer)
                                          :start_chars (:type string)
                                          :end_line_num (:type integer)
                                          :end_chars (:type string))
                         :required ["start_line_num" "start_chars" "end_line_num" "end_chars"]
                         :additionalProperties :json-false)))
          :additionalProperties :json-false
          :required ["occurrences"])
  "The JSON schema for semantic search responses.")


(defvar-local semext--processing-in-progress nil
  "Non-nil when a chunk is currently being processed.")

;; State for multi-chunk operations
(defvar-local semext--aggregated-results nil
  "List to store results aggregated across multiple chunks.")
(defvar-local semext--last-processed-end-point nil
  "The end point of the last chunk processed during a multi-chunk operation.")
(defvar-local semext--active-operation-finalizer nil
  "The function to call once all chunks have been processed.")
(defvar-local semext--active-operation-error-prefix nil
  "The error prefix for the currently active multi-chunk operation.")

(defun semext--buffer-text (&optional start end)
  "Return the buffer text with line numbers prepended to each line.
If START and END are provided, only return text between those positions."
  (let ((lines nil)
        (line-num 1)
        (start-line-num 1))
    (save-excursion
      (goto-char (point-min))
      ;; Count lines until START if provided
      (when start
        (while (and (< (point) start) (not (eobp)))
          (setq line-num (1+ line-num))
          (forward-line 1))
        (setq start-line-num line-num))
      ;; If END is provided, collect lines until END
      ;; Otherwise collect all lines
      (while (and (if end (< (point) end) t)
                  (not (eobp)))
        (let ((line (buffer-substring-no-properties
                     (line-beginning-position)
                     (line-end-position))))
          (push (format "%d: %s" line-num line) lines)
          (setq line-num (1+ line-num))
          (forward-line 1))))
    (cons start-line-num (string-join (nreverse lines) "\n"))))

(defun semext--get-chunk-bounds (point)
  "Get the start and end positions for a chunk centered around POINT."
  (save-excursion
    (goto-char point)
    ;; Move to line beginning
    (beginning-of-line)
    ;; Calculate half chunk size (with overlap consideration)
    (let* ((half-chunk (/ semext-chunk-size 2))
           (chunk-start-line (max 1 (- (line-number-at-pos) half-chunk)))
           (chunk-end-line (+ chunk-start-line semext-chunk-size))
           chunk-start chunk-end)

      ;; Find start position
      (goto-char (point-min))
      (forward-line (1- chunk-start-line))
      (setq chunk-start (point))

      ;; Find end position
      (goto-char (point-min))
      (forward-line (1- chunk-end-line))
      (if (eobp)
          (setq chunk-end (point-max))
        (end-of-line)
        (setq chunk-end (point)))

      (cons chunk-start chunk-end))))

(defun semext--process-buffer-region (start end prompt schema success-callback error-callback &optional context-note)
  "Process the buffer region from START to END using the LLM.
Call LLM with PROMPT and expect response matching SCHEMA.
On success, call SUCCESS-CALLBACK with the parsed JSON data and START-LINE-NUM.
On error, call ERROR-CALLBACK with the error message.
CONTEXT-NOTE is an optional string to add to the prompt context."
  (when semext--processing-in-progress
    (message "Already processing a chunk, skipping request")
    (funcall error-callback "Already processing")
    (cl-return-from semext--process-buffer-region nil))

  (setq semext--processing-in-progress t)
  (message "Processing chunk from line %d to %d..."
           (line-number-at-pos start)
           (line-number-at-pos end))

  (condition-case err
      (let* ((text-with-info (semext--buffer-text start end))
             (start-line-num (car text-with-info))
             (text (cdr text-with-info))
             (full-context (concat prompt
                                   (when context-note (concat "\n" context-note)))))
        (llm-chat-async
         semext-provider
         (llm-make-chat-prompt text :context full-context :response-format schema)
         ;; Success lambda
         (lambda (resp)
           (message "Received response from LLM for chunk")
           (condition-case err
               (let ((json-data (json-parse-string resp :object-type 'plist :array-type 'list)))
                 (funcall success-callback json-data start-line-num))
             (error
              (message "Error processing LLM response: %s" (error-message-string err))
              (funcall error-callback (error-message-string err))))
           ;; Clear processing flag ONLY if successful
           (setq semext--processing-in-progress nil))
         ;; Error lambda
         (lambda (_ err)
           (message "Error during LLM request: %s" err)
           (funcall error-callback err)
           (setq semext--processing-in-progress nil))))
    ;; Error handling for setting up the request
    (error
     (message "Failed to start LLM request: %s" (error-message-string err))
     (funcall error-callback (error-message-string err))
     (setq semext--processing-in-progress nil))))

(defun average-line-length ()
  "Calculate the average length of lines in characters."
  (let ((lines (line-number-at-pos (point-max))))
    (if (> lines 0)
        (/ (- (point-max) (point-min)) lines)
      80))) ; Default if buffer is empty or has no lines

(defun semext-forward-part (&optional n)
  "Move point forward to the beginning of the next semantic part.
With prefix argument N, move forward N parts.
Parts are computed on demand across the entire buffer."
  (interactive "p")
  (setq n (or n 1))
  (let ((original-point (point)))
    (semext--perform-search-action
     semext--parts-prompt
     semext--parts-json-schema
     ;; Finalizer callback
     (lambda (all-parts-points) ; Receives a sorted list of points
       (let* (;; Find points after the original point
              (next-points (seq-filter (lambda (pt) (> pt original-point))
                                       all-parts-points)))
         (if (and next-points (<= n (length next-points)))
             (progn
               (goto-char (nth (1- n) next-points))
               (message "Moved forward %d part(s)" n))
           (message "No further parts found forward"))))
     ;; Error message prefix
     "Error during semantic forward-part")))

(defun semext-backward-part (&optional n)
  "Move point backward to the beginning of the previous semantic part.
With prefix argument N, move backward N parts.
Parts are computed on demand across the entire buffer."
  (interactive "p")
  (setq n (or n 1))
  (let ((original-point (point)))
    (semext--perform-search-action
     semext--parts-prompt
     semext--parts-json-schema
     ;; Finalizer callback
     (lambda (all-parts-points) ; Receives a sorted list of points
       (let* (;; Find points before the original point
              (prev-points (seq-filter (lambda (pt) (< pt original-point))
                                       all-parts-points)))
         (if (and prev-points (<= n (length prev-points)))
             (progn
               ;; Get the nth previous point (list is sorted, so take from end)
               (goto-char (nth (- (length prev-points) n) prev-points))
               (message "Moved backward %d part(s)" n))
           (message "No previous parts found backward"))))
     ;; Error message prefix
     "Error during semantic backward-part")))

(defun semext--find-point-from-line-chars (line-num chars)
  "Find the buffer position corresponding to LINE-NUM and starting CHARS."
  (save-excursion
    (goto-char (point-min))
    (forward-line (1- line-num))
    (when (search-forward chars (line-end-position) t)
      (backward-char (length chars))
      (point))))

(defun semext--perform-search-action (prompt schema finalizer-callback error-message-prefix)
  "Initiate a multi-chunk semantic action across the entire buffer.
Handles provider check, sets up state, and starts processing the first chunk.
PROMPT: The base prompt string for the LLM (chunk info will be added).
SCHEMA: The expected JSON schema for the response.
FINALIZER-CALLBACK: Function to call with the aggregated results list
  once the entire buffer is processed. It receives (results).
ERROR-MESSAGE-PREFIX: String to prefix error messages with."
  (unless (member 'json-response (llm-capabilities semext-provider))
    (error "semext requires a provider that can do json responses"))
  (when semext--active-operation-finalizer
    (message "Warning: Overwriting an existing semantic operation"))

  ;; Reset state for the new operation
  (setq semext--aggregated-results nil
        semext--last-processed-end-point (point-min) ; Start tracking from point-min
        semext--active-operation-finalizer finalizer-callback
        semext--active-operation-error-prefix error-message-prefix)

  (message "Starting semantic operation...")
  ;; Start processing from the beginning of the buffer
  (semext--process-next-chunk prompt schema))

(defun semext--process-next-chunk (prompt schema)
  "Calculate bounds for the next chunk starting after the last processed point and call the LLM processor."
  ;; Calculate next chunk start point considering overlap
  (let* ((next-chunk-start (max (point-min)
                                (- semext--last-processed-end-point
                                   (* semext-chunk-overlap (average-line-length)))))
         (bounds (semext--get-chunk-bounds next-chunk-start))
         (chunk-start (car bounds))
         (chunk-end (cdr bounds)))

    ;; Check if the new chunk start is already beyond the last processed end point.
    ;; This indicates we've covered the buffer.
    (if (>= chunk-start semext--last-processed-end-point)
        ;; If last processed point was already point-max, we are done.
        ;; Otherwise, if chunk_start >= last_end, and last_end wasn't point_max,
        ;; it means get-chunk-bounds might have clamped to point-max, process this last chunk.
        (if (= semext--last-processed-end-point (point-max))
            (progn ;; Already finished, do nothing here.
              (message "Semantic operation complete (final check detected).")
              ;; The finalizer call and state clearing will happen in the
              ;; semext--handle-chunk-response instance that detected
              ;; last-processed-end-point reached point-max.
              nil) ; Explicitly do nothing
          ;; Process the potentially final chunk (e.g., if buffer size < chunk size)
          (semext--process-buffer-region-wrapper chunk-start chunk-end prompt schema))
      ;; Process the calculated chunk
      (semext--process-buffer-region-wrapper chunk-start chunk-end prompt schema))))


(defun semext--process-buffer-region-wrapper (chunk-start chunk-end prompt schema)
  "Wrapper to call semext--process-buffer-region with the chunk-aware callback."
  (semext--process-buffer-region
   chunk-start chunk-end
   prompt schema
   ;; Success callback - pass chunk_end along
   (lambda (json-data start-line-num)
     (semext--handle-chunk-response json-data start-line-num chunk-end prompt schema))
   ;; Error callback
   (lambda (err)
     (message "%s: %s" semext--active-operation-error-prefix err)
     (setq semext--active-operation-finalizer nil)) ; Clear state on error
   ;; Context note
   "Note: The line numbers provided are relative to the excerpt you're analyzing."))


(defun semext--handle-chunk-response (json-data start-line-num chunk-end prompt schema)
  "Handle the response for a single chunk, aggregate results, and trigger next chunk or finalizer."
  ;; Process results for this chunk based on the response structure
  (let ((new-results (cond ((plist-member json-data :replacements)
                            (semext--process-query-replace-results json-data start-line-num))
                           ((plist-member json-data :occurrences)
                            (semext--process-search-results json-data start-line-num))
                           ((plist-member json-data :parts)
                            (semext--process-parts-results json-data start-line-num))
                           (t
                            (message "Warning: Unknown JSON response structure received")
                            nil))))
    (when new-results
      ;; Append results directly; duplicates will be handled after sorting.
      (setq semext--aggregated-results (append semext--aggregated-results new-results)))

    ;; Update the point up to which we have processed
    (setq semext--last-processed-end-point (max semext--last-processed-end-point chunk-end))

    ;; Check if we've processed the entire buffer
    (if (< semext--last-processed-end-point (point-max))
        ;; More buffer to process, trigger next chunk
        (progn
          (message "Processed up to line %d. Requesting next chunk..." (line-number-at-pos semext--last-processed-end-point))
          (semext--process-next-chunk prompt schema))
      ;; End of buffer reached, sort, remove duplicates, and call the finalizer
      (message "Semantic operation complete.")
      (let ((sorted-unique-results (seq-uniq (sort-results semext--aggregated-results))))
        (funcall semext--active-operation-finalizer sorted-unique-results))
      ;; Clear state
      (setq semext--active-operation-finalizer nil
            semext--aggregated-results nil
            semext--last-processed-end-point nil
            semext--active-operation-error-prefix nil))))

;; Helper to sort results consistently (by start point)
(defun sort-results (results)
  "Sort RESULTS list. Assumes list of points, plists with :start, or cons cells."
  (when results
    (let ((is-point-list (numberp (car results))))
      (sort results (lambda (a b)
                      (let ((val-a (if is-point-list a (if (consp a) (car a) (plist-get a :start))))
                            (val-b (if is-point-list b (if (consp b) (car b) (plist-get b :start)))))
                        (< val-a val-b)))))))

(defun semext-query-replace (search-query replace-query)
  "Perform semantic search for SEARCH-QUERY and replace with REPLACE-QUERY.
Processes the entire buffer chunk by chunk, then interactively asks for each replacement."
  (interactive "sSearch query: \nsReplace query: ")
  (let ((prompt (format "%s\n\nSearch Description: %s\nReplacement Description: %s"
                        semext--query-replace-prompt search-query replace-query)))
    (semext--perform-search-action
     prompt
     semext--query-replace-json-schema
     ;; Finalizer callback (runs after all chunks are processed)
     (lambda (all-results)
       (let ((marker-pairs nil) ; List to store (start-marker end-marker replacement-text)
             (applied-count 0))
         (if (not all-results)
             (message "LLM did not identify any replacements in the buffer.")
           ;; 1. Create markers from aggregated results
           (dolist (res all-results)
             (push (list (copy-marker (plist-get res :start))
                         (copy-marker (plist-get res :end))
                         (plist-get res :replacement))
                   marker-pairs))
           ;; Markers created, now process interactively (results are already sorted)
           (setq marker-pairs (nreverse marker-pairs)) ; Reverse push order to get buffer order
           (dolist (pair marker-pairs)
             (let ((start-marker (nth 0 pair))
                   (end-marker (nth 1 pair))
                   (replacement-text (nth 2 pair)))
               (when (and (marker-position start-marker) (marker-position end-marker)) ; Check if markers are still valid
                 (goto-char (marker-position start-marker))
                 (push-mark (marker-position end-marker) t t) ; Highlight region
                 (let ((original-text (buffer-substring-no-properties
                                       (marker-position start-marker)
                                       (marker-position end-marker))))
                   (if (y-or-n-p (format "Replace '%s' with '%s'? "
                                         (truncate-string-to-width original-text 40 nil nil "...")
                                         (truncate-string-to-width replacement-text 40 nil nil "...")))
                       (progn
                         (delete-region (marker-position start-marker) (marker-position end-marker))
                         (insert replacement-text)
                         (cl-incf applied-count))))
                 ;; Ensure mark is deactivated regardless of user choice
                 (deactivate-mark))
               ;; Clean up markers after processing
               (set-marker start-marker nil)
               (set-marker end-marker nil)))
           (message "Finished query-replace. Applied %d replacements." applied-count))))
     ;; Error message prefix
     "Error during semantic query-replace")))

(defun semext--process-parts-results (json-data start-line-num)
  "Process JSON parts results and return a list of points.
START-LINE-NUM is the starting line number of the processed chunk."
  (let ((parts (plist-get json-data :parts))
        (points nil))
    (when parts
      (dolist (part parts)
        (let* ((line-num (+ (1- start-line-num) (plist-get part :line_num)))
               (start-chars (plist-get part :start_chars))
               (point (semext--find-point-from-line-chars line-num start-chars)))
          (when point
            (push point points)))))
    ;; Return points found in this chunk (sorting happens after aggregation)
    points))

(defun semext--process-query-replace-results (json-data start-line-num)
  "Process JSON query-replace results and return a list of plists.
Each plist is (:start START :end END :replacement TEXT).
START-LINE-NUM is the starting line number of the processed chunk."
  (let ((replacements (plist-get json-data :replacements))
        (results nil))
    (when replacements
      (dolist (rep replacements)
        (let* ((rep-start-line (+ (1- start-line-num) (plist-get rep :start_line_num)))
               (rep-start-chars (plist-get rep :start_chars))
               (rep-end-line (+ (1- start-line-num) (plist-get rep :end_line_num)))
               (rep-end-chars (plist-get rep :end_chars))
               (replacement-text (plist-get rep :replacement_text))
               (start-point (semext--find-point-from-line-chars rep-start-line rep-start-chars))
               (end-point (save-excursion
                            (when-let ((p (semext--find-point-from-line-chars rep-end-line rep-end-chars)))
                              (when p (+ p (length rep-end-chars)))))))
          (when (and start-point end-point (> end-point start-point))
            (push (list :start start-point :end end-point :replacement replacement-text)
                  results)))))
    ;; Return in buffer order (reverse the pushed list)
    (nreverse results)))


(defun semext--process-search-results (json-data start-line-num)
  "Process JSON search results and return a sorted list of (START . END) point pairs.
START-LINE-NUM is the starting line number of the processed chunk."
  (let ((occurrences (plist-get json-data :occurrences))
        (point-pairs nil))
    (when occurrences
      (dolist (occ occurrences)
        (let* ((occ-start-line (+ (1- start-line-num) (plist-get occ :start_line_num)))
               (occ-start-chars (plist-get occ :start_chars))
               (occ-end-line (+ (1- start-line-num) (plist-get occ :end_line_num)))
               (occ-end-chars (plist-get occ :end_chars))
               (start-point (semext--find-point-from-line-chars occ-start-line occ-start-chars))
               (end-point (save-excursion
                            (when-let ((p (semext--find-point-from-line-chars occ-end-line occ-end-chars)))
                              (when p (+ p (length occ-end-chars)))))))
          (when (and start-point end-point (> end-point start-point))
            (push (cons start-point end-point) point-pairs)))))
    ;; Sort by start point
    (sort point-pairs (lambda (a b) (< (car a) (car b))))))

(defun semext-search-forward (search-query)
  "Perform semantic search forward for SEARCH-QUERY across the entire buffer.
Processes the buffer chunk by chunk, then moves point to the first
occurrence after the initial point and highlights it."
  (interactive "sSearch forward: ")
  (let ((original-point (point))
        (prompt (format "%s\n\nSearch Description: %s"
                        semext--search-prompt search-query)))
    (semext--perform-search-action
     prompt
     semext--search-json-schema
     ;; Finalizer callback
     (lambda (all-results)
       (let* (;; Results are already sorted by start point
              (found-pair (seq-find (lambda (pair) (> (car pair) original-point))
                                    all-results)))
         (if found-pair
             (progn
               (goto-char (car found-pair))
               (push-mark (cdr found-pair) t t)
               (message "Found occurrence forward"))
           (message "Search forward failed: No further occurrences found"))))
     ;; Error message prefix
     "Error during semantic search forward")))

(defun semext-search-backward (search-query)
  "Perform semantic search backward for SEARCH-QUERY across the entire buffer.
Processes the buffer chunk by chunk, then moves point to the first
occurrence ending before the initial point and highlights it."
  (interactive "sSearch backward: ")
  (let ((original-point (point))
        (prompt (format "%s\n\nSearch Description: %s"
                        semext--search-prompt search-query)))
    (semext--perform-search-action
     prompt
     semext--search-json-schema
     ;; Finalizer callback
     (lambda (all-results)
       (let* ( ;; Results are sorted. Find the last one ending before original-point.
              (found-pair (car (seq-filter (lambda (pair) (< (cdr pair) original-point))
                                           (reverse all-results))))) ; Reverse sorted list to find last easily
         (if found-pair
             (progn
               (goto-char (car found-pair))
               (push-mark (cdr found-pair) t t)
               (message "Found occurrence backward"))
           (message "Search backward failed: No previous occurrences found"))))
     ;; Error message prefix
     "Error during semantic search backward")))

(provide 'semext)

;;; semext.el ends here
