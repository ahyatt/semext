;;; semext.el -- Semantic extensions to Emacs functionality -*- lexical-binding: t; -*-

;;; Commentary:

;; This library provides some extensions to the built-in Emacs, using llm
;; functionality.  The goal is to provide new functions that operate like
;; existing functions, but at a semantic level.

;;; Code:

(require 'llm)
(require 'seq)

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
  "The JSON schema we expect to get back in our LLM requests.")

(defvar-local semext--part-points nil
  "The stored points representing the start of a pointhave the buffer text with line numbershave the buffer text with line numbers.")

(defun semext--buffer-text ()
  "Return the buffer text with line numbers prepended to each line."
  (let ((lines nil)
        (line-num 1))
    (save-excursion
      (goto-char (point-min))
      (while (not (eobp))
        (let ((line (buffer-substring-no-properties
                     (line-beginning-position)
                     (line-end-position))))
          (push (format "%d: %s" line-num line) lines)
          (setq line-num (1+ line-num))
          (forward-line 1))))
    (string-join (nreverse lines) "\n")))

(defun semext--populate-parts ()
  "Return points of all part start positions in the buffer."

  ;; We will ask the llm to parse the buffer and return the line number and
  ;; leading several characters of each part.
  (llm-chat-async semext-provider
                  (llm-make-chat-prompt (semext--buffer-text)
                                        :context semext--parts-prompt
                                        :response-format semext--parts-json-schema)
                  (lambda (resp)
                    (message "Received response: %s" resp)
                    (let* ((json-data (json-parse-string resp :object-type 'plist :array-type 'list))
                           (parts (plist-get json-data :parts))
                           (points nil))
                      (dolist (part parts)
                        (let ((line-num (plist-get part :line_num))
                              (start-chars (plist-get part :start_chars)))
                          (save-excursion
                            (goto-char (point-min))
                            (forward-line (1- line-num))
                            (when (search-forward start-chars (line-end-position) t)
                              (backward-char (length start-chars))
                              (push (point) points)))))
                      (setq semext--part-points (nreverse points))))
                  (lambda (_ err) (message "Error getting semantic parts via semext: %s" err))))

(defun semext--part-points ()
  "Return `semext--part-points', populating it if necessary."
  (or semext--part-points
      (progn
        (semext--populate-parts)
        (while (null semext--part-points)
          (sit-for 0.1)))))

(defun semext-forward-part (&optional n)
  "Move point forward to the beginning of the next part."
  (interactive "p")
  (unless (member 'json-response (llm-capabilities semext-provider))
    (error "semext requires a provider that can do json responses"))
  (let* ((points (semext--part-points))
         (next-point (seq-find (lambda (point) (> point (point)))
                               semext--part-points)))
    (when next-point
      (goto-char next-point))))

(defun semext-backward-part (&optional n)
  "Move point backward to the beginning of the previous part."
  (interactive "p")
  (unless (member 'json-response (llm-capabilities semext-provider))
    (error "semext requires a provider that can do json responses"))
  (let* ((points (semext--part-points))
         (prev-point (seq-find (lambda (point) (< point (point)))
                               (reverse semext--part-points))))
    (when prev-point
      (goto-char prev-point))))

(provide 'semext)
;;; semext.el ends here
