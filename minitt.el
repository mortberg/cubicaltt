;; define several class of keywords
(setq minitt-keywords '("data" "import" "mutual" "let" "in" "split"
                     "module" "where" "U") )
(setq minitt-special '("undefined" "primitive"))

;; create regex strings
(setq minitt-keywords-regexp (regexp-opt minitt-keywords 'words))
(setq minitt-operators-regexp (regexp-opt '(":" "->" "=" "\\" "|" "\\" "*" "_") t))
(setq minitt-special-regexp (regexp-opt minitt-special 'words))
(setq minitt-def-regexp "^[[:word:]]+")

;; clear memory
(setq minitt-keywords nil)
(setq minitt-special nil)

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq minitt-font-lock-keywords
  `(
    (,minitt-keywords-regexp . font-lock-type-face)
    (,minitt-operators-regexp . font-lock-variable-name-face)
    (,minitt-special-regexp . font-lock-warning-face)
    (,minitt-def-regexp . font-lock-function-name-face)
))

;; command to comment/uncomment text
(defun minitt-comment-dwim (arg)
  "Comment or uncomment current line or region in a smart way. For detail, see `comment-dwim'."
  (interactive "*P")
  (require 'newcomment)
  (let ((comment-start "--") (comment-end ""))
    (comment-dwim arg)))


;; syntax table for comments, same as for haskell-mode
(defvar minitt-syntax-table
  (let ((st (make-syntax-table)))
       (modify-syntax-entry ?\{  "(}1nb" st)
       (modify-syntax-entry ?\}  "){4nb" st)
       (modify-syntax-entry ?-  "_ 123" st)
       (modify-syntax-entry ?\n ">" st)
   st))

;; define the mode
(define-derived-mode minitt-mode fundamental-mode
  "minitt mode"
  "Major mode for editing minitt files…"

  :syntax-table minitt-syntax-table

  ;; code for syntax highlighting
  (setq font-lock-defaults '(minitt-font-lock-keywords))
  (setq mode-name "minitt")

  ;; modify the keymap
  (define-key minitt-mode-map [remap comment-dwim] 'minitt-comment-dwim)

  ;; clear memory
  (setq minitt-keywords-regexp nil)
  (setq minitt-operators-regexp nil)
  (setq minitt-special-regexp nil)
)

(provide 'minitt-mode)
