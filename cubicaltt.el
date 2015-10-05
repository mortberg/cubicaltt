;; define several class of keywords
(setq ctt-keywords '("hdata" "data" "import" "mutual" "let" "in" "split"
                     "module" "where" "U") )
(setq ctt-special '("undefined" "primitive"))

;; create regex strings
(setq ctt-keywords-regexp (regexp-opt ctt-keywords 'words))
(setq ctt-operators-regexp
      (regexp-opt '(":" "->" "=" "|" "\\" "*" "_" "<" ">" "\\/" "/\\" "-" "@") t))
(setq ctt-special-regexp (regexp-opt ctt-special 'words))
(setq ctt-def-regexp "^[[:word:]']+")

;; clear memory
(setq ctt-keywords nil)
(setq ctt-special nil)

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq ctt-font-lock-keywords
  `(
    (,ctt-keywords-regexp . font-lock-type-face)
    (,ctt-operators-regexp . font-lock-variable-name-face)
    (,ctt-special-regexp . font-lock-warning-face)
    (,ctt-def-regexp . font-lock-function-name-face)
))

;; command to comment/uncomment text
(defun ctt-comment-dwim (arg)
  "Comment or uncomment current line or region in a smart way. For detail, see `comment-dwim'."
  (interactive "*P")
  (require 'newcomment)
  (let ((comment-start "--") (comment-end ""))
    (comment-dwim arg)))


;; syntax table for comments, same as for haskell-mode
(defvar ctt-syntax-table
  (let ((st (make-syntax-table)))
       (modify-syntax-entry ?\{  "(}1nb" st)
       (modify-syntax-entry ?\}  "){4nb" st)
       (modify-syntax-entry ?-  "_ 123" st)
       (modify-syntax-entry ?\n ">" st)
   st))

;; define the mode
(define-derived-mode ctt-mode fundamental-mode
  "ctt mode"
  "Major mode for editing cubical type theory files."

  :syntax-table ctt-syntax-table

  ;; code for syntax highlighting
  (setq font-lock-defaults '(ctt-font-lock-keywords))
  (setq mode-name "ctt")

  ;; modify the keymap
  (define-key ctt-mode-map [remap comment-dwim] 'ctt-comment-dwim)

  ;; clear memory
  (setq ctt-keywords-regexp nil)
  (setq ctt-operators-regexp nil)
  (setq ctt-special-regexp nil)
)

(provide 'ctt-mode)
