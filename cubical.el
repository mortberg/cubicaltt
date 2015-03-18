;; define several class of keywords
(setq cubical-keywords '("data" "import" "mutual" "let" "in" "split"
                     "module" "where" "U") )
(setq cubical-special '("undefined" "primitive"))

;; create regex strings
(setq cubical-keywords-regexp (regexp-opt cubical-keywords 'words))
(setq cubical-operators-regexp (regexp-opt '(":" "->" "=" "\\" "|" "\\" "*" "_") t))
(setq cubical-special-regexp (regexp-opt cubical-special 'words))
(setq cubical-def-regexp "^[[:word:]]+")

;; clear memory
(setq cubical-keywords nil)
(setq cubical-special nil)

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq cubical-font-lock-keywords
  `(
    (,cubical-keywords-regexp . font-lock-type-face)
    (,cubical-operators-regexp . font-lock-variable-name-face)
    (,cubical-special-regexp . font-lock-warning-face)
    (,cubical-def-regexp . font-lock-function-name-face)
))

;; command to comment/uncomment text
(defun cubical-comment-dwim (arg)
  "Comment or uncomment current line or region in a smart way. For detail, see `comment-dwim'."
  (interactive "*P")
  (require 'newcomment)
  (let ((comment-start "--") (comment-end ""))
    (comment-dwim arg)))


;; syntax table for comments, same as for haskell-mode
(defvar cubical-syntax-table
  (let ((st (make-syntax-table)))
       (modify-syntax-entry ?\{  "(}1nb" st)
       (modify-syntax-entry ?\}  "){4nb" st)
       (modify-syntax-entry ?-  "_ 123" st)
       (modify-syntax-entry ?\n ">" st)
   st))

;; define the mode
(define-derived-mode cubical-mode fundamental-mode
  "cubical mode"
  "Major mode for editing cubical files…"

  :syntax-table cubical-syntax-table

  ;; code for syntax highlighting
  (setq font-lock-defaults '(cubical-font-lock-keywords))
  (setq mode-name "cubical")

  ;; modify the keymap
  (define-key cubical-mode-map [remap comment-dwim] 'cubical-comment-dwim)

  ;; clear memory
  (setq cubical-keywords-regexp nil)
  (setq cubical-operators-regexp nil)
  (setq cubical-special-regexp nil)
)

(provide 'cubical-mode)
