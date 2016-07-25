;; define several class of keywords
(setq ctt-keywords '("hdata" "data" "import" "mutual" "let" "in" "split"
                     "with" "module" "where" "U" "opaque" "visible") )
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


(defgroup ctt nil "Options for ctt-mode for cubical type theory" :group 'languages)

(defcustom ctt-command "cubical"
  "The command to be run for cubical."
  :group 'ctt
  :type 'string
  :options '("cubical" "cabal exec cubical"))

(defvar *ctt-cubical-process* nil
  "The subprocess buffer for cubical.")

(defvar *ctt-loaded-buffer* nil
  "The currently-loaded buffer for cubical.

If no buffer is loaded, then this variable is nil.")


(defun ctt-ensure-process ()
  "Ensure that a process is running for cubical and return the process buffer."
  (if (and *ctt-cubical-process* (get-buffer-process *ctt-cubical-process*))
      *ctt-cubical-process*
    (let ((process (make-comint "cubical" ctt-command)))
      (setq *ctt-cubical-process* process)
      process)))


(defun ctt-load ()
  "Start cubical if it is not running, and get the current buffer loaded."
  (interactive)
  (let ((file (buffer-file-name)))
    (unless file
      (error "The current buffer is not associated with a file"))
    (let ((cubical-proc (ctt-ensure-process))
          (dir (file-name-directory file))
          (f (file-name-nondirectory file)))
      (save-buffer)
      ;; Get in the right working directory. No space-escaping is
      ;; necessary for cubical.
      (comint-send-string *ctt-cubical-process* (concat ":cd " dir "\n"))
      ;; Load the file
      (comint-send-string *ctt-cubical-process* (concat ":l " f "\n"))
      ;; Show the buffer
      (pop-to-buffer *ctt-cubical-process* '(display-buffer-use-some-window (inhibit-same-window . t))))))


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
  (define-key ctt-mode-map (kbd "C-c C-l") 'ctt-load)

  ;; clear memory
  (setq ctt-keywords-regexp nil)
  (setq ctt-operators-regexp nil)
  (setq ctt-special-regexp nil))

(provide 'ctt-mode)
