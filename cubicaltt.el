;;; cubicaltt.el --- Mode for cubical type theory -*- lexical-binding: t -*-
;; URL: https://github.com/mortberg/cubicaltt
;; Package-version: 1.0
;; Package-Requires: ((emacs "24.1") (cl-lib "0.5"))
;; Keywords: languages

;; This file is not part of GNU Emacs.

;; Copyright (c) 2015 Cyril Cohen, Thierry Coquand, Simon Huber, Anders Mörtberg

;; Permission is hereby granted, free of charge, to any person obtaining
;; a copy of this software and associated documentation files (the
;; "Software"), to deal in the Software without restriction, including
;; without limitation the rights to use, copy, modify, merge, publish,
;; distribute, sublicense, and/or sell copies of the Software, and to
;; permit persons to whom the Software is furnished to do so, subject to
;; the following conditions:

;; The above copyright notice and this permission notice shall be included
;; in all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
;; IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
;; CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
;; TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
;; SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;;; Commentary:
;; This package provides a major mode for editing proofs or programs
;; in cubical, an implementation of cubical type theory.


;;; Code:

(require 'comint)
(require 'cl-lib)

;;;; Customization options

(defgroup ctt nil "Options for ctt-mode for cubical type theory" :group 'languages)

(defcustom ctt-command "cubical"
  "The command to be run for cubical."
  :group 'ctt
  :type 'string
  :options '("cubical" "cabal exec cubical"))

;;;; Syntax

(defvar ctt-keywords
  '("hdata" "data" "import" "mutual" "let" "in" "split"
    "with" "module" "where" "U" "opaque" "visible")
  "Keywords for cubical.")

(defvar ctt-special
  '("undefined" "primitive")
  "Special operators for cubical.")

(defvar ctt-keywords-regexp
  (regexp-opt ctt-keywords 'words)
  "Regexp that recognizes keywords for cubical.")

(defvar ctt-operators-regexp
  (regexp-opt '(":" "->" "=" "|" "\\" "*" "_" "<" ">" "\\/" "/\\" "-" "@") t)
  "Regexp that recognizes operators for cubical.")

(defvar ctt-special-regexp
  (regexp-opt ctt-special 'words)
  "Regexp that recognizes special operators for cubical.")

(defvar ctt-def-regexp "^[[:word:]']+"
  "Regexp that recognizes the beginning of a cubical definition.")

(defvar ctt-font-lock-keywords
  `((,ctt-keywords-regexp . font-lock-type-face)
    (,ctt-operators-regexp . font-lock-variable-name-face)
    (,ctt-special-regexp . font-lock-warning-face)
    (,ctt-def-regexp . font-lock-function-name-face))
  "Font-lock information, assigning each class of keyword a face.")

(defun ctt-comment-dwim (arg)
  "Comment or uncomment current line or region in a smart way, or kill with ARG.

For details, see `comment-dwim'."
  (interactive "*P")
  (require 'newcomment)
  (let ((comment-start "--") (comment-end ""))
    (comment-dwim arg)))

(defvar ctt-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\{  "(}1nb" st)
    (modify-syntax-entry ?\}  "){4nb" st)
    (modify-syntax-entry ?-  "_ 123" st)
    (modify-syntax-entry ?\n ">" st)
    st)
  "The syntax table for cubical, with Haskell-style comments.")


;;;; The interactive toplevel

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
      (comint-send-string cubical-proc (concat ":cd " dir "\n"))
      ;; Load the file
      (comint-send-string cubical-proc (concat ":l " f "\n"))
      ;; Show the buffer
      (pop-to-buffer cubical-proc '(display-buffer-use-some-window (inhibit-same-window . t))))))

;;;; Completion support

(defvar ctt--completion-regexp
  "^\\(?1:[[:word:]']+\\) [:(]\\|^data \\(?1:[[:word:]']+\\)\\|=\\s-*\\(?1:[[:word:]']\\)\\||\\s-*\\(?1:[[:word:]']\\)"
  "Regexp for finding names to complete.

This regexp matches the following kinds of strings:

<NAME> :
<NAME> (
data <NAME>
= <NAME>
| <NAME>

It is overly liberal, but it is better to have too many
suggestions for completion rather than too few.")

(defun ctt-defined-names ()
  "Find all names defined in this buffer."
  (save-excursion
    (let (names)
      (goto-char (point-min))
      (while (re-search-forward ctt--completion-regexp nil t)
        ;; Do not save if inside comment
        (unless (nth 4 (syntax-ppss))
          (push (match-string-no-properties 1) names)))
      names)))

(defun ctt-completion-at-point ()
  "Attempt to perform completion for cubical's keywords and the definitions in this file."
  (when (looking-back "\\w+" nil t)
    (let* ((match (match-string-no-properties 0))
           (start-pos (match-beginning 0))
           (end-pos (match-end 0))
           (candidates (cl-remove-if-not
                        (apply-partially #'string-prefix-p match)
                        (append ctt-keywords
                                ctt-special
                                (ctt-defined-names)))))
      (if (null candidates)
          nil
        (list start-pos end-pos candidates)))))

;;;; The mode itself

;;;###autoload
(define-derived-mode ctt-mode prog-mode
                     "ctt mode"
  "Major mode for editing cubical type theory files."

  :syntax-table ctt-syntax-table

  ;; Code for syntax highlighting
  (setq font-lock-defaults '(ctt-font-lock-keywords))
  (setq mode-name "ctt")

  ;; Modify the keymap
  (define-key ctt-mode-map [remap comment-dwim] 'ctt-comment-dwim)
  (define-key ctt-mode-map (kbd "C-c C-l") 'ctt-load)

  ;; Install the completion handler
  (set (make-local-variable 'completion-at-point-functions)
       '(ctt-completion-at-point))

  ;; Clear memory
  (setq ctt-keywords-regexp nil)
  (setq ctt-operators-regexp nil)
  (setq ctt-special-regexp nil))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ctt\\'" . ctt-mode))

(provide 'cubicaltt)
;;; cubicaltt.el ends here
