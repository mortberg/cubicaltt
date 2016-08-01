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

(defgroup cubicaltt nil "Options for cubicaltt-mode for cubical type theory"
  :group 'languages
  :prefix 'cubicaltt
  :tag "Cubical type theory")

(defcustom cubicaltt-command "cubical"
  "The command to be run for cubical."
  :group 'ctt
  :type 'string
  :tag "Command for cubical"
  :options '("cubical" "cabal exec cubical"))

;;;; Syntax

(defvar cubicaltt-keywords
  '("hdata" "data" "import" "mutual" "let" "in" "split"
    "with" "module" "where" "U" "opaque" "visible")
  "Keywords for cubical.")

(defvar cubicaltt-special
  '("undefined" "primitive")
  "Special operators for cubical.")

(defvar cubicaltt-keywords-regexp
  (regexp-opt cubicaltt-keywords 'words)
  "Regexp that recognizes keywords for cubical.")

(defvar cubicaltt-operators-regexp
  (regexp-opt '(":" "->" "=" "|" "\\" "*" "_" "<" ">" "\\/" "/\\" "-" "@") t)
  "Regexp that recognizes operators for cubical.")

(defvar cubicaltt-special-regexp
  (regexp-opt cubicaltt-special 'words)
  "Regexp that recognizes special operators for cubical.")

(defvar cubicaltt-def-regexp "^[[:word:]']+"
  "Regexp that recognizes the beginning of a cubical definition.")

(defvar cubicaltt-font-lock-keywords
  `((,cubicaltt-keywords-regexp . font-lock-type-face)
    (,cubicaltt-operators-regexp . font-lock-variable-name-face)
    (,cubicaltt-special-regexp . font-lock-warning-face)
    (,cubicaltt-def-regexp . font-lock-function-name-face))
  "Font-lock information, assigning each class of keyword a face.")

(defvar cubicaltt-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?\{  "(}1nb" st)
    (modify-syntax-entry ?\}  "){4nb" st)
    (modify-syntax-entry ?-  "_ 123" st)
    (modify-syntax-entry ?\n ">" st)
    st)
  "The syntax table for cubical, with Haskell-style comments.")


;;;; The interactive toplevel

(defvar cubicaltt-cubical-process nil
  "The subprocess buffer for cubical.")

(defvar cubicaltt-loaded-buffer nil
  "The currently-loaded buffer for cubical.

If no buffer is loaded, then this variable is nil.")

(defun cubicaltt-ensure-process ()
  "Ensure that a process is running for cubical and return the process buffer."
  (if (and cubicaltt-cubical-process (get-buffer-process cubicaltt-cubical-process))
      cubicaltt-cubical-process
    (let ((process (make-comint "cubical" cubicaltt-command)))
      (setq cubicaltt-cubical-process process)
      process)))

(defun cubicaltt-load ()
  "Start cubical if it is not running, and get the current buffer loaded."
  (interactive)
  (let ((file (buffer-file-name)))
    (unless file
      (error "The current buffer is not associated with a file"))
    (let ((cubical-proc (cubicaltt-ensure-process))
          (dir (file-name-directory file))
          (f (file-name-nondirectory file)))
      (save-buffer)
      ;; Get in the right working directory. No space-escaping is
      ;; necessary for cubical, which in fact expects filenames to be
      ;; written without quotes or space-escaping.
      (comint-send-string cubical-proc (concat ":cd " dir "\n"))
      ;; Load the file
      (comint-send-string cubical-proc (concat ":l " f "\n"))
      ;; Show the buffer
      (pop-to-buffer cubical-proc '(display-buffer-use-some-window (inhibit-same-window . t))))))

;;;; Completion support

(defvar cubicaltt--completion-regexp
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

(defun cubicaltt-defined-names ()
  "Find all names defined in this buffer."
  (save-excursion
    (let (names)
      (goto-char (point-min))
      (while (re-search-forward cubicaltt--completion-regexp nil t)
        ;; Do not save if inside comment
        (unless (nth 4 (syntax-ppss))
          (push (match-string-no-properties 1) names)))
      names)))

(defun cubicaltt-completion-at-point ()
  "Attempt to perform completion for cubical's keywords and the definitions in this file."
  (when (looking-back "\\w+" nil t)
    (let* ((match (match-string-no-properties 0))
           (start-pos (match-beginning 0))
           (end-pos (match-end 0))
           (candidates (cl-remove-if-not
                        (apply-partially #'string-prefix-p match)
                        (append cubicaltt-keywords
                                cubicaltt-special
                                (cubicaltt-defined-names)))))
      (if (null candidates)
          nil
        (list start-pos end-pos candidates)))))

;;;; The mode itself

;;;###autoload
(define-derived-mode cubicaltt-mode prog-mode
  "ctt"
  "Major mode for editing cubical type theory files."

  :syntax-table cubicaltt-syntax-table

  ;; Make comment-dwim do the right thing for Cubical
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-end) "")

  ;; Code for syntax highlighting
  (setq font-lock-defaults '(cubicaltt-font-lock-keywords))

  ;; Bind mode-specific commands to keys
  (define-key cubicaltt-mode-map (kbd "C-c C-l") 'cubicaltt-load)

  ;; Install the completion handler
  (set (make-local-variable 'completion-at-point-functions)
       '(cubicaltt-completion-at-point))

  ;; Setup imenu, to allow tools such as imenu and Helm to jump
  ;; directly to names in the current buffer.
  (set (make-local-variable 'imenu-generic-expression)
       '(("Definitions" "^\\(?1:[[:word:]']+\\) *[:(]" 1)
         ("Datatypes" "^\\s-*data\\s-+\\(?1:[[:word:]']+\\)" 1)))

  ;; Clear memory
  (setq cubicaltt-keywords-regexp nil)
  (setq cubicaltt-operators-regexp nil)
  (setq cubicaltt-special-regexp nil))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.ctt\\'" . cubicaltt-mode))

(provide 'cubicaltt)
;;; cubicaltt.el ends here
