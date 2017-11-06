" Vim syntax file
" Language:     cubicaltt
" Author:       Carlo Angiuli
" Last Change:  2017 November 6
"
" For https://github.com/mortberg/cubicaltt
"
" Move this file to ~/.vim/syntax/ and add the following line to your .vimrc:
"   au BufNewFile,BufRead *.ctt setf cubicaltt

if exists("b:current_syntax")
  finish
endif

syn keyword cttKeyword hdata data import mutual let in split with module where
syn keyword cttKeyword opaque transparent[] transparent_all
syn keyword cttOperator U PathP comp transport fill Glue glue unglue Id idC idJ
syn match   cttOperator '[:=|*_<>\-@]\|->\|\\\|\\/\|/\\'
syn keyword cttUndef undefined

syn region cttComment start="--" end="$"
syn region cttComment start="{-" end="-}"

hi def link cttKeyword Structure
hi def link cttOperator Identifier
hi def link cttUndef Todo
hi def link cttComment Comment

let b:current_syntax = "cubicaltt"
