" Vim syntax file
" Language: Esol

syn keyword esolKeyword type var case run trace 
syn match esolName "\<[A-Z][^ ]*\>"
syn keyword esolBoolean true false
syn match esolInteger "\([(\[{: ]\|^\)\zs[0-9]\+\ze\([)\]}: ]\|$\)"
syn match esolOperator "\( \|^\)\zs\(+\|%\|<\|==\|||\)\ze\( \|$\)"
syn region esolString start=/'/ end=/'/
syn region esolComment start="//" end=/$/

hi def link esolKeyword  Keyword
hi def link esolName     Type
hi def link esolBoolean  Boolean
hi def link esolInteger  Number
hi def link esolOperator Operator
hi def link esolString   String
hi def link esolComment  Comment

let b:current_syntax = "esol"
