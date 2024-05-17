hook global BufCreate .*[.]esol %{
    set-option buffer filetype esol
}

hook global WinSetOption filetype=esol %<
    require-module esol
>

hook -group esol-highlight global WinSetOption filetype=esol %{
	add-highlighter window/esol ref esol
	hook -once -always window WinSetOption filetype=*. %{ remove-highlighter window/esol }
}

provide-module esol %§
    add-highlighter shared/esol regions
    add-highlighter shared/esol/code default-region group
    add-highlighter shared/esol/comment region '//' $ fill comment

    add-highlighter shared/esol/string_single region '"' (?<!\\)(\\\\)*" fill string
    add-highlighter shared/esol/code/ regex "\b(type|var|trace|run|case|do|input|output|read|write)\b" 0:keyword
§
