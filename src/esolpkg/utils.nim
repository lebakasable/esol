import
  std/options,
  std/strformat

template info*(message: string) =
  stderr.write_line("INFO: ", message)

template info*(loc: untyped, message: string) =
  stderr.write_line(loc, ": INFO: ", message)

template error*(message: string) =
  stderr.write_line("ERROR: ", message)

template error*(loc: untyped, message: string) =
  stderr.write_line(loc, ": ERROR: ", message)

template panic*(message: string) =
  error(message)
  quit(1)

template panic*(prefix: untyped, args: string) =
  error(prefix, args)
  quit(1)
  
proc first*[T](s: seq[T]): Option[T] =
  if s.len > 0:
    result = some(s[0])

proc last*[T](s: seq[T]): Option[T] =
  if s.len > 0:
    result = some(s[s.len-1])

proc shift*[T](s: var seq[T]): Option[T] =
  if s.len > 0:
    result = some(s[0])
    s = s[1..s.len-1]

proc shift*(s: var string): Option[char] =
  if s.len > 0:
    result = some(s[0])
    s = s[1..s.len-1]
