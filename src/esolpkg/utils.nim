import
  std/logging,
  std/options

template panic*(args: varargs[string, `$`]) =
  error(args)
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
