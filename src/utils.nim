import
  std/options,
  fusion/matching,
  std/tables

template info*(message: string) =
  stderr.writeLine("INFO: ", message)

template info*(loc: untyped, message: string) =
  stderr.writeLine(loc, ": INFO: ", message)

template note*(message: string) =
  stderr.writeLine("NOTE: ", message)

template note*(loc: untyped, message: string) =
  stderr.writeLine(loc, ": NOTE: ", message)

template warn*(message: string) =
  stderr.writeLine("WARNING: ", message)

template warn*(loc: untyped, message: string) =
  stderr.writeLine(loc, ": WARNING: ", message)

template error*(message: string) =
  stderr.writeLine("ERROR: ", message)

template error*(loc: untyped, message: string) =
  stderr.writeLine(loc, ": ERROR: ", message)

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

proc get*[A, B](t: Table[A, B], key: A): Option[B] =
  if t.contains(key):
    return some(t[key])

proc getKey*[A, B](t: Table[A, B], key: A): Option[A] =
  for keyInTable in t.keys:
    if keyInTable == key: return some(keyInTable)

proc orElse*[T](self: Option[T], `else`: Option[T]): Option[T] =
  if self.isNone(): return `else`

proc andThen*[T](self: Option[T], then: Option[T]): Option[T] =
  if self.isSome(): return then
