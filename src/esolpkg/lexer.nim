import
  ./utils,
  std/strutils,
  std/options,
  std/sequtils,
  std/enumerate,
  fusion/matching,
  std/streams

type
  Symbol* = object
    name*: string
  # TODO: proper lexer so symbols have a location
  Lexer* = seq[string]

proc new_lexer*(source: string): Lexer =
  source
    .multi_replace(
      ("(", " ( "), (")", " ) "), 
      ("{", " { "), ("}", " } "), 
      (":", " : "),
    )
    .multi_replace(
      ("' ( '", "'('"), ("' ) '", "')'"), 
      ("' { '", "'{'"), ("' } '", "'}'"), 
      ("' : '", "':'"),
    )
    .split_lines
    .map_it(it.split("//")[0]).join(" ")
    .split
    .filter_it(it != "")

proc next*(self: var Lexer): Option[string] =
  if self.len > 0:
    result = some(self[0])
    self = self[1..self.len-1]

proc next_symbol*(self: var Lexer): Option[Symbol] =
  if Some(@name) ?= self.next:
    return some(Symbol(name: name))

proc peek*(self: Lexer): Option[string] =
  if self.len > 0:
    return some(self[0])

proc peek_symbol*(self: var Lexer): Option[Symbol] =
  if Some(@name) ?= self.peek:
    return some(Symbol(name: name))

proc parse_symbol*(self: var Lexer): Symbol =
  if Some(@name) ?= self.next:
    return Symbol(name: name)
  else:
    panic "Expected symbol but reached the end of the input."
    
proc expect_symbol*(self: var Lexer, expected_names: varargs[string]): Symbol =
  let symbol = self.parse_symbol()
  for name in expected_names:
    if symbol.name == name:
      return symbol
  var buffer = new_string_stream()
  for i, name in enumerate(expected_names):
    if i == 0:
      buffer.write "`", name, "`"
    elif i + 1 == expected_names.len:
      buffer.write ", or `", name, "`"
    else:
      buffer.write ", `", name, "`"
  panic "Expected ", buffer.data, " but got `", symbol.name, "`."
