import
  ./utils,
  std/strutils,
  std/options,
  std/enumerate,
  fusion/matching,
  std/streams,
  std/strformat

type
  Location* = object
    file_path*: string
    row*: int
    col*: int
  Symbol* = object
    name*: string
    loc*: Location
  Lexer* = object
    symbols*: seq[Symbol]
    loc*: Location

proc `$`*(self: Location): string = &"{self.file_path}:{self.row}:{self.col}"
proc `$`*(self: Symbol): string = self.name
proc `==`*(self, other: Symbol): bool = self.name == other.name

proc tokenize*(file_path: string, source: string): Lexer =
  var loc = Location(file_path: file_path, row: 1, col: 1)
  var last_word_len = 0

  let lines = source.split_lines()
  for line in lines:
    if not line.starts_with("//"):
      let words = line.split_whitespace()
      for word in words:
        var word = word
        loc.col += last_word_len
  
        if word.len > 1 and word[0] in ['(', '{', ':']:
          result.symbols.add(Symbol(name: $word[0], loc: loc))
          discard word.shift()
          loc.col += 1
        if word.len > 1 and word[word.len-1] in [')', '}', ':']:
          result.symbols.add(Symbol(name: $word[word.len-2], loc: loc))
          discard word.shift()
          loc.col += word.len

        result.symbols.add(Symbol(name: word, loc: loc))
        last_word_len = word.len + 1
    loc.row += 1
    loc.col = 0
    last_word_len = 1

proc next*(self: var Lexer): Option[Symbol] =
  if self.symbols.len > 0:
    result = some(self.symbols[0])
    self.symbols = self.symbols[1..self.symbols.len-1]
    self.loc = result.get.loc

proc peek*(self: Lexer): Option[Symbol] =
  if self.symbols.len > 0:
    return some(self.symbols[0])

proc parse_symbol*(self: var Lexer): Symbol =
  if Some(@symbol) ?= self.next:
    return symbol
  else:
    panic self.loc, "Expected symbol but reached the end of the input."

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
  panic self.loc, "Expected {buffer.data} but got `{symbol}`."
