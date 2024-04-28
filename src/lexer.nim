import
  ./utils,
  std/strutils,
  std/options,
  std/enumerate,
  fusion/matching,
  std/streams,
  std/strformat,
  std/hashes

const SPECIAL = (['(', '{', '['],
                 [')', '}', ']', ':'])
  
type
  Location* = object
    filePath*: string
    row*: int
    col*: int
  Symbol* = object
    name*: string
    loc*: Location
  Lexer* = object
    symbols*: seq[Symbol]
    loc*: Location

proc `$`*(self: Location): string = &"{self.filePath}:{self.row}:{self.col}"
proc `$`*(self: Symbol): string = self.name
proc `==`*(self, other: Symbol): bool = self.name == other.name
proc hash*(self: Symbol): Hash = self.name.hash()

proc tokenize*(filePath: string, source: string): Lexer =
  var loc = Location(filePath: filePath, row: 1, col: 1)
  var lastWordLen = 0

  let lines = source.splitLines()
  for line in lines:
    if not line.startsWith("//"):
      let words = line.splitWhitespace()
      for word in words:
        var word = word
        loc.col += lastWordLen
  
        if word.len > 1 and word[0] in SPECIAL[0]:
          result.symbols.add(Symbol(name: $word[0], loc: loc))
          discard word.shift()
          loc.col += 1
        if word.len > 1 and word[word.len-1] in SPECIAL[1]:
          result.symbols.add(Symbol(name: word[0..word.len-2], loc: loc))
          word = $word[word.len-1]
          loc.col += word.len

        result.symbols.add(Symbol(name: word, loc: loc))
        lastWordLen = word.len + 1
    loc.row += 1
    loc.col = 0
    lastWordLen = 1

proc next*(self: var Lexer): Option[Symbol] =
  if self.symbols.len > 0:
    result = some(self.symbols[0])
    self.symbols = self.symbols[1..self.symbols.len-1]
    self.loc = result.get.loc

proc peek*(self: Lexer): Option[Symbol] =
  if self.symbols.len > 0:
    return some(self.symbols[0])

proc expectSymbol*(self: var Lexer, expectedNames: varargs[string]): Symbol =
  if expectedNames.len == 0:
    if Some(@symbol) ?= self.next:
      return symbol
    else:
      panic self.loc, "Expected symbol but reached the end of the input."
  else:
    let symbol = self.expectSymbol()
    for name in expectedNames:
      if symbol.name == name:
        return symbol
    var buffer = newStringStream()
    for i, name in enumerate(expectedNames):
      if i == 0:
        buffer.write "`", name, "`"
      elif i + 1 == expectedNames.len:
        buffer.write ", or `", name, "`"
      else:
        buffer.write ", `", name, "`"
    panic self.loc, &"Expected {buffer.data} but got `{symbol}`."
