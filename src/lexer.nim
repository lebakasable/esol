import
  ./utils,
  std/strutils,
  std/options,
  std/enumerate,
  fusion/matching,
  std/streams,
  std/strformat,
  std/hashes

const SPECIAL = (['(', '{', '[',      '.'],
                 [')', '}', ']', ':', '.'])
  
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
    var line = line
    if not line.startsWith("//"):
      while line.len > 0 and line[0].isSpaceAscii():
        discard line.shift()
        loc.col += 1

      let words = line.split()
      for word in words:
        var word = word
        if word.len > 0:
          loc.col += lastWordLen
    
          while word.len > 1 and word[0] in SPECIAL[0]:
            result.symbols.add(Symbol(name: $word[0], loc: loc))
            discard word.shift()
            loc.col += 1

          var toAdd = newSeq[Symbol]()
          var lastLoc = loc
          while word.len > 1 and word[word.len-1] in SPECIAL[1]:
            toAdd.add(Symbol(name: $word[word.len-1], loc: Location(filePath: filePath, row: loc.row, col: lastLoc.col+word.len-1)))
            word = $word[0..word.len-2]
            loc.col += 1

          result.symbols.add(Symbol(name: word, loc: lastLoc))
          lastWordLen = word.len + 1

          if toAdd.len > 0:
            for i in countdown(toAdd.len-1, 0):
              result.symbols.add(toAdd[i])
        else:
          loc.col += 1
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

proc expect*(self: var Lexer, expectedNames: varargs[string]): Symbol =
  if expectedNames.len == 0:
    if Some(@symbol) ?= self.next:
      return symbol
    else:
      panic self.loc, "Expected symbol but reached the end of the input."
  else:
    let symbol = self.expect()
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
