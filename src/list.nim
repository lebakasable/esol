import
  ./lexer,
  fusion/matching,
  std/sequtils,
  std/options,
  std/enumerate,
  std/strformat,
  std/tables

type
  ListKind* = enum
    lkSymbol,
    lkList
  List* = object
    case kind*: ListKind
    of lkSymbol:
      name*: Symbol
    of lkList:
      openParen*: Symbol
      items*: seq[List]

proc parseList*(lexer: var Lexer): List =
  let symbol = lexer.expectSymbol()
  case symbol.name
  of "(":
    var items = newSeq[List]()
    while Some(@nextSymbol) ?= lexer.peek():
      if nextSymbol.name == ")": break
      items.add(parseList(lexer))
    discard lexer.expectSymbol(")")
    return List(
      kind: lkList,
      openParen: symbol,
      items: items,
    )
  else: return List(kind: lkSymbol, name: symbol)

proc `$`*(self: List): string =
  case self.kind:
  of lkSymbol:
    return self.name.name
  of lkList:
    var buffer = "("
    for i, item in enumerate(self.items):
      if i == 0:
        buffer &= &"{item}"
      else:
        buffer &= &" {item}"
    return buffer & ")"

proc `==`*(self: List, other: List): bool =
  case (self.kind, other.kind)
  of (lkSymbol, lkSymbol):
    return self.name == other.name
  of (lkList, lkList):
    if self.items.len != other.items.len: return false
    for (a, b) in self.items.zip(other.items):
      if a != b: return false
    return true
  else: return false

proc symbolName*(self: List): Option[Symbol] =
  if self.kind == lkSymbol: return some(self.name)
 
proc substitute*(self: List, `var`: Symbol, list: List): List =
  case self.kind
  of lkSymbol:
    if self.name == `var`:
      return list
    else: 
      return self
  of lkList:
    let items = self.items.mapIt(it.substitute(`var`, list))
    return List(kind: lkList, openParen: self.openParen, items: items)

proc loc*(self: List): Location =
  case self.kind
  of lkSymbol: return self.name.loc
  of lkList: return self.openParen.loc

proc findSymbol*(self: List, symbol: Symbol): Option[Symbol] =
  case self.kind
  of lkSymbol:
    if self.name == symbol:
      return some(self.name)
  of lkList:
    for item in self.items:
      if Some(@name) ?= item.findSymbol(symbol):
        return some(name)
