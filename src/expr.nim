import
  ./lexer,
  fusion/matching,
  std/sequtils,
  std/options,
  std/enumerate,
  std/strformat

type
  ExprKind* = enum
    ekSymbol,
    ekInteger,
    ekTuple
  Expr* = object
    case kind*: ExprKind
    of ekSymbol:
      name*: Symbol
    of ekInteger:
      value*: int
      symbol*: Symbol
    of ekTuple:
      openParen*: Symbol
      items*: seq[Expr]

proc parseExpr*(lexer: var Lexer): Expr =
  let symbol = lexer.expectSymbol()
  case symbol.name
  of "(":
    var items = newSeq[Expr]()
    while Some(@nextSymbol) ?= lexer.peek():
      if nextSymbol.name == ")": break
      items.add(parseExpr(lexer))
    discard lexer.expectSymbol(")")
    return Expr(
      kind: ekTuple,
      openParen: symbol,
      items: items,
    )
  else: return Expr(kind: ekSymbol, name: symbol)

proc `$`*(self: Expr): string =
  case self.kind:
  of ekSymbol:
    return self.name.name
  of ekInteger:
    return self.symbol.name
  of ekTuple:
    var buffer = "("
    for i, item in enumerate(self.items):
      if i == 0:
        buffer &= &"{item}"
      else:
        buffer &= &" {item}"
    return buffer & ")"

proc `==`*(self, other: Expr): bool =
  case (self.kind, other.kind)
  of (ekSymbol, ekSymbol):
    return self.name == other.name
  of (ekTuple, ekTuple):
    if self.items.len != other.items.len: return false
    for (a, b) in self.items.zip(other.items):
      if a != b: return false
    return true
  else: return false

proc symbolName*(self: Expr): Option[Symbol] =
  if self.kind == ekSymbol: return some(self.name)
 
proc substitute*(self: Expr, `var`: Symbol, expr: Expr): Expr =
  case self.kind
  of ekSymbol:
    if self.name == `var`:
      return expr
    else: 
      return self
  of ekInteger:
    if self.symbol == `var`:
      return expr
    else:
      return self
  of ekTuple:
    let items = self.items.mapIt(it.substitute(`var`, expr))
    return Expr(kind: ekTuple, openParen: self.openParen, items: items)

proc loc*(self: Expr): Location =
  case self.kind
  of ekSymbol: return self.name.loc
  of ekInteger: return self.symbol.loc
  of ekTuple: return self.openParen.loc

proc findSymbol*(self: Expr, symbol: Symbol): Option[Symbol] =
  case self.kind
  of ekSymbol:
    if self.name == symbol:
      return some(self.name)
  of ekInteger:
    if self.symbol == symbol:
      return some(self.symbol)
  of ekTuple:
    for item in self.items:
      if Some(@name) ?= item.findSymbol(symbol):
        return some(name)
