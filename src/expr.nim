import
  ./lexer,
  fusion/matching,
  std/sequtils,
  std/options,
  std/enumerate,
  std/strformat,
  std/strutils

type
  ExprKind* = enum
    ekSymbol,
    ekInteger,
    ekTuple,
    ekEval
  Expr* = ref object
    case kind*: ExprKind
    of ekSymbol:
      name*: Symbol
    of ekInteger:
      value*: int
      symbol*: Symbol
    of ekTuple:
      openParen*: Symbol
      items*: seq[Expr]
    of ekEval:
      openBracket*: Symbol
      lhs*: Expr
      rhs*: Expr

proc toExpr*(symbol: Symbol): Expr =
  return Expr(kind: ekSymbol, name: symbol)

proc toExpr*(symbol: Symbol, integer: int): Expr =
  return Expr(kind: ekInteger, symbol: symbol, value: integer)

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
  of "[":
    let lhs = lexer.expectSymbol().toExpr()
    discard lexer.expectSymbol("+")
    let rhs = lexer.expectSymbol().toExpr()
    discard lexer.expectSymbol("]")
    return Expr(
      kind: ekEval,
      openBracket: symbol,
      lhs: lhs,
      rhs: rhs,
    )
  else: 
    try:
      return toExpr(symbol, symbol.name.parseInt())
    except:
      return toExpr(symbol)

proc `$`*(self: Expr): string =
  case self.kind:
  of ekSymbol:
    return self.name.name
  of ekInteger:
    return $self.value
  of ekTuple:
    var buffer = "("
    for i, item in enumerate(self.items):
      if i == 0:
        buffer &= &"{item}"
      else:
        buffer &= &" {item}"
    return buffer & ")"
  of ekEval:
    return &"[{self.lhs} + {self.rhs}]"

proc `==`*(self, other: Expr): bool =
  case (self.kind, other.kind)
  of (ekSymbol, ekSymbol):
    return self.name == other.name
  of (ekInteger, ekInteger):
    return self.value == other.value
  of (ekTuple, ekTuple):
    if self.items.len != other.items.len: return false
    for (a, b) in self.items.zip(other.items):
      if a != b: return false
    return true
  of (ekEval, ekEval):
    return self.lhs == other.lhs and self.rhs == other.rhs
  else: return false

proc symbolName*(self: Expr): Option[Symbol] =
  if self.kind == ekSymbol: return some(self.name)
  if self.kind == ekInteger: return some(self.symbol)
 
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
  of ekEval:
    return Expr(
      kind: ekEval,
      openBracket: self.openBracket,
      lhs: self.lhs.substitute(`var`, expr),
      rhs: self.rhs.substitute(`var`, expr),
    )

proc loc*(self: Expr): Location =
  case self.kind
  of ekSymbol: return self.name.loc
  of ekInteger: return self.symbol.loc
  of ekTuple: return self.openParen.loc
  of ekEval: return self.openBracket.loc
