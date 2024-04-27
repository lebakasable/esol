import
  ./lexer,
  ./utils,
  fusion/matching,
  std/sequtils,
  std/options,
  std/enumerate,
  std/strformat,
  std/strutils,
  std/tables

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
 
proc substituteBindings*(self: Expr, bindings: Table[Symbol, Expr]): Expr =
  case self.kind
  of ekSymbol:
    if Some(@expr) ?= bindings.get(self.name):
      return expr
    else: 
      return self
  of ekInteger:
    return self
  of ekTuple:
    let items = self.items.mapIt(it.substituteBindings(bindings))
    return Expr(kind: ekTuple, openParen: self.openParen, items: items)
  of ekEval:
    return Expr(
      kind: ekEval,
      openBracket: self.openBracket,
      lhs: self.lhs.substituteBindings(bindings),
      rhs: self.rhs.substituteBindings(bindings),
    )

proc loc*(self: Expr): Location =
  case self.kind
  of ekSymbol: return self.name.loc
  of ekInteger: return self.symbol.loc
  of ekTuple: return self.openParen.loc
  of ekEval: return self.openBracket.loc

proc patternMatch*(self: Expr, value: Expr, bindings: var Table[Symbol, Expr], scope: Option[Table[Symbol, Symbol]] = none(Table[Symbol, Symbol])): bool =
  case self.kind
  of ekSymbol:
    if Some(@scope) ?= scope:
      if scope.hasKey(self.name):
        bindings[self.name] = value
        return true
      else:
        case value.kind
        of ekSymbol: return self.name == value.name
        of ekInteger, ekTuple, ekEval: return false
    else:
      bindings[self.name] = value
      return true
  of ekInteger:
    if Some(@scope) ?= scope:
      if scope.hasKey(self.symbol):
        bindings[self.symbol] = value
        return true
      else:
        case value.kind
        of ekInteger: return self.symbol == value.symbol
        of ekSymbol, ekTuple, ekEval: return false
    else:
      bindings[self.symbol] = value
      return true
  of ekTuple:
    case value.kind
    of ekTuple:
      if self.items.len != value.items.len: return false
      for (a, b) in self.items.zip(value.items):
        if not a.patternMatch(b, bindings, scope):
          return false
      return true
    of ekSymbol, ekInteger, ekEval: return false
  of ekEval:
    case value.kind
    of ekEval:
      if not self.lhs.patternMatch(value.lhs, bindings, scope):
        return false
      if not self.rhs.patternMatch(value.rhs, bindings, scope):
        return false
      return true
    of ekSymbol, ekInteger, ekTuple: return false

proc usesVar*(self: Expr, name: Symbol): Option[Symbol] =
  case self.kind
  of ekSymbol:
    if self.name == name:
      return some(self.name)
  of ekInteger: return
  of ekTuple:
    for item in self.items:
      if Some(@symbol) ?= item.usesVar(name):
        return some(symbol)
  of ekEval:
    return self.lhs.usesVar(name).orElse(self.rhs.usesVar(name))
