import
  ./lexer,
  ./utils,
  fusion/matching,
  std/sequtils,
  std/options,
  std/enumerate,
  std/strformat,
  std/strutils,
  std/tables,
  std/hashes

type
  AtomKind* = enum
    akSymbol
    akInteger
  Atom* = object
    case kind*: AtomKind
    of akSymbol:
      symbol*: Symbol
    of akInteger:
      value*: int
      loc*: Loc
  ExprKind* = enum
    ekAtom
    ekTuple
    ekEval
  Expr* = ref object
    case kind*: ExprKind
    of ekAtom:
      atom*: Atom
    of ekTuple:
      items*: seq[Expr]
      tupleLoc*: Loc
    of ekEval:
      lhs*: Expr
      op*: Expr
      rhs*: Expr
      evalLoc*: Loc
 
proc `$`*(self: Expr): string =
  case self.kind:
  of ekAtom:
    case self.atom.kind
    of akSymbol: return self.atom.symbol.name
    of akInteger: return $self.atom.value
  of ekTuple:
    var buffer = "("
    for i, item in enumerate(self.items):
      if i == 0:
        buffer &= &"{item}"
      else:
        buffer &= &" {item}"
    return buffer & ")"
  of ekEval:
    return &"[{self.lhs} {self.op} {self.rhs}]"

proc `==`*(self, other: Expr): bool =
  case (self.kind, other.kind)
  of (ekAtom, ekAtom):
    case (self.atom.kind, other.atom.kind)
    of (akSymbol, akSymbol):
      return self.atom.symbol == other.atom.symbol
    of (akInteger, akInteger):
      return self.atom.value == other.atom.value
    else: return false
  of (ekTuple, ekTuple):
    if self.items.len != other.items.len: return false
    for (a, b) in self.items.zip(other.items):
      if a != b: return false
    return true
  of (ekEval, ekEval):
    return self.lhs == other.lhs and self.rhs == other.rhs
  else: return false

proc hash*(self: Expr): Hash = hash($self)

proc loc*(self: Expr): Loc =
  case self.kind
  of ekAtom: return self.atom.symbol.loc
  of ekTuple: return self.tupleLoc
  of ekEval: return self.evalLoc

proc toExpr*(symbol: Symbol): Expr =
  return Expr(kind: ekAtom, atom: Atom(kind: akSymbol, symbol: symbol))

proc toExpr*(integer: int, loc: Loc): Expr =
  return Expr(kind: ekAtom, atom: Atom(kind: akInteger, value: integer, loc: loc))

proc parseExpr*(lexer: var Lexer): Expr =
  let symbol = lexer.expect()
  case symbol.name
  of "(":
    var items = newSeq[Expr]()
    while Some(@nextSymbol) ?= lexer.peek():
      if nextSymbol.name == ")": break
      items.add(parseExpr(lexer))
    discard lexer.expect(")")
    return Expr(
      kind: ekTuple,
      items: items,
      tupleLoc: symbol.loc,
    )
  of "[":
    let lhs = lexer.parseExpr()
    let op = lexer.parseExpr()
    let rhs = lexer.parseExpr()
    discard lexer.expect("]")
    return Expr(
      kind: ekEval,
      lhs: lhs,
      op: op,
      rhs: rhs,
      evalLoc: symbol.loc,
    )
  else: 
    try:
      return toExpr(symbol.name.parseInt(), symbol.loc)
    except:
      return toExpr(symbol)

proc toAtom*(symbol: Symbol): Atom =
  try:
    return Atom(kind: akInteger, value: symbol.name.parseInt, loc: symbol.loc)
  except:
    return Atom(kind: akSymbol, symbol: symbol)

proc expectAtom*(self: Expr): Atom =
  case self.kind
  of ekAtom: return self.atom
  of ekTuple: panic self.tupleLoc, &"Expected atom but got tuple `{self}`."
  of ekEval: panic self.evalLoc, &"Expected atom but got eval expression `{self}`."

proc expectSymbol*(self: Atom): Symbol =
  case self.kind
  of akSymbol: return self.symbol
  of akInteger: panic self.loc, &"Expected symbol but got integer `{self.value}`."

proc expectInteger*(self: Atom): int =
  case self.kind
  of akInteger: return self.value
  of akSymbol: panic self.symbol.loc, &"Expected integer but got symbol `{self.symbol}`."

proc expectBool*(self: Symbol): bool =
  case self.name
  of "true": return true
  of "false": return false
  else:
    panic self.loc, &"Expected boolean but got symbol `{self.name}`."

template intOp(op: untyped): Expr =
  Expr(kind: ekAtom, atom: Atom(
    kind: akInteger,
    value: `op`(lhs, rhs),
    loc: self.loc,
  ))
  
template boolOp(op: untyped): Expr =
  Expr(kind: ekAtom, atom: Atom(kind: akSymbol, symbol: Symbol(
    name: if `op`(lhs, rhs): "true" else: "false",
    loc: self.loc
  )))

proc eval*(self: Expr): Expr =
  case self.kind
  of ekAtom: return self
  of ekTuple:
    result = self
    result.items = result.items.mapIt(it.eval())
  of ekEval:
    let op = self.op.eval.expectAtom.expectSymbol
    let lhs = self.lhs.eval.expectAtom
    case lhs.kind
    of akInteger:
      let lhs = lhs.expectInteger
      let rhs = self.rhs.eval.expectAtom.expectInteger
      case op.name
      of "+": return intOp(`+`)
      of "-": return intOp(`-`)
      of "*": return intOp(`*`)
      of "%": return intOp(`%%`)
      of "<": return boolOp(`<`)
      of "<=": return boolOp(`<=`)
      of ">": return boolOp(`>`)
      of ">=": return boolOp(`>=`)
      of "==": return boolOp(`==`)
      of "!=": return boolOp(`!=`)
      else:
        panic op.loc, &"Unknown integer operation `{op}`."
    of akSymbol:
      let lhs = lhs.symbol.expectBool
      let rhs = self.rhs.eval.expectAtom.expectSymbol.expectBool
      case op.name
      of "||": return boolOp(`or`)
      of "&&": return boolOp(`and`)
      else:
        panic op.loc, &"Unknown boolean operation `{op}`."

import ./typeexpr

proc asVar*(self: Atom, scope: Table[Symbol, TypeExpr]): Option[TypeExpr] =
  if self.kind == akSymbol:
    return scope.get(self.symbol)

proc exprFromSymbol*(symbol: Symbol): Expr =
  return Expr(kind: ekAtom, atom: symbol.toAtom())

proc asSymbol*(self: Expr): Option[Symbol] =
  if self.kind == ekAtom:
    return some(self.atom.symbol)
 
proc substituteBindings*(self: Expr, bindings: Table[Symbol, Expr]): Expr =
  case self.kind
  of ekAtom:
    case self.atom.kind
    of akSymbol:
      if Some(@expr) ?= bindings.get(self.atom.symbol):
        return expr
      else: 
        return self
    of akInteger:
      return self
  of ekTuple:
    let items = self.items.mapIt(it.substituteBindings(bindings))
    return Expr(kind: ekTuple, items: items, tupleLoc: self.tupleLoc)
  of ekEval:
    return Expr(
      kind: ekEval,
      lhs: self.lhs.substituteBindings(bindings),
      op: self.op.substituteBindings(bindings),
      rhs: self.rhs.substituteBindings(bindings),
      evalLoc: self.evalLoc,
    )

proc patternMatch*(self: Expr, value: Expr, bindings: var Table[Symbol, Expr], scope: Table[Symbol, TypeExpr]): bool =
  case self.kind
  of ekAtom:
    case self.atom.kind
    of akSymbol:
      if scope.hasKey(self.atom.symbol):
        bindings[self.atom.symbol] = value
        return true
      else:
        return self == value
    of akInteger: return self == value
  of ekTuple:
    case value.kind
    of ekTuple:
      if self.items.len != value.items.len: return false
      for (a, b) in self.items.zip(value.items):
        if not a.patternMatch(b, bindings, scope):
          return false
      return true
    of ekAtom, ekEval: return false
  of ekEval:
    case value.kind
    of ekEval:
      if not self.lhs.patternMatch(value.lhs, bindings, scope):
        return false
      if not self.rhs.patternMatch(value.rhs, bindings, scope):
        return false
      return true
    of ekAtom, ekTuple: return false

proc usesVar*(self: Expr, name: Symbol): Option[Symbol] =
  case self.kind
  of ekAtom:
    case self.atom.kind
    of akSymbol:
      if self.atom.symbol == name:
        return some(self.atom.symbol)
    of akInteger: return
  of ekTuple:
    for item in self.items:
      if Some(@symbol) ?= item.usesVar(name):
        return some(symbol)
  of ekEval:
    return self.lhs.usesVar(name).orElse(self.rhs.usesVar(name))

proc normalize*(self: Expr): Expr =
  case self.kind
  of ekAtom: return self
  of ekTuple:
    var buffer = "_"
    for i, item in enumerate(self.items):
      if i > 0: buffer &= "_"
      buffer &= $item.normalize()
    buffer &= "_"
    return Expr(kind: ekAtom, atom: Atom(
      kind: akSymbol,
      symbol: Symbol(name: buffer, loc: self.tupleLoc),
    ))
  of ekEval:
    panic "Normalizing `eval` expressions has not been implemented yet."

