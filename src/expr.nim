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
  std/hashes,
  std/sets

type
  AtomKind* = enum
    akSymbol
    akInteger
  Atom* = object
    symbol*: Symbol
    case kind*: AtomKind
    of akSymbol: discard
    of akInteger:
      value*: int
  ExprKind* = enum
    ekAtom
    ekTuple
    ekEval
  Expr* = ref object
    case kind*: ExprKind
    of ekAtom:
      atom*: Atom
    of ekTuple:
      openParen*: Symbol
      items*: seq[Expr]
    of ekEval:
      openBracket*: Symbol
      lhs*: Expr
      op*: Expr
      rhs*: Expr
  TypeExprKind* = enum
    tekNamed
    tekAnonymous
    tekInteger
    tekUnion
    tekDiff
  TypeExpr* = ref object
    case kind*: TypeExprKind
    of tekNamed:
      name*: Symbol
    of tekAnonymous:
      elements*: HashSet[Expr]
    of tekInteger:
      symbol*: Symbol
    of tekUnion, tekDiff:
      lhs*: TypeExpr
      rhs*: TypeExpr
      
proc asVar*(self: Atom, scope: Table[Symbol, TypeExpr]): Option[TypeExpr] =
  if self.kind == akSymbol:
    return scope.get(self.symbol)

proc fromSymbol*(symbol: Symbol): Atom =
  try:
    return Atom(kind: akInteger, symbol: symbol, value: symbol.name.parseInt)
  except:
    return Atom(kind: akSymbol, symbol: symbol)

proc asSymbol*(self: Expr): Option[Symbol] =
  if self.kind == ekAtom:
    return some(self.atom.symbol)

proc toExpr*(symbol: Symbol): Expr =
  return Expr(kind: ekAtom, atom: Atom(kind: akSymbol, symbol: symbol))

proc toExpr*(symbol: Symbol, integer: int): Expr =
  return Expr(kind: ekAtom, atom: Atom(kind: akInteger, symbol: symbol, value: integer))

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
      openParen: symbol,
      items: items,
    )
  of "[":
    let lhs = lexer.expect().toExpr()
    let op = lexer.expect().toExpr()
    let rhs = lexer.expect().toExpr()
    discard lexer.expect("]")
    return Expr(
      kind: ekEval,
      openBracket: symbol,
      lhs: lhs,
      op: op,
      rhs: rhs,
    )
  else: 
    try:
      return toExpr(symbol, symbol.name.parseInt())
    except:
      return toExpr(symbol)

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
    return self.atom.symbol == other.atom.symbol
  of (ekTuple, ekTuple):
    if self.items.len != other.items.len: return false
    for (a, b) in self.items.zip(other.items):
      if a != b: return false
    return true
  of (ekEval, ekEval):
    return self.lhs == other.lhs and self.rhs == other.rhs
  else: return false

proc hash*(self: Expr): Hash = hash($self)
 
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
    return Expr(kind: ekTuple, openParen: self.openParen, items: items)
  of ekEval:
    return Expr(
      kind: ekEval,
      openBracket: self.openBracket,
      lhs: self.lhs.substituteBindings(bindings),
      op: self.op.substituteBindings(bindings),
      rhs: self.rhs.substituteBindings(bindings),
    )

proc loc*(self: Expr): Location =
  case self.kind
  of ekAtom: return self.atom.symbol.loc
  of ekTuple: return self.openParen.loc
  of ekEval: return self.openBracket.loc

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
      symbol: Symbol(name: buffer, loc: self.openParen.loc),
    ))
  of ekEval:
    panic "Normalizing `eval` expressions has not been implemented yet."

proc `$`*(self: TypeExpr): string =
  case self.kind
  of tekNamed: return self.name.name
  of tekAnonymous:
    var buffer = "{"
    for element in self.elements:
      buffer &= &" {element}"
    return buffer & " }"
  of tekInteger: return "Integer"
  of tekUnion: return &"{self.lhs} + {self.rhs}"
  of tekDiff: return &"{self.lhs} - {self.rhs}"

proc parseTypeExpr*(lexer: var Lexer): TypeExpr =
  let symbol = lexer.expect()
  var lhs: TypeExpr
  case symbol.name
  of "{":
    var elements = newSeq[Expr]()
    while Some(@symbol) ?= lexer.peek():
      if symbol.name == "}": break
      elements.add(parseExpr(lexer))
    discard lexer.expect("}")
    lhs = TypeExpr(kind: tekAnonymous, elements: elements.toHashSet())
  else:
    let atom = fromSymbol(symbol)
    case atom.kind
    of akSymbol:
      case atom.symbol.name
      of "Integer":
        lhs = TypeExpr(kind: tekInteger, symbol: atom.symbol)
      else:
        lhs = TypeExpr(kind: tekNamed, name: atom.symbol)
    of akInteger:
      panic atom.symbol.loc, "Integer is not a type expression."
  if Some(@symbol) ?= lexer.peek():
    case symbol.name
    of "+":
      discard lexer.next()
      return TypeExpr(kind: tekUnion, lhs: lhs, rhs: parseTypeExpr(lexer))
    of "-":
      discard lexer.next()
      return TypeExpr(kind: tekDiff, lhs: lhs, rhs: parseTypeExpr(lexer))
    else: return lhs
  else:
      return lhs

proc eval*(self: Expr): Expr =
  let op = self.op.atom.symbol
  case op.name
  of "+":
    return Expr(kind: ekAtom, atom: Atom(
      kind: akInteger,
      symbol: self.openBracket,
      value: self.lhs.atom.value + self.rhs.atom.value,
    ))
  of "%":
    return Expr(kind: ekAtom, atom: Atom(
      kind: akInteger,
      symbol: self.openBracket,
      value: self.lhs.atom.value %% self.rhs.atom.value,
    ))
  else:
    panic op.loc, &"Unknown operation `{op}`."
