import
  ./lexer,
  ./expr,
  ./utils,
  std/sets,
  std/strformat,
  fusion/matching,
  std/options,
  std/tables,
  std/enumerate

type
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
    let atom = atomFromSymbol(symbol)
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
    # TODO: operator precedence
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

proc expand*(self: TypeExpr, types: Table[Symbol, TypeExpr]): HashSet[Expr] =
  case self.kind
  of tekNamed:
    return types[self.name].expand(types)
  of tekAnonymous:
    return self.elements
  of tekInteger:
    panic self.symbol.loc, &"The type `{self.symbol}` can't be expanded as it is too big."
  of tekUnion:
    return self.lhs.expand(types).union(self.rhs.expand(types))
  of tekDiff:
    return self.lhs.expand(types).difference(self.rhs.expand(types))
    
proc contains*(self: TypeExpr, element: Expr, types: Table[Symbol, TypeExpr]): bool =
  case self.kind
  of tekNamed:
    if Some(@typeExpr) ?= types.get(self.name):
      return typeExpr.contains(element, types)
    else:
      panic self.name.loc, &"The type `{self.name}` is not defined."
  of tekAnonymous: return self.elements.contains(element)
  of tekInteger: return element.kind == ekAtom and element.atom.kind == akInteger
  of tekUnion: return self.lhs.contains(element, types) or self.rhs.contains(element, types)
  of tekDiff: return self.lhs.contains(element, types) and not self.rhs.contains(element, types)
