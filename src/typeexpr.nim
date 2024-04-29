import
  ./lexer,
  ./expr,
  ./utils,
  std/sets,
  std/strformat,
  fusion/matching,
  std/options,
  std/tables,
  std/enumerate,
  std/sequtils

type
  TypeExprKind* = enum
    tekNamed
    tekEnclosed
    tekAnonymous
    tekInteger
    tekUnion
    tekDiff
    tekProduct
  TypeExpr* = ref object
    case kind*: TypeExprKind
    of tekNamed:
      name*: Symbol
    of tekEnclosed:
      inner*: TypeExpr
      enclosedLoc*: Loc
    of tekAnonymous:
      anonymousElements*: HashSet[Expr]
      anonymousLoc*: Loc
    of tekInteger:
      symbol*: Symbol
    of tekUnion, tekDiff:
      lhs*: TypeExpr
      rhs*: TypeExpr
    of tekProduct:
      productElements*: seq[TypeExpr]

proc `$`*(self: TypeExpr): string =
  case self.kind
  of tekNamed: return self.name.name
  of tekEnclosed:
    return &"({self.inner})"
  of tekAnonymous:
    var buffer = "{"
    for element in self.anonymousElements:
      buffer &= &" {element}"
    return buffer & " }"
  of tekInteger: return "Integer"
  of tekUnion: return &"{self.lhs} + {self.rhs}"
  of tekDiff: return &"{self.lhs} - {self.rhs}"
  of tekProduct:
    for i, element in enumerate(self.productElements):
      if i > 0: result &= " * "
      else: result &= $element

proc loc*(self: TypeExpr): Loc =
  case self.kind
  of tekNamed: return self.name.loc
  of tekEnclosed: return self.enclosedLoc
  of tekAnonymous: return self.anonymousLoc
  of tekInteger: return self.symbol.loc
  of tekUnion, tekDiff: return self.lhs.loc
  of tekProduct: return self.productElements[0].loc

proc parseTypeExpr*(lexer: var Lexer, types: Table[Symbol, TypeExpr]): TypeExpr

proc parseAnonymous(lexer: var Lexer): HashSet[Expr] =
  discard lexer.expect("{")
  while Some(@symbol) ?= lexer.peek():
    if symbol.name == "}": break
    let value = parseExpr(lexer).eval()
    if Some(@existingValue) ?= result.get(value):
      error value.loc, "Type may only consist of non-repeating values."
      note existingValue.loc, "Same value was provided here."
      quit(1)
    result.incl(value)
  discard lexer.expect("}")

proc parsePrimary(lexer: var Lexer, types: Table[Symbol, TypeExpr]): TypeExpr =
  if None() ?= lexer.peek():
    panic lexer.loc, "Expected symbol but reached the end of the input."
  let symbol = lexer.peek().get
  case symbol.name
  of "{":
    let elements = parseAnonymous(lexer)
    return TypeExpr(
      kind: tekAnonymous,
      anonymousElements: elements,
      anonymousLoc: symbol.loc
    )
  of "(":
    discard lexer.next()
    let inner = parseTypeExpr(lexer, types)
    discard lexer.expect(")")
    return inner
  else:
    discard lexer.next()
    case symbol.toAtom.kind
    of akSymbol:
      case symbol.name
      of "Integer":
        return TypeExpr(kind: tekInteger)
      else:
        if not types.hasKey(symbol):
          panic symbol.loc, &"Unknown type `{symbol}`."
        return TypeExpr(kind: tekNamed, name: symbol)
    of akInteger:
      panic symbol.loc, "Integer is not a type expression."

proc parseProduct*(lexer: var Lexer, types: Table[Symbol, TypeExpr]): TypeExpr =
  var elements = @[parsePrimary(lexer, types)]
  while Some(@symbol) ?= lexer.peek():
    if symbol.name == "*":
      discard lexer.next()
      elements.add(parsePrimary(lexer, types))
    else:
      break
  if elements.len == 1:
    return elements[0]
  elif elements.len > 1:
    return TypeExpr(kind: tekProduct, productElements: elements)
  else:
    unreachable()

proc parseTypeExpr*(lexer: var Lexer, types: Table[Symbol, TypeExpr]): TypeExpr =
  var lhs = parseProduct(lexer, types)
  while Some(@symbol) ?= lexer.peek():
    case symbol.name
    of "+":
      discard lexer.next()
      let rhs = parseProduct(lexer, types)
      lhs = TypeExpr(kind: tekUnion, lhs: lhs, rhs: rhs)
    of "-":
      discard lexer.next()
      let rhs = parseProduct(lexer, types)
      lhs = TypeExpr(kind: tekDiff, lhs: lhs, rhs: rhs)
    else: break
  return lhs

proc expandProductRecursively(expandedElements: seq[HashSet[Expr]], itemLoc: Loc, items: var seq[Expr], result: var HashSet[Expr]) =
  case expandedElements
  of [@head, all @tail]:
    for element in head:
      items.add(element)
      expandProductRecursively(tail, itemLoc, items, result)
      discard items.pop()
  of []:
    result.incl(Expr(kind: ekTuple, items: items, tupleLoc: itemLoc))

proc expand*(self: TypeExpr, types: Table[Symbol, TypeExpr]): HashSet[Expr] =
  case self.kind
  of tekNamed:
    return types[self.name].expand(types)
  of tekEnclosed:
    return self.inner.expand(types)
  of tekAnonymous:
    return self.anonymousElements
  of tekInteger:
    panic self.symbol.loc, &"The type `{self.symbol}` can't be expanded as it is too big."
  of tekUnion:
    return self.lhs.expand(types).union(self.rhs.expand(types))
  of tekDiff:
    return self.lhs.expand(types).difference(self.rhs.expand(types))
  of tekProduct:
    var expandedElements = newSeq[HashSet[Expr]]()
    for element in self.productElements:
      expandedElements.add(element.expand(types))
    var items = newSeq[Expr]()
    expandProductRecursively(expandedElements, self.loc, items, result)
    
proc contains*(self: TypeExpr, element: Expr, types: Table[Symbol, TypeExpr]): bool =
  case self.kind
  of tekNamed:
    if Some(@typeExpr) ?= types.get(self.name):
      return typeExpr.contains(element, types)
    else:
      panic self.name.loc, &"The type `{self.name}` is not defined."
  of tekEnclosed: return self.inner.contains(element, types)
  of tekAnonymous: return self.anonymousElements.contains(element)
  of tekInteger: return element.kind == ekAtom and element.atom.kind == akInteger
  of tekUnion: return self.lhs.contains(element, types) or self.rhs.contains(element, types)
  of tekDiff: return self.lhs.contains(element, types) and not self.rhs.contains(element, types)
  of tekProduct:
    case element.kind
    of ekTuple:
      if element.items.len != self.productElements.len:
        return false
      for (subElement, subType) in element.items.zip(self.productElements):
        if not subType.contains(subElement, types):
          return false
      return true
    else: return false
