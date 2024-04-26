import
  ./lexer,
  fusion/matching,
  std/sequtils,
  std/options,
  std/enumerate,
  std/strformat,
  std/tables

type
  SexprKind* = enum
    AtomSexpr,
    ListSexpr
  Sexpr* = object
    case kind*: SexprKind
    of AtomSexpr:
      name*: Symbol
    of ListSexpr:
      open_paren*: Symbol
      items*: seq[Sexpr]

proc parse_sexpr*(lexer: var Lexer): Sexpr =
  let symbol = lexer.parse_symbol()
  case symbol.name
  of "(":
    var items = new_seq[Sexpr]()
    while Some(@next_symbol) ?= lexer.peek():
      if next_symbol.name == ")": break
      items.add(parse_sexpr(lexer))
    discard lexer.expect_symbol(")")
    return Sexpr(
      kind: ListSexpr,
      open_paren: symbol,
      items: items,
    )
  else: return Sexpr(kind: AtomSexpr, name: symbol)

proc `$`*(self: Sexpr): string =
  case self.kind:
  of AtomSexpr:
    return self.name.name
  of ListSexpr:
    var buffer = "("
    for i, item in enumerate(self.items):
      if i == 0:
        buffer &= &"{item}"
      else:
        buffer &= &" {item}"
    return buffer & ")"

proc `==`*(self: Sexpr, other: Sexpr): bool =
  case (self.kind, other.kind)
  of (AtomSexpr, AtomSexpr):
    return self.name == other.name
  of (ListSexpr, ListSexpr):
    if self.items.len != other.items.len: return false
    for (a, b) in self.items.zip(other.items):
      if a != b: return false
    return true
  else: return false

proc atom_name*(self: Sexpr): Option[Symbol] =
  if self.kind == AtomSexpr: return some(self.name)
 
proc substitute*(self: Sexpr, `var`: Symbol, sexpr: Sexpr): Sexpr =
  case self.kind
  of AtomSexpr:
    if self.name == `var`:
      return sexpr
    else: 
      return self
  of ListSexpr:
    let items = self.items.map_it(it.substitute(`var`, sexpr))
    return Sexpr(kind: ListSexpr, open_paren: self.open_paren, items: items)
    
proc pattern_match*(self: Sexpr, value: Sexpr, bindings: var Table[Symbol, Sexpr]): bool =
  result = true
  case (self.kind, value.kind)
  of (AtomSexpr, _):
    bindings[self.name] = value
  of (ListSexpr, ListSexpr):
    if self.items.len == value.items.len:
      for (a, b) in self.items.zip(value.items):
        if not a.pattern_match(b, bindings):
          result = false
    else:
      result = false
  else: result = false

proc loc*(self: Sexpr): Location =
  case self.kind
  of AtomSexpr: return self.name.loc
  of ListSexpr: return self.open_paren.loc
