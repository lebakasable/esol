import
  lexer,
  fusion/matching

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
    while Some(@next_symbol) ?= lexer.peek_symbol():
      if next_symbol.name == ")": break
      items.add(parse_sexpr(lexer))
    discard lexer.expect_symbol(")")
    return Sexpr(
      kind: ListSexpr,
      open_paren: symbol,
      items: items,
    )
  else: return Sexpr(kind: AtomSexpr, name: symbol)
