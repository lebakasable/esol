{.experimental: "caseStmtMacros".}

import
  esolpkg/utils,
  esolpkg/sexpr,
  esolpkg/lexer,
  std/logging,
  std/options,
  fusion/matching,
  std/streams,
  std/enumerate,
  std/os,
  std/tables,
  std/strutils,
  std/strformat

type
  StatementKind = enum
    CaseStatement
    ForStatement
  Statement = ref object
    case kind: StatementKind
    of CaseStatement:
      state: Sexpr
      read: Sexpr
      write: Sexpr
      action: Sexpr
      next: Sexpr
    of ForStatement:
      # TODO: support sexpr for `var` and `seq`
      `var`: Symbol
      seq: Symbol
      body: Statement
  Program = object
    statements: seq[Statement]
    seqs: Table[string, seq[Symbol]]
  Machine = object
    state: Sexpr
    tape: seq[Sexpr]
    tape_default: Sexpr
    head: int
    halt: bool

proc substitute(self: Statement, `var`: Symbol, symbol: Symbol): Statement =
  case self.kind
  of CaseStatement:
    result = Statement(
      kind:  CaseStatement,
      state:   self.state.substitute(`var`, symbol),
      read:     self.read.substitute(`var`, symbol),
      write:   self.write.substitute(`var`, symbol),
      action: self.action.substitute(`var`, symbol),
      next:     self.next.substitute(`var`, symbol),
    )
  of ForStatement:
    return Statement(
      kind: ForStatement,
      `var`: self.`var`,
      # TODO: allow substituting the sequences
      seq:   self.seq,
      body:  self.body.substitute(`var`, symbol),
    )

proc entry_state(self: Statement, program: Program): Option[Sexpr] =
  case self.kind
  of CaseStatement: return some(self.state)
  of ForStatement:
    if program.seqs.contains(self.seq.name):
      if Some(@symbol) ?= program.seqs[self.seq.name].first:
        return self.body.substitute(self.`var`, symbol).entry_state(program)
    else:
      panic &"Unknown sequence `{self.seq.name}`."
  
proc match_state(self: Statement, program: Program, state: Sexpr, read: Sexpr): Option[(Sexpr, Sexpr, Sexpr)] =
  case self.kind
  of CaseStatement:
    if self.state == state and self.read == read:
      return some((self.write, self.action, self.next))
  of ForStatement:
    if program.seqs.contains(self.seq.name):
      for symbol in program.seqs[self.seq.name]:
        if Some(@triple) ?= self.body.substitute(self.`var`, symbol).match_state(program, state, read):
          return some(triple)
    else:
      panic &"Unknown sequence `{self.seq.name}`."

proc entry_state(self: Program): Option[Sexpr] =
  for statement in self.statements:
    if Some(@state) ?= statement.entry_state(self):
      return some(state)

proc print(self: Machine) =
  stdout.write self.state, ": "
  for i, sexpr in enumerate(self.tape):
    stdout.write sexpr, " "
  echo()

proc next(self: var Machine, program: Program) =
  for statement in program.statements:
    if Some((@write, @action, @next)) ?= statement.match_state(program, self.state, self.tape[self.head]):
      self.tape[self.head] = write
      if Some(@action) ?= action.atom_name:
        case action.name:
          of "<-":
            if self.head == 0:
              panic "Tape underflow."
            self.head -= 1
          of "->":
            self.head += 1
            if self.head >= self.tape.len:
              self.tape.add(self.tape_default)
          of ".": discard
          of "!": self.print()
          else:
            panic "Action can only be `->`, `<-`, `.` or `!`."
      else:
        panic "Action must be an atom."
      self.state = next
      self.halt = false
      break
 
proc parse_seq(lexer: var Lexer): seq[Symbol] =
  discard lexer.expect_symbol("{")
  while lexer.peek.is_some:
    let symbol = lexer.parse_symbol()
    if symbol.name == "}": break
    result.add(symbol)

proc parse_case(lexer: var Lexer): Statement =
  Statement(
    kind: CaseStatement,
    state:  parse_sexpr(lexer),
    read:   parse_sexpr(lexer),
    write:  parse_sexpr(lexer),
    action: parse_sexpr(lexer),
    next:   parse_sexpr(lexer)  ,
  )
  
proc parse_statement(lexer: var Lexer): Statement =
  let key = lexer.expect_symbol("case", "for")
  case key.name
  of "case": return parse_case(lexer)
  of "for":
    let `var` = lexer.parse_symbol()
    discard lexer.expect_symbol("in")
    let seq = lexer.parse_symbol()
    let body = parse_statement(lexer)
    return Statement(kind: ForStatement, `var`: `var`, seq: seq, body: body)
      
proc parse_program(lexer: var Lexer): Program =
  while Some(@key) ?= lexer.peek:
    case key
    of "case", "for":
      result.statements.add(parse_statement(lexer))
    of "let":
      discard lexer.next
      let name = lexer.parse_symbol()
      if result.seqs.has_key(name.name):
        panic &"Redefinition of sequence `{name.name}`."
      let seq = parse_seq(lexer)
      result.seqs[name.name] = seq
    else:
      panic &"Unknown keyword `{key}`."

proc parse_program_file(program_path: string): (Program, string) =
  let program_source = try: read_file(program_path)
                       except: panic &"Could not read file `{program_path}`."

  var lexer = new_lexer(program_source)
  return (parse_program(lexer), program_source)

proc parse_sexprs(lexer: var Lexer): seq[Sexpr] =
  while lexer.peek.is_some:
    result.add(parse_sexpr(lexer))

proc parse_tape_file(tape_path: string): (seq[Sexpr], string) =
  let tape_source = try: read_file(tape_path)
                    except: panic &"Could not read file `{tape_path}`."

  var lexer = new_lexer(tape_source)
  return (parse_sexprs(lexer), tape_source)

proc usage(app_file: string) =
  stderr.write_line &"Usage: {app_file} <input.esol> <input.tape>"
  
proc main() =
  var logger = new_console_logger()
  add_handler(logger)

  var args = command_line_params()
  let app_file = get_app_filename()

  var program_path: string
  if Some(@path) ?= args.shift:
    program_path = path
  else:
    usage(app_file)
    panic "No program file is provided."

  var tape_path: string
  if Some(@path) ?= args.shift:
    tape_path = path
  else:
    usage(app_file)
    panic "No tape file is provided."

  let (program, _) = parse_program_file(program_path)

  var state: Sexpr
  if Some(@sexpr) ?= program.entry_state: state = sexpr
  else: panic "Source file must contain at least one case."
  
  let (tape, _) = parse_tape_file(tape_path)

  var tape_default: Sexpr
  if Some(@sexpr) ?= tape.last: tape_default = sexpr
  else: panic "Tape file should not be empty, it must contain at least one symbol to be repeated indefinitely."

  var machine = Machine(
    state: state,
    tape: tape,
    tape_default: tape_default,
    head: 0,
    halt: false,
  )

  while not machine.halt:
    machine.halt = true
    machine.next(program)

when isMainModule: main()
