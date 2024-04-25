{.experimental: "caseStmtMacros".}

import
  esolpkg/utils,
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
      state: Symbol
      read: Symbol
      write: Symbol
      step: Symbol
      next: Symbol
    of ForStatement:
      `var`: Symbol
      seq: Symbol
      body: Statement
  Program = object
    statements: seq[Statement]
    seqs: Table[string, seq[Symbol]]
  Machine = object
    state: Symbol
    tape: seq[Symbol]
    tape_default: Symbol
    head: int
    halt: bool

proc substitute(self: Statement, `var`: Symbol, symbol: Symbol): Statement =
  case self.kind
  of CaseStatement:
    result = Statement(
      kind: CaseStatement,
      state: if self.state == `var`: symbol else: self.state,
      read:  if self.read  == `var`: symbol else: self.read,
      write: if self.write == `var`: symbol else: self.write,
      # TODO: substitute step
      step: self.step,
      next:  if self.next  == `var`: symbol else: self.next,
    )
  of ForStatement:
    return Statement(
      kind: ForStatement,
      `var`: self.`var`,
      seq: if self.seq == `var`: symbol else: self.seq,
      body: self.body.substitute(self.`var`, self.seq),
    )

proc entry_state(self: Statement, program: Program): Option[Symbol] =
  case self.kind
  of CaseStatement: return some(self.state)
  of ForStatement:
    if program.seqs.contains(self.seq.name):
      if Some(@symbol) ?= program.seqs[self.seq.name].first:
        return self.body.substitute(self.`var`, symbol).entry_state(program)
    else:
      panic &"Unknown sequence `{self.seq.name}`."
  
proc match(self: Statement, program: Program, state: Symbol, read: Symbol): Option[(Symbol, Symbol, Symbol)] =
  case self.kind
  of CaseStatement:
    if self.state == state and self.read == read:
      return some((self.write, self.step, self.next))
  of ForStatement:
    if program.seqs.contains(self.seq.name):
      for symbol in program.seqs[self.seq.name]:
        if Some(@triple) ?= self.body.substitute(self.`var`, symbol).match(program, state, read):
          return some(triple)
    else:
      panic &"Unknown sequence `{self.seq.name}`."

proc entry_state(self: Program): Option[Symbol] =
  for statement in self.statements:
    if Some(@state) ?= statement.entry_state(self):
      return some(state)

proc next(self: var Machine, program: Program) =
  for statement in program.statements:
    if Some(@matched) ?= statement.match(program, self.state, self.tape[self.head]):
      let (write, step, next) = matched
      self.tape[self.head] = write
      case step.name:
        of "<-":
          if self.head == 0:
            panic "Tape underflow."
          self.head -= 1
        of "->":
          self.head += 1
          if self.head >= self.tape.len:
            self.tape.add(self.tape_default)
      self.state = next
      self.halt = false
      break

proc print(self: Machine) =
  let buffer = new_string_stream()
  buffer.write self.state.name, ": "
  var head = 0
  for i, symbol in enumerate(self.tape):
    if i == self.head:
      head = buffer.data.len
    buffer.write symbol.name, " "
  echo &"{buffer.data}\n{' '.repeat(head)}^"
  
proc parse_seq(lexer: var Lexer): seq[Symbol] =
  discard lexer.expect_symbol("{")
  while lexer.peek.is_some:
    let symbol = lexer.parse_symbol()
    if symbol.name == "}": break
    result.add(symbol)

proc parse_case(lexer: var Lexer): Statement =
  Statement(
    kind: CaseStatement,
    state: lexer.parse_symbol(),
    read: lexer.parse_symbol(),
    write: lexer.parse_symbol(),
    step: lexer.expect_symbol("->", "<-"),
    next: lexer.parse_symbol()  ,
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

proc parse_symbols(lexer: var Lexer): seq[Symbol] =
  while lexer.peek.is_some:
    result.add(lexer.parse_symbol())

proc parse_tape_file(tape_path: string): (seq[Symbol], string) =
  let tape_source = try: read_file(tape_path)
                    except: panic &"Could not read file `{tape_path}`."

  var lexer = new_lexer(tape_source)
  return (parse_symbols(lexer), tape_source)

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

  var state: Symbol
  if Some(@s) ?= program.entry_state: state = s
  else: panic "Source file must contain at least one case."
  
  let (tape, _) = parse_tape_file(tape_path)

  var tape_default: Symbol
  if Some(@symbol) ?= tape.last: tape_default = symbol
  else: panic "Tape file should not be empty, it must contain at least one symbol to be repeated indefinitely."

  var machine = Machine(
    state: state,
    tape: tape,
    tape_default: tape_default,
    head: 0,
    halt: false,
  )

  while not machine.halt:
    machine.print
    machine.halt = true
    machine.next(program)

when isMainModule: main()
