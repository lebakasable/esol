{.experimental: "caseStmtMacros".}

import
  std/logging,
  std/strutils,
  std/sequtils,
  std/options,
  fusion/matching,
  std/streams,
  std/enumerate,
  std/os,
  std/tables
    
template panic(args: varargs[string, `$`]) =
  error(args)
  quit(1)
  
proc peek[T](s: seq[T]): Option[T] =
  if s.len > 0:
    result = some(s[0])

proc last[T](s: seq[T]): Option[T] =
  if s.len > 0:
    result = some(s[s.len-1])

proc next[T](s: var seq[T]): Option[T] =
  if s.len > 0:
    result = some(s[0])
    s = s[1..s.len-1]

type
  Symbol = object
    name: string
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
  # TODO: proper lexer so symbols have a location
  Lexer = seq[string]
  
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
      if Some(@symbol) ?= program.seqs[self.seq.name].peek:
        return self.body.substitute(self.`var`, symbol).entry_state(program)
    else:
      panic "Unknown sequence `", self.seq.name, "`."
  
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
      panic "Unknown sequence `", self.seq.name, "`."

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
  echo buffer.data
  for _ in 0..<head:
    stdout.write " "
  echo "^"
  
proc parse_symbol(lexer: var Lexer): Symbol =
  if Some(@name) ?= lexer.next:
    return Symbol(name: name)
  else:
    panic "Expected symbol but reached the end of the input."

proc expect_symbol(lexer: var Lexer, expected_names: varargs[string]): Symbol =
  let symbol = parse_symbol(lexer)
  for name in expected_names:
    if symbol.name == name:
      return symbol
  var buffer = new_string_stream()
  for i, name in enumerate(expected_names):
    if i == 0:
      buffer.write "`", name, "`"
    elif i + 1 == expected_names.len:
      buffer.write ", or `", name, "`"
    else:
      buffer.write ", `", name, "`"
  panic "Expected ", buffer.data, " but got `", symbol.name, "`."

proc parse_seq(lexer: var Lexer): seq[Symbol] =
  discard expect_symbol(lexer, "{")
  while lexer.peek.is_some:
    let symbol = parse_symbol(lexer)
    if symbol.name == "}": break
    result.add(symbol)

proc parse_case(lexer: var Lexer): Statement =
  Statement(
    kind: CaseStatement,
    state: parse_symbol(lexer),
    read: parse_symbol(lexer),
    write: parse_symbol(lexer),
    step: expect_symbol(lexer, "->", "<-"),
    next: parse_symbol(lexer)  ,
  )
  
proc parse_statement(lexer: var Lexer): Statement =
  let key = expect_symbol(lexer, "case", "for")
  case key.name
  of "case": return parse_case(lexer)
  of "for":
    let `var` = parse_symbol(lexer)
    discard expect_symbol(lexer, "in")
    let seq = parse_symbol(lexer)
    let body = parse_statement(lexer)
    return Statement(kind: ForStatement, `var`: `var`, seq: seq, body: body)
    
proc parse_program(lexer: var Lexer): Program =
  while Some(@key) ?= lexer.peek:
    case key
    of "case", "for":
      result.statements.add(parse_statement(lexer))
    of "let":
      discard lexer.next
      let name = parse_symbol(lexer)
      if result.seqs.has_key(name.name):
        panic "Redefinition of sequence `", name.name, "`."
      let seq = parse_seq(lexer)
      result.seqs[name.name] = seq
    else:
      panic "Unknown keyword `", key, "`."

proc parse_program_file(program_path: string): (Program, string) =
  let program_source = try: read_file(program_path)
                       except: panic "Could not read file `", program_path, "`."

  var lexer = program_source.split.filter_it(it != "")
  return (parse_program(lexer), program_source)

proc parse_symbols(lexer: var Lexer): seq[Symbol] =
  while lexer.peek.is_some:
    result.add(parse_symbol(lexer))

proc parse_tape_file(tape_path: string): (seq[Symbol], string) =
  let tape_source = try: read_file(tape_path)
                    except: panic "Could not read file `", tape_path, "`."

  var lexer = tape_source.split.filter_it(it != "")
  return (parse_symbols(lexer), tape_source)

proc usage(app_file: string) =
  stderr.write_line "Usage: ", app_file, " <input.esol> <input.tape>"
  
proc main() =
  var logger = new_console_logger()
  add_handler(logger)

  var args = command_line_params()
  let app_file = get_app_filename()

  var program_path: string
  if Some(@path) ?= args.next:
    program_path = path
  else:
    usage(app_file)
    panic "No program file is provided."

  var tape_path: string
  if Some(@path) ?= args.next:
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
