import
  esolpkg/utils,
  esolpkg/sexpr,
  esolpkg/lexer,
  std/logging,
  std/options,
  fusion/matching,
  std/enumerate,
  std/os,
  std/tables,
  std/strformat,
  std/strutils,
  std/sequtils

type
  StatementKind = enum
    CaseStatement
    ForStatement
    BlockStatement
  Statement = ref object
    case kind: StatementKind
    of CaseStatement:
      state: Sexpr
      read: Sexpr
      write: Sexpr
      action: Sexpr
      next: Sexpr
    of ForStatement:
      `var`: Sexpr
      # TODO: support sexpr for `set`
      set: Symbol
      body: Statement
    of BlockStatement:
      statements: seq[Statement]
  Run = object
    keyword: Symbol
    state: Sexpr
    tape: seq[Sexpr]
    trace: bool
  Program = object
    statements: seq[Statement]
    seqs: Table[string, seq[Sexpr]]
    runs: seq[Run]
  Machine = object
    state: Sexpr
    tape: seq[Sexpr]
    tape_default: Sexpr
    head: int
    halt: bool

proc substitute(self: Statement, `var`: Symbol, sexpr: Sexpr): Statement =
  case self.kind
  of CaseStatement:
    result = Statement(
      kind:  CaseStatement,
      state:   self.state.substitute(`var`, sexpr),
      read:     self.read.substitute(`var`, sexpr),
      write:   self.write.substitute(`var`, sexpr),
      action: self.action.substitute(`var`, sexpr),
      next:     self.next.substitute(`var`, sexpr),
    )
  of ForStatement:
    return Statement(
      kind: ForStatement,
      `var`: self.`var`,
      # TODO: allow substituting the sets
      set:   self.set,
      body:  self.body.substitute(`var`, sexpr),
    )
  of BlockStatement:
    return Statement(
      kind: BlockStatement,
      statements: self.statements.map_it(it.substitute(`var`, sexpr))
    )

proc match_state(self: Statement, program: Program, state: Sexpr, read: Sexpr): Option[(Sexpr, Sexpr, Sexpr)] =
  case self.kind
  of CaseStatement:
    if self.state == state and self.read == read:
      return some((self.write, self.action, self.next))
  of ForStatement:
    if program.seqs.contains(self.set.name):
      for sexpr in program.seqs[self.set.name]:
        var bindings = init_table[Symbol, Sexpr]()
        if self.`var`.pattern_match(sexpr, bindings):
          var subs_body = self.body
          for key, value in bindings:
            subs_body = subs_body.substitute(key, value)
          if Some(@triple) ?= subs_body.match_state(program, state, read):
            return some(triple)
        else:
          panic &"`{self.`var`}` does not match `{sexpr}` from set `{self.set.name}`."
          # note &"The matched value is located here."
    else:
      panic &"Unknown set `{self.set.name}`."
  of BlockStatement:
    for statement in self.statements:
      if Some(@triple) ?= statement.match_state(program, state, read):
        return some(triple)

proc parse_seq(lexer: var Lexer): seq[Sexpr] =
  discard lexer.expect_symbol("{")
  while Some(@symbol) ?= lexer.peek_symbol:
    if symbol.name == "}": break
    result.add(parse_sexpr(lexer))
  discard lexer.expect_symbol("}")

proc parse_statement(lexer: var Lexer): Statement =
  let key = lexer.expect_symbol("case", "for", "{")
  case key.name
  of "case":
    return Statement(
      kind: CaseStatement,
      state:  parse_sexpr(lexer),
      read:   parse_sexpr(lexer),
      write:  parse_sexpr(lexer),
      action: parse_sexpr(lexer),
      next:   parse_sexpr(lexer),
    )
  of "for":
    var vars = new_seq[Sexpr]()
    while Some(@symbol) ?= lexer.peek_symbol:
      if symbol.name == ":": break
      vars.add(parse_sexpr(lexer))
    discard lexer.expect_symbol(":")
    let set = lexer.parse_symbol()
    result = parse_statement(lexer)
    for i in countdown(vars.len - 1, 0):
      result = Statement(
        kind: ForStatement,
        `var`: vars[i],
        set: set,
        body: result)
  of "{":
    var statements = new_seq[Statement]()
    while Some(@symbol) ?= lexer.peek_symbol:
      if symbol.name == "}": break
      statements.add(parse_statement(lexer))
    discard lexer.expect_symbol("}")
    return Statement(
      kind: BlockStatement,
      statements: statements,
    )

proc parse_program(lexer: var Lexer): Program =
  while Some(@key) ?= lexer.peek:
    case key
    of "run", "trace":
      let keyword = lexer.expect_symbol("run", "trace")
      result.runs.add(Run(
        keyword: keyword,
        state: parse_sexpr(lexer),
        tape: parse_seq(lexer),
        trace: keyword.name == "trace"
      ))
    of "set":
      discard lexer.next
      let name = lexer.parse_symbol()
      if result.seqs.has_key(name.name):
        panic &"Redefinition of set `{name.name}`."
      let seq = parse_seq(lexer)
      result.seqs[name.name] = seq
    of "case", "for":
      result.statements.add(parse_statement(lexer))
    else:
      panic &"Unknown keyword `{key}`."

proc print(self: Machine) =
  for sexpr in self.tape:
    stdout.write &"{sexpr} "
  echo()

proc trace(self: Machine) =
  var buffer = &"{self.state}: "
  var head = 0
  for i, sexpr in enumerate(self.tape):
    if i == self.head:
      head = buffer.len
    buffer &= &"{sexpr} "
  echo &"{buffer}\n{' '.repeat(head)}^"

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

proc usage(app_file: string) =
  stderr.write_line &"Usage: {app_file} <input.esol>"
  
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

  let program_source = try: read_file(program_path)
                       except: panic &"Could not read file `{program_path}`."
  var lexer = new_lexer(program_source)
  let program = parse_program(lexer)

  for i, run in enumerate(program.runs):
    echo "-".repeat(20)
    
    var tape_default: Sexpr
    if Some(@sexpr) ?= run.tape.last: tape_default = sexpr
    else: panic "Tape file should not be empty, it must contain at least one symbol to be repeated indefinitely."

    var machine = Machine(
      state: run.state,
      tape: run.tape,
      tape_default: tape_default,
      head: 0,
      halt: false,
    )

    while not machine.halt:
      if run.trace: machine.trace()
      machine.halt = true
      machine.next(program)

when is_main_module: main()
