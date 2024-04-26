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
    sets: Table[string, seq[Sexpr]]
    runs: seq[Run]
  Machine = object
    state: Sexpr
    tape: seq[Sexpr]
    tape_default: Sexpr
    head: int
    halt: bool

proc `$`(self: Statement): string =
  case self.kind
  of CaseStatement:
    return &"case {self.state} {self.read} {self.write} {self.action} {self.next}"
  of ForStatement:
    return &"for {self.`var`} : {self.set} {self.body}"
  of BlockStatement:
    result = "{\n"
    for statement in self.statements:
      result &= &"  {statement}\n"
    result &= "}"

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
    if program.sets.contains(self.set.name):
      for sexpr in program.sets[self.set.name]:
        var bindings = init_table[Symbol, Sexpr]()
        if self.`var`.pattern_match(sexpr, bindings):
          var subs_body = self.body
          for key, value in bindings:
            subs_body = subs_body.substitute(key, value)
          if Some(@triple) ?= subs_body.match_state(program, state, read):
            return some(triple)
        else:
          panic &"`{self.`var`}` does not match `{sexpr}` from set `{self.set}`."
          # note &"The matched value is located here."
    else:
      panic &"Unknown set `{self.set}`."
  of BlockStatement:
    for statement in self.statements:
      if Some(@triple) ?= statement.match_state(program, state, read):
        return some(triple)

proc expand(self: Statement, program: Program) =
  case self.kind
  of CaseStatement: echo self
  of ForStatement:
    if program.sets.contains(self.set.name):
      for sexpr in program.sets[self.set.name]:
        var bindings = init_table[Symbol, Sexpr]()
        if self.`var`.pattern_match(sexpr, bindings):
          var subs_body = self.body
          for key, value in bindings:
            subs_body = subs_body.substitute(key, value)
          subs_body.expand(program)
        else:
          panic &"`{self.`var`}` does not match `{sexpr}` from set `{self.set}`."
  of BlockStatement:
    for statement in self.statements:
      echo statement

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
      if result.sets.has_key(name.name):
        panic &"Redefinition of set `{name}`."
      let seq = parse_seq(lexer)
      result.sets[name.name] = seq
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
  
type Command = object
  name: string
  description: string
  signature: string
  run: proc (app_file: string, args: var seq[string])

var commands = new_seq[Command]()
  
proc usage(app_file: string) =
  stderr.write_line &"Usage: {app_file} <COMMAND> [ARGS]"
  stderr.write_line &"COMMANDS:"
  for command in commands:
    stderr.write_line &"  {command} {command.signature}\t{command.description}"

commands = @[
  Command(
    name: "run",
    description: "Runs an Esol program.",
    signature: "<input.esol>",
    run: proc (app_file: string, args: var seq[string]) =
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

      setControlCHook(nil)

      for i, run in enumerate(program.runs):
        if i > 0: echo "-".repeat(20)
    
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
  ),
  Command(
    name: "expand",
    description: "Expands an Esol program.",
    signature: "<input.esol>",
    run: proc (app_file: string, args: var seq[string]) =
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

      for statement in program.statements:
        statement.expand(program)

      for run in program.runs:
        let keyword = if run.trace: "trace" else: "run"
        var tape = "{ "
        for sexpr in run.tape:
          tape &= &"{sexpr} "
        tape &= "}"
        echo &"{keyword} {run.state} {tape}"
  )
]
  
proc main() =
  var logger = new_console_logger()
  add_handler(logger)

  var args = command_line_params()
  let app_file = get_app_filename()

  var command: string
  if Some(@name) ?= args.shift:
    command = name
  else:
    usage(app_file)
    panic "No command is provided."

  let matched_command = commands.filter_it(it.name == command)
  if matched_command.len > 0:
    matched_command[0].run(app_file, args)
  else:
    panic &"Unknown command `{command}`."

when is_main_module: main()
