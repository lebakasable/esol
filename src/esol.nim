import
  ./utils,
  ./expr,
  ./lexer,
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
    skCase
    skVar
    skBlock
  Statement = ref object
    case kind: StatementKind
    of skCase:
      state: Expr
      read: Expr
      write: Expr
      action: Expr
      next: Expr
    of skVar:
      name: Symbol
      `type`: Symbol
      body: Statement
    of skBlock:
      statements: seq[Statement]
  Run = object
    keyword: Symbol
    state: Expr
    tape: seq[Expr]
    trace: bool
  Program = object
    statements: seq[Statement]
    types: Table[Symbol, seq[Expr]]
    runs: seq[Run]
  Machine = object
    state: Expr
    tape: seq[Expr]
    tapeDefault: Expr
    head: int
    halt: bool

proc `$`(self: Statement): string =
  case self.kind
  of skCase:
    return &"case {self.state} {self.read} {self.write} {self.action} {self.next}"
  of skVar:
    return &"var {self.name} : {self.`type`} {self.body}"
  of skBlock:
    result = "{\n"
    for statement in self.statements:
      result &= &"  {statement}\n"
    result &= "}"

proc substitute(self: Statement, name: Symbol, expr: Expr): Statement =
  case self.kind
  of skCase:
    result = Statement(
      kind:  skCase,
      state:   self.state.substitute(name, expr),
      read:     self.read.substitute(name, expr),
      write:   self.write.substitute(name, expr),
      action: self.action.substitute(name, expr),
      next:     self.next.substitute(name, expr),
    )
  of skVar:
    return Statement(
      kind: skVar,
      name: self.name,
      # TODO: allow substituting the types
      `type`:  self.`type`,
      body:  self.body.substitute(name, expr),
    )
  of skBlock:
    return Statement(
      kind: skBlock,
      statements: self.statements.mapIt(it.substitute(name, expr))
    )

proc matchState(self: Statement, program: var Program, state: Expr, read: Expr): Option[(Expr, Expr, Expr)] =
  case self.kind
  of skCase:
    if self.state == state and self.read == read:
      return some((self.write, self.action, self.next))
  of skVar:
    if Some(@exprs) ?= program.types.get(self.`type`):
      for expr in exprs:
        if Some(@triple) ?= self.body.substitute(self.name, expr).matchState(program, state, read):
          return some(triple)
    else:
      panic self.`type`.loc, &"Unknown type `{self.`type`}`."
  of skBlock:
    for statement in self.statements:
      if Some(@triple) ?= statement.matchState(program, state, read):
        return some(triple)

proc expand(self: Statement, program: var Program) =
  case self.kind
  of skCase: echo self
  of skVar:
    if Some(@exprs) ?= program.types.get(self.`type`):
      for expr in exprs:
        self.body.substitute(self.name, expr).expand(program)
    else:
      panic self.`type`.loc, &"Unknown type `{self.`type`}`."
  of skBlock:
    for statement in self.statements:
      statement.expand(program)

proc parseSeq(lexer: var Lexer): seq[Expr] =
  discard lexer.expectSymbol("{")
  while Some(@symbol) ?= lexer.peek():
    if symbol.name == "}": break
    result.add(parseExpr(lexer))
  discard lexer.expectSymbol("}")

proc parseStatement(lexer: var Lexer): Statement =
  let key = lexer.expectSymbol("case", "var", "{")
  case key.name
  of "case":
    return Statement(
      kind: skCase,
      state:  parseExpr(lexer),
      read:   parseExpr(lexer),
      write:  parseExpr(lexer),
      action: parseExpr(lexer),
      next:   parseExpr(lexer),
    )
  of "var":
    var vars = newSeq[Symbol]()
    while Some(@symbol) ?= lexer.peek():
      if symbol.name == ":": break
      vars.add(lexer.expectSymbol())
    discard lexer.expectSymbol(":")
    let `type` = lexer.expectSymbol()
    result = parseStatement(lexer)
    for i in countdown(vars.len - 1, 0):
      result = Statement(
        kind: skVar,
        name: vars[i],
        `type`: `type`,
        body: result)
  of "{":
    var statements = newSeq[Statement]()
    while Some(@symbol) ?= lexer.peek():
      if symbol.name == "}": break
      statements.add(parseStatement(lexer))
    discard lexer.expectSymbol("}")
    return Statement(
      kind: skBlock,
      statements: statements,
    )

proc parseProgram(lexer: var Lexer): Program =
  while Some(@key) ?= lexer.peek():
    case key.name
    of "run", "trace":
      let keyword = lexer.expectSymbol("run", "trace")
      result.runs.add(Run(
        keyword: keyword,
        state: parseExpr(lexer),
        tape: parseSeq(lexer),
        trace: keyword.name == "trace"
      ))
    of "type":
      discard lexer.next
      let name = lexer.expectSymbol()
      if result.types.hasKey(name):
        panic name.loc, &"Redefinition of type `{name}`."
      let seq = parseSeq(lexer)
      result.types[name] = seq
    of "case", "var":
      result.statements.add(parseStatement(lexer))
    else:
      panic key.loc, &"Unknown keyword `{key}`."

proc print(self: Machine) =
  for expr in self.tape:
    stdout.write &"{expr} "
  echo()

proc trace(self: Machine) =
  var buffer = &"{self.state}: "
  var head = 0
  var lastExpr = Expr()
  var underline = ""
  for i, expr in enumerate(self.tape):
    if i == self.head:
      head = buffer.len
      underline = '~'.repeat(len($expr)-1)
    buffer &= &"{expr} "
  echo &"{buffer}\n{' '.repeat(head)}^{underline}"

proc next(self: var Machine, program: var Program) =
  for statement in program.statements:
    if Some((@write, @action, @next)) ?= statement.matchState(program, self.state, self.tape[self.head]):
      if write.kind == ekEval:
        if write.lhs.kind == ekInteger:
          if write.rhs.kind == ekInteger:
            self.tape[self.head] = Expr(
              kind: ekInteger,
              symbol: write.openBracket,
              value: write.lhs.value + write.rhs.value,
            )
          else:
            panic write.rhs.loc, "Right hand side value must be an integer."
        else:
          panic write.lhs.loc, "Left hand side value must be an integer."
      else:
        self.tape[self.head] = write
      if Some(@action) ?= action.symbolName():
        case action.name:
          of "<-":
            if self.head == 0:
              panic action.loc, "Tape underflow."
            self.head -= 1
          of "->":
            self.head += 1
            if self.head >= self.tape.len:
              self.tape.add(self.tapeDefault)
          of ".": discard
          of "!": self.print()
          else:
            panic action.loc, "Action can only be `->`, `<-`, `.` or `!`."
      else:
        panic action.loc, "Action must be a symbol."
      self.state = next
      self.halt = false
      break
  
type Command = object
  name: string
  description: string
  signature: string
  run: proc (args: var seq[string])

var appFile = "esol"
var commands = newSeq[Command]()
  
proc usage(file = stdout) =
  file.writeLine &"Usage: {appFile} <COMMAND> [ARGS]"
  file.writeLine &"COMMANDS:"
  for command in commands:
    file.writeLine &"  {command.name} {command.signature}\t{command.description}"

commands = @[
  Command(
    name: "run",
    description: "Runs an Esol program.",
    signature: "<input.esol>",
    run: proc (args: var seq[string]) =
      var programPath: string
      if Some(@path) ?= args.shift:
        programPath = path
      else:
        usage(stderr)
        panic "No program file is provided."

      let programSource = try: readFile(programPath)
                           except: panic &"Could not read file `{programPath}`."
      var lexer = tokenize(programPath, programSource)
      var program = parseProgram(lexer)

      setControlCHook(nil)

      for i, run in enumerate(program.runs):
        echo &"{run.keyword.loc}: run"
    
        var tapeDefault: Expr
        if Some(@expr) ?= run.tape.last(): tapeDefault = expr
        else: panic "Tape should not be empty, it must contain at least one symbol to be repeated indefinitely."

        var machine = Machine(
          state: run.state,
          tape: run.tape,
          tapeDefault: tapeDefault,
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
    run: proc (args: var seq[string]) =
      var programPath: string
      if Some(@path) ?= args.shift:
        programPath = path
      else:
        usage(stderr)
        panic "No program file is provided."

      let programSource = try: readFile(programPath)
                           except: panic &"Could not read file `{programPath}`."
      var lexer = tokenize(programPath, programSource)
      var program = parseProgram(lexer)

      for statement in program.statements:
        statement.expand(program)

      for run in program.runs:
        let keyword = if run.trace: "trace" else: "run"
        var tape = "{ "
        for expr in run.tape:
          tape &= &"{expr} "
        tape &= "}"
        echo &"{keyword} {run.state} {tape}"
  ),
  Command(
    name: "lex",
    description: "Lexes an Esol program.",
    signature: "<input.esol>",
    run: proc (args: var seq[string]) =
      var programPath: string
      if Some(@path) ?= args.shift:
        programPath = path
      else:
        usage(stderr)
        panic "No program file is provided."

      let programSource = try: readFile(programPath)
                           except: panic &"Could not read file `{programPath}`."
      var lexer = tokenize(programPath, programSource)

      for symbol in lexer.symbols:
        echo &"{symbol.loc}: {symbol.name}"
  ),
  Command(
    name: "help",
    description: "Prints this help message.",
    signature: "         ",
    run: proc (args: var seq[string]) =
      usage()
  )
]
  
proc main() =
  var args = commandLineParams()
  appFile = getAppFilename()

  var command: string
  if Some(@name) ?= args.shift:
    command = name
  else:
    usage(stderr)
    panic "No command is provided."

  let matchedCommand = commands.filterIt(it.name == command)
  if matchedCommand.len > 0:
    matchedCommand[0].run(args)
  else:
    panic &"Unknown command `{command}`."

when isMainModule: main()
