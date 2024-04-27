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
      keyword: Symbol
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
    return &"{self.keyword} {self.state} {self.read} {self.write} {self.action} {self.next}"
  of skVar:
    return &"var {self.name} : {self.`type`} {self.body}"
  of skBlock:
    result = "{\n"
    for statement in self.statements:
      result &= &"  {statement}\n"
    result &= "}"

proc substituteVar(self: Statement, name: Symbol, expr: Expr): Statement =
  case self.kind
  of skCase:
    var bindings = {name: expr}.toTable()
    result = Statement(
      kind:  skCase,
      keyword: self.keyword,
      state:   self.state.substituteBindings(bindings),
      read:     self.read.substituteBindings(bindings),
      write:   self.write.substituteBindings(bindings),
      action: self.action.substituteBindings(bindings),
      next:     self.next.substituteBindings(bindings),
    )
  of skVar:
    return Statement(
      kind: skVar,
      name: self.name,
      # TODO: allow substituting the types
      `type`:  self.`type`,
      body:  self.body.substituteVar(name, expr),
    )
  of skBlock:
    return Statement(
      kind: skBlock,
      statements: self.statements.mapIt(it.substituteVar(name, expr))
    )

proc typeContainsValue(program: Program, `type`: Symbol, value: Expr): bool =
  if Some(@typeValues) ?= program.types.get(`type`):
    return typeValues.contains(value)
  else:
    case `type`.name
    of "Integer":
      if value.kind == ekInteger: return true
      else: return false
    else:
      panic `type`.loc, "Unknown type `{`type`}`."

proc typeCheckCase(self: Statement, program: var Program, state: Expr, read: Expr, scope: var Table[Symbol, Symbol]): Option[(Expr, Expr, Expr)] =
  case self.kind
  of skCase:
    var bindings = initTable[Symbol, Expr]()

    if not self.state.patternMatch(state, bindings, some(scope)):
      return
    if not self.read.patternMatch(read, bindings, some(scope)):
      return

    for name, `type` in scope:
      let value = bindings[name]
      if not typeContainsValue(program, `type`, value):
        return
    return some((
      self.write.substituteBindings(bindings),
      self.action.substituteBindings(bindings),
      self.next.substituteBindings(bindings),
    ))
  of skVar:
    if Some(@shadowedVar) ?= scope.getKey(self.name):
      error self.name.loc, &"`{self.name}` shadows another name in the higher scope."
      note shadowedVar.loc, "The shadowed name is located here."
      quit(1)
    scope[self.name] = self.`type`
    result = self.body.typeCheckCase(program, state, read, scope)
    scope.del(self.name)
  of skBlock:
    for statement in self.statements:
      if Some(@triple) ?= statement.typeCheckCase(program, state, read, scope):
        return some(triple)

proc sanityCheck(self: Statement, program: Program, scope: var Table[Symbol, Symbol]) =
  case self.kind
  of skCase:
    var unusedVars = newSeq[Symbol]()
    for name, `type` in scope:
      if not (program.types.hasKey(`type`) or `type`.name in ["Integer"]):
        panic `type`.loc, &"Unknown type `{`type`}`."
      if self.state.usesVar(name).orElse(self.read.usesVar(name)).isNone():
        unusedVars.add(name)
    if unusedVars.len > 0:
      error self.keyword.loc, "Not all variables in the scope are used in the input of this case."
      for `var` in unusedVars:
        note `var`.loc, &"Unused variable `{`var`}`."
      quit(1)
  of skVar:
    if Some(@shadowedVar) ?= scope.getKey(self.name):
      error self.name.loc, &"`{self.name}` shadows another name in the higher scope."
      note shadowedVar.loc, "The shadowed name is located here."
      quit(1)
    scope[self.name] = self.`type`
    self.body.sanityCheck(program, scope)
    scope.del(self.name)
  of skBlock:
    for statement in self.statements:
      statement.sanityCheck(program, scope)

proc normalize(self: Statement): Statement =
  case self.kind
  of skCase:
    return Statement(
      kind:    skCase,
      keyword: self.keyword,
      state:   self.state.normalize(),
      read:     self.read.normalize(),
      write:   self.write.normalize(),
      action: self.action.normalize(),
      next:     self.next.normalize(),
    )
  of skVar:
    return Statement(
      kind: skVar,
      `type`: self.`type`,
      body: self.body.normalize(),
    )
  of skBlock:
    return Statement(
      kind: skBlock,
      statements: self.statements.map_it(it.normalize())
    )

proc expand(self: Statement, program: var Program, normalize = false) =
  case self.kind
  of skCase:
    if normalize:
      echo self.normalize()
    else:
      echo self
  of skVar:
    if Some(@exprs) ?= program.types.get(self.`type`):
      for expr in exprs:
        self.body.substituteVar(self.name, expr).expand(program, normalize)
    else:
      case self.`type`.name:
      of "Integer":
        panic self.`type`.loc, &"This type can't be expanded as it is too big."
      else:
        panic self.`type`.loc, &"Unknown type `{self.`type`}`."
  of skBlock:
    for statement in self.statements:
      statement.expand(program, normalize)

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
      keyword: key,
      state:   parseExpr(lexer),
      read:    parseExpr(lexer),
      write:   parseExpr(lexer),
      action:  parseExpr(lexer),
      next:    parseExpr(lexer),
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

proc parseSource(lexer: var Lexer): Program =
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

proc expand(self: Run) =
  let keyword = if self.trace: "trace" else: "run"
  var tape = "{ "
  for expr in self.tape:
    tape &= &"{expr} "
  tape &= "}"
  echo &"{keyword} {self.state} {tape}"

proc sanityCheck(self: Program) =
  for statement in self.statements:
    var scope = initTable[Symbol, Symbol]()
    statement.sanityCheck(self, scope)

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
    var scope = initTable[Symbol, Symbol]()
    if Some((@write, @action, @next)) ?= statement.typeCheckCase(program, self.state, self.tape[self.head], scope):
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
    description: "Runs an Esol file.",
    signature: "<input.esol>",
    run: proc (args: var seq[string]) =
      var sourcePath: string
      if Some(@path) ?= args.shift:
        sourcePath = path
      else:
        usage(stderr)
        panic "No input file is provided."

      let source = try: readFile(sourcePath)
                   except: panic &"Could not read file `{sourcePath}`."
      var lexer = tokenize(sourcePath, source)
      var program = parseSource(lexer)

      program.sanityCheck()

      setControlCHook(nil)
      for run in program.runs:
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
    description: "Expands an Esol file.",
    signature: "[--no-expr] <input.esol>",
    run: proc (args: var seq[string]) =
      var sourcePath = none(string)
      var noExpr = false

      while Some(@arg) ?= args.shift:
        case arg
        of "--no-expr": noExpr = true
        else:
          if sourcePath.isSome():
            usage(stderr)
            panic "Interpreting several files is not supported."
          else:
            sourcePath = some(arg)

      if Some(_) ?= sourcePath: discard else:
        usage(stderr)
        panic "No input file is provided."

      let source = try: readFile(sourcePath.get)
                   except: panic &"Could not read file `{sourcePath.get}`."
      var lexer = tokenize(sourcePath.get, source)
      var program = parseSource(lexer)

      program.sanityCheck()
      
      for statement in program.statements:
        statement.expand(program, noExpr)

      for run in program.runs:
        run.expand()
  ),
  Command(
    name: "lex",
    description: "Lexes an Esol file.",
    signature: "<input.esol>",
    run: proc (args: var seq[string]) =
      var sourcePath: string
      if Some(@path) ?= args.shift:
        sourcePath = path
      else:
        usage(stderr)
        panic "No input file is provided."

      let source = try: readFile(sourcePath)
                   except: panic &"Could not read file `{sourcePath}`."
      var lexer = tokenize(sourcePath, source)

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
