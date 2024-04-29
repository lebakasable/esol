import
  ./utils,
  ./expr,
  ./typeexpr,
  ./lexer,
  std/options,
  fusion/matching,
  std/enumerate,
  std/os,
  std/tables,
  std/strformat,
  std/strutils,
  std/sequtils,
  std/sets

type
  Case = object
    keyword: Symbol
    state: Expr
    read: Expr
    write: Expr
    action: Expr
    next: Expr
  ScopedCase = object
    `case`: Case
    scope: Table[Symbol, TypeExpr]
  StatementKind = enum
    skCase
    skVar
    skBlock
  Statement = ref object
    case kind: StatementKind
    of skCase:
      `case`: Case
    of skVar:
      name: Symbol
      `type`: TypeExpr
      body: Statement
    of skBlock:
      statements: seq[Statement]
  Run = object
    keyword: Symbol
    state: Expr
    tape: seq[Expr]
    trace: bool
  Program = object
    scopedCases: seq[ScopedCase]
    types: Table[Symbol, TypeExpr]
    runs: seq[Run]
  Machine = object
    state: Expr
    tape: seq[Expr]
    tapeDefault: Expr
    head: int
    halt: bool

proc `$`(self: Case): string =
  &"{self.keyword} {self.state} {self.read} {self.write} {self.action} {self.next}"

proc substituteVar(self: Case, name: Symbol, expr: Expr): Case =
  var bindings = {name: expr}.toTable()
  return Case(
    keyword: self.keyword,
    state:   self.state.substituteBindings(bindings),
    read:    self.read.substituteBindings(bindings),
    write:   self.write.substituteBindings(bindings),
    action:  self.action.substituteBindings(bindings),
    next:    self.next.substituteBindings(bindings),
  )

proc normalize(self: Case): Case =
  return Case(
    keyword: self.keyword,
    state:   self.state.normalize(),
    read:    self.read.normalize(),
    write:   self.write.normalize(),
    action:  self.action.normalize(),
    next:    self.next.normalize(),
  )

# TODO: fix expand
proc expand(self: ScopedCase, types: Table[Symbol, TypeExpr],  normalize = false) =
  for name, `type` in self.scope:
    for typeExpr in `type`.expand(types):
      let `case` = self.`case`.substituteVar(name, typeExpr)
      if normalize:
        echo `case`.normalize()
      else:
        echo `case`

proc typeCheckNextCase(self: ScopedCase, types: Table[Symbol, TypeExpr], state: Expr, read: Expr): Option[(Expr, Expr, Expr)] =
  var bindings = initTable[Symbol, Expr]()
  if self.`case`.state.patternMatch(state, bindings, self.scope) and self.`case`.read.patternMatch(read, bindings, self.scope):
    for name, `type` in self.scope:
      let value = bindings[name]
      if not `type`.contains(value, types):
        return
    return some((
      self.`case`.write.substituteBindings(bindings),
      self.`case`.action.substituteBindings(bindings),
      self.`case`.next.substituteBindings(bindings),
    ))

proc `$`(self: Statement): string =
  case self.kind
  of skCase:
    return $self.`case`
  of skVar:
    return &"var {self.name} : {self.`type`} {self.body}"
  of skBlock:
    result = "{\n"
    for statement in self.statements:
      result &= &"  {statement}\n"
    result &= "}"

proc compileToCases(self: Statement, types: Table[Symbol, TypeExpr], scope: var Table[Symbol, TypeExpr], scopedCases: var seq[ScopedCase]) =
  case self.kind
  of skCase:
    var unusedVars = newSeq[Symbol]()
    for name, _ in scope:
      if self.`case`.state.usesVar(name).orElse(self.`case`.read.usesVar(name)).isNone():
        unusedVars.add(name)
    if unusedVars.len > 0:
      error self.`case`.keyword.loc, "Not all variables in the scope are used in the input of this case."
      for `var` in unusedVars:
        note `var`.loc, &"Unused variable `{`var`}`."
      quit(1)
    scopedCases.add(ScopedCase(`case`: self.`case`, scope: scope))
  of skVar:
    if Some(@shadowedVar) ?= scope.getKey(self.name):
      error self.name.loc, &"`{self.name}` shadows another name in the higher scope."
      note shadowedVar.loc, "The shadowed name is located here."
      quit(1)
    scope[self.name] = self.`type`
    self.body.compileToCases(types, scope, scopedCases)
    scope.del(self.name)
  of skBlock:
    for statement in self.statements:
      statement.compileToCases(types, scope, scopedCases)

proc parseStatement(lexer: var Lexer, types: Table[Symbol, TypeExpr]): Statement =
  let key = lexer.expect("case", "var", "{")
  case key.name
  of "case":
    return Statement(kind: skCase, `case`: Case(
      keyword: key,
      state:   parseExpr(lexer),
      read:    parseExpr(lexer),
      write:   parseExpr(lexer),
      action:  parseExpr(lexer),
      next:    parseExpr(lexer),
    ))
  of "var":
    var vars = newSeq[Symbol]()
    while Some(@symbol) ?= lexer.peek():
      if symbol.name == ":": break
      vars.add(lexer.expect())
    discard lexer.expect(":")
    let `type` = parseTypeExpr(lexer, types)
    result = parseStatement(lexer, types)
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
      statements.add(parseStatement(lexer, types))
    discard lexer.expect("}")
    return Statement(
      kind: skBlock,
      statements: statements,
    )
    
proc parseSource(lexer: var Lexer): (seq[Statement], Table[Symbol, TypeExpr], seq[Run]) =
  while Some(@key) ?= lexer.peek():
    case key.name
    of "run", "trace":
      let keyword = lexer.expect("run", "trace")
      let state = parseExpr(lexer)
      discard lexer.expect("{")
      var tape = newSeq[Expr]()
      while Some(@symbol) ?= lexer.peek():
        if symbol.name == "}": break
        tape.add(parseExpr(lexer))
      discard lexer.expect("}")
      result[2].add(Run(
        keyword: keyword,
        state: state,
        tape: tape,
        trace: keyword.name == "trace"
      ))
    of "type":
      discard lexer.next
      let name = lexer.expect()
      if result[1].hasKey(name):
        panic name.loc, &"Redefinition of type `{name}`."
      result[1][name] = parseTypeExpr(lexer, result[1])
    of "case", "var":
      result[0].add(parseStatement(lexer, result[1]))
    else:
      panic key.loc, &"Unknown keyword `{key}`."

proc compileCasesFromStatements(types: Table[Symbol, TypeExpr], statements: seq[Statement]): seq[ScopedCase] =
  for statement in statements:
    var scope = initTable[Symbol, TypeExpr]()
    statement.compileToCases(types, scope, result)

proc expand(self: Run, normalize = false) =
  let keyword = if self.trace: "trace" else: "run"
  var tape = "{ "
  for expr in self.tape:
    if normalize:
      tape &= &"{expr.normalize()} "
    else:
      tape &= &"{expr} "
  tape &= "}"
  echo &"{keyword} {self.state} {tape}"

proc print(self: Machine) =
  for expr in self.tape:
    stdout.write &"{expr} "
  echo()

proc trace(self: Machine) =
  var buffer = &"{self.state}: "
  var head = 0
  var underline = ""
  for i, expr in enumerate(self.tape):
    if i == self.head:
      head = buffer.utf8Len
      underline = '~'.repeat(utf8Len($expr)-1)
    buffer &= &"{expr} "
  echo &"{buffer}\n{' '.repeat(head)}^{underline}"

proc next(self: var Machine, program: var Program) =
  for `case` in program.scopedCases:
    if Some((@write, @action, @next)) ?= `case`.typeCheckNextCase(program.types, self.state, self.tape[self.head]):
      self.tape[self.head] = eval(write)
      if Some(@action) ?= action.asSymbol():
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
      self.state = next.eval()
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
      var (statements, types, runs) = parseSource(lexer)
      var scopedCases = compileCasesFromStatements(types, statements)
      var program = Program(scopedCases: scopedCases, types: types, runs: runs)

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
      var (statements, types, runs) = parseSource(lexer)
      var scopedCases = compileCasesFromStatements(types, statements)

      for `case` in scopedCases:
        `case`.expand(types, noExpr)

      for run in runs:
        run.expand(noExpr)
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
