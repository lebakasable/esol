import
  ./utils,
  ./list,
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
    skFor
    skBlock
  Statement = ref object
    case kind: StatementKind
    of skCase:
      state: List
      read: List
      write: List
      action: List
      next: List
    of skFor:
      `var`: List
      # TODO: support list for `set`
      set: Symbol
      body: Statement
    of skBlock:
      statements: seq[Statement]
  Run = object
    keyword: Symbol
    state: List
    tape: seq[List]
    trace: bool
  Program = object
    statements: seq[Statement]
    sets: Table[string, seq[List]]
    runs: seq[Run]
  Machine = object
    state: List
    tape: seq[List]
    tapeDefault: List
    head: int
    halt: bool

proc `$`(self: Statement): string =
  case self.kind
  of skCase:
    return &"case {self.state} {self.read} {self.write} {self.action} {self.next}"
  of skFor:
    return &"for {self.`var`} : {self.set} {self.body}"
  of skBlock:
    result = "{\n"
    for statement in self.statements:
      result &= &"  {statement}\n"
    result &= "}"

proc substitute(self: Statement, `var`: Symbol, list: List): Statement =
  case self.kind
  of skCase:
    result = Statement(
      kind:  skCase,
      state:   self.state.substitute(`var`, list),
      read:     self.read.substitute(`var`, list),
      write:   self.write.substitute(`var`, list),
      action: self.action.substitute(`var`, list),
      next:     self.next.substitute(`var`, list),
    )
  of skFor:
    return Statement(
      kind: skFor,
      `var`: self.`var`,
      # TODO: allow substituting the sets
      set:   self.set,
      body:  self.body.substitute(`var`, list),
    )
  of skBlock:
    return Statement(
      kind: skBlock,
      statements: self.statements.mapIt(it.substitute(`var`, list))
    )

proc matchState(self: Statement, program: var Program, state: List, read: List): Option[(List, List, List)] =
  case self.kind
  of skCase:
    if self.state == state and self.read == read:
      return some((self.write, self.action, self.next))
  of skFor:
    if Some(@lists) ?= program.sets.get(self.set.name):
      for list in lists:
        var bindings = initTable[Symbol, List]()
        if self.`var`.patternMatch(list, bindings):
          var subsBody = self.body
          for key, value in bindings:
            subsBody = subsBody.substitute(key, value)
          if Some(@triple) ?= subsBody.matchState(program, state, read):
            return some(triple)
        else:
          error self.`var`.loc, &"`{self.`var`}` does not match `{list}` from set `{self.set}`."
          info list.loc, "The matched value is located here."
    else:
      panic self.set.loc, &"Unknown set `{self.set}`."
  of skBlock:
    for statement in self.statements:
      if Some(@triple) ?= statement.matchState(program, state, read):
        return some(triple)

proc expand(self: Statement, program: var Program) =
  case self.kind
  of skCase: echo self
  of skFor:
    if Some(@lists) ?= program.sets.get(self.set.name):
      for list in lists:
        var bindings = initTable[Symbol, List]()
        if self.`var`.patternMatch(list, bindings):
          var subsBody = self.body
          for key, value in bindings:
            subsBody = subsBody.substitute(key, value)
          subsBody.expand(program)
        else:
          error self.`var`.loc, &"`{self.`var`}` does not match `{list}` from set `{self.set}`."
          info list.loc, "The matched value is located here."
  of skBlock:
    for statement in self.statements:
      echo statement

proc parseSeq(lexer: var Lexer): seq[List] =
  discard lexer.expectSymbol("{")
  while Some(@symbol) ?= lexer.peek():
    if symbol.name == "}": break
    result.add(parseList(lexer))
  discard lexer.expectSymbol("}")

proc parseStatement(lexer: var Lexer): Statement =
  let key = lexer.expectSymbol("case", "for", "{")
  case key.name
  of "case":
    return Statement(
      kind: skCase,
      state:  parseList(lexer),
      read:   parseList(lexer),
      write:  parseList(lexer),
      action: parseList(lexer),
      next:   parseList(lexer),
    )
  of "for":
    var vars = newSeq[List]()
    while Some(@symbol) ?= lexer.peek():
      if symbol.name == ":": break
      vars.add(parseList(lexer))
    discard lexer.expectSymbol(":")
    let set = lexer.expectSymbol()
    result = parseStatement(lexer)
    for i in countdown(vars.len - 1, 0):
      result = Statement(
        kind: skFor,
        `var`: vars[i],
        set: set,
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
        state: parseList(lexer),
        tape: parseSeq(lexer),
        trace: keyword.name == "trace"
      ))
    of "set":
      discard lexer.next
      let name = lexer.expectSymbol()
      if result.sets.hasKey(name.name):
        panic name.loc, &"Redefinition of set `{name}`."
      let seq = parseSeq(lexer)
      result.sets[name.name] = seq
    of "case", "for":
      result.statements.add(parseStatement(lexer))
    else:
      panic key.loc, &"Unknown keyword `{key}`."

proc print(self: Machine) =
  for list in self.tape:
    stdout.write &"{list} "
  echo()

proc trace(self: Machine) =
  var buffer = &"{self.state}: "
  var head = 0
  for i, list in enumerate(self.tape):
    if i == self.head:
      head = buffer.len
    buffer &= &"{list} "
  echo &"{buffer}\n{' '.repeat(head)}^"

proc next(self: var Machine, program: var Program) =
  for statement in program.statements:
    if Some((@write, @action, @next)) ?= statement.matchState(program, self.state, self.tape[self.head]):
      self.tape[self.head] = write
      if Some(@action) ?= action.atomName:
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
  run: proc (appFile: string, args: var seq[string])

var commands = newSeq[Command]()
  
proc usage(appFile: string) =
  stderr.writeLine &"Usage: {appFile} <COMMAND> [ARGS]"
  stderr.writeLine &"COMMANDS:"
  for command in commands:
    stderr.writeLine &"  {command} {command.signature}\t{command.description}"

commands = @[
  Command(
    name: "run",
    description: "Runs an Esol program.",
    signature: "<input.esol>",
    run: proc (appFile: string, args: var seq[string]) =
      var programPath: string
      if Some(@path) ?= args.shift:
        programPath = path
      else:
        usage(appFile)
        panic "No program file is provided."

      let programSource = try: readFile(programPath)
                           except: panic &"Could not read file `{programPath}`."
      var lexer = tokenize(programPath, programSource)
      var program = parseProgram(lexer)

      setControlCHook(nil)

      for i, run in enumerate(program.runs):
        if i > 0: echo "-".repeat(20)
    
        var tapeDefault: List
        if Some(@list) ?= run.tape.last(): tapeDefault = list
        else: panic "Tape should not be empty, it must contain at least one symbol to be repeated indefinitely."

        var machine = Machine(
          state: run.state,
          tape: run.tape,
          tapeDefault: tapeDefault,
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
    run: proc (appFile: string, args: var seq[string]) =
      var programPath: string
      if Some(@path) ?= args.shift:
        programPath = path
      else:
        usage(appFile)
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
        for list in run.tape:
          tape &= &"{list} "
        tape &= "}"
        echo &"{keyword} {run.state} {tape}"
  ),
  Command(
    name: "lex",
    description: "Lexes an Esol program.",
    signature: "<input.esol>",
    run: proc (appFile: string, args: var seq[string]) =
      var programPath: string
      if Some(@path) ?= args.shift:
        programPath = path
      else:
        usage(appFile)
        panic "No program file is provided."

      let programSource = try: readFile(programPath)
                           except: panic &"Could not read file `{programPath}`."
      var lexer = tokenize(programPath, programSource)

      for symbol in lexer.symbols:
        echo &"{symbol.loc}: {symbol.name}"
  )
]
  
proc main() =
  var args = commandLineParams()
  let appFile = getAppFilename()

  var command: string
  if Some(@name) ?= args.shift:
    command = name
  else:
    usage(appFile)
    panic "No command is provided."

  let matchedCommand = commands.filterIt(it.name == command)
  if matchedCommand.len > 0:
    matchedCommand[0].run(appFile, args)
  else:
    panic &"Unknown command `{command}`."

when isMainModule: main()
