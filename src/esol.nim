{.experimental: "caseStmtMacros".}

import
  std/logging,
  std/strutils,
  std/sequtils,
  std/options,
  fusion/matching,
  std/streams,
  std/enumerate,
  std/os
    
template panic(args: varargs[string, `$`]) =
  error(args)
  quit(1)

type
  Symbol = object
    name: string
  Step = enum
    Left, Right
  Case = object
    state: Symbol
    read: Symbol
    write: Symbol
    step: Step
    next: Symbol
  Machine = object
    state: Symbol
    tape: seq[Symbol]
    tape_default: Symbol
    head: int
    halt: bool
  # TODO: proper lexer so symbols have a location
  Lexer = seq[string]

method next(self: var Machine, cases: seq[Case]) {.base.} =
  for `case` in cases:
    if `case`.state == self.state and `case`.read == self.tape[self.head]:
      self.tape[self.head] = `case`.write
      case `case`.step:
        of Left:
          if self.head == 0:
            panic "Tape underflow."
          self.head -= 1
        of Right:
          self.head += 1
          if self.head >= self.tape.len:
            self.tape.add(self.tape_default)
      self.state = `case`.next
      self.halt = false
      break
  
method print(self: Machine) {.base.} =
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
  
proc parse_symbol(lexer: var Lexer): Symbol =
  case lexer.next
  of Some(@name): return Symbol(name: name)
  of None(): panic "Expected symbol but reached the end of the input."

proc parse_step(lexer: var Lexer): Step =
  let symbol = parse_symbol(lexer)
  case symbol.name
  of "->": return Right
  of "<-": return Left
  else: panic "Expected arrow but got `", symbol.name, "`."
  
proc parse_case(lexer: var Lexer): Case =
  Case(
    state: parse_symbol(lexer),
    read: parse_symbol(lexer),
    write: parse_symbol(lexer),
    step: parse_step(lexer),
    next: parse_symbol(lexer),
  )

proc parse_symbols(lexer: var Lexer): seq[Symbol] =
  result = new_seq[Symbol]()
  while lexer.peek.is_some:
    result.add(parse_symbol(lexer))

proc parse_cases(lexer: var Lexer): seq[Case] =
  result = new_seq[Case]()
  while lexer.peek.is_some:
    result.add(parse_case(lexer))

proc parse_tape_file(tape_path: string): (seq[Symbol], string) =
  let tape_source = try: read_file(tape_path)
                    except: panic "Could not read file `", tape_path, "`."

  var lexer = tape_source.split.filter_it(it != "")
  return (parse_symbols(lexer), tape_source)

proc parse_cases_file(cases_path: string): (seq[Case], string) =
  let cases_source = try: read_file(cases_path)
                     except: panic "Could not read file `", cases_path, "`."

  var lexer = cases_source.split.filter_it(it != "")
  return (parse_cases(lexer), cases_source)

proc usage(program: string) =
  stderr.write_line "Usage: ", program, " <input.esol> <input.tape>"
    
proc main() =
  var logger = new_console_logger()
  add_handler(logger)

  var args = command_line_params()
  let program = get_app_filename()

  var cases_path: string
  case args.next
  of Some(@path): cases_path = path
  of None():
    usage(program)
    panic "No cases file is provided."

  var tape_path: string
  case args.next
  of Some(@path): tape_path = path
  of None():
    usage(program)
    panic "No tape file is provided."

  let (cases, cases_source) = parse_cases_file(cases_path)
  
  var state: Symbol
  case cases.peek
  of Some(@c): state = c.state
  of None(): panic "Cases file must contain at least one case."
  
  let (tape, tape_source) = parse_tape_file(tape_path)

  var tape_default: Symbol
  case tape.last
  of Some(@symbol): tape_default = symbol
  of None(): panic "Tape file should not be empty, it must contain at least one symbol to be repeated indefinitely."

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
    machine.next(cases)

when isMainModule: main()
