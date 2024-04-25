import esolpkg/[sexpr, lexer]

proc test_file(file_path: string) =
  let source = read_file(file_path)

  var lexer = new_lexer(source)
  let sexpr = parse_sexpr(lexer)

  echo sexpr

test_file "tests/list.sexpr"
