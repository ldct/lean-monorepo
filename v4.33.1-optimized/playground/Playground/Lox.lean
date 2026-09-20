import Batteries
import Init
import Std

-- Based on https://github.com/munificent/craftinginterpreters/blob/master/java/com/craftinginterpreters/lox/Scanner.java

inductive TokenType
  | leftParen
  | rightParen
  | leftBrace
  | rightBrace
  | comma
  | dot
  | minus
  | plus
  | semicolon
  | slash
  | star
  | bang
  | bangEqual
  | equal
  | equalEqual
  | greater
  | greaterEqual
  | less
  | lessEqual
  | identifier
  | string
  | number
  | and
  | class
  | else
  | false
  | fun
  | for
  | if
  | nil
  | or
  | print
  | return
  | super
  | this
  | true
  | var
  | while
  | whitespace -- todo delete this
  | EOF
  deriving Repr, Inhabited, BEq

private structure State where
  input : Array Char
  current : Nat := 0
  tokens : Array TokenType := .empty
  error : Option String := .none

private abbrev M := StateM State

private def peek : M Char := do
  let s ← get
  match s.input[s.current]? with
  | some c => return c
  | none => return '\x00'

private def isAtEnd : M Bool := do
  let s ← get
  return s.current ≥ s.input.size

-- todo - is isAtEnd equivalent to peek = '\x00'?

-- Scan tokens with 0 lookahead
def scan0 (c : Char) : Option TokenType := match c with
  | '(' => some .leftParen
  | ')' => some .rightParen
  | '{' => some .leftBrace
  | '}' => some .rightBrace
  | ',' => some .comma
  | '.' => some .dot
  | '-' => some .minus
  | '+' => some .plus
  | ';' => some .semicolon
  | '*' => some .star
  | _ => none

private def advance : M (Option Char) := do
  let s ← get
  let some c := s.input[s.current]? | return none
  set { s with current := s.current + 1 }
  return some c

private def matchChar (expected : Char) : M Bool := do
  if (← isAtEnd) then return false
  if (← peek) ≠ expected then return false
  _ ← advance
  return true

private def emit (kind : TokenType) : M Unit :=
  modify fun s => { s with tokens := s.tokens.push kind }

-- scan with single character lookahead
private def scan1 (c : Char) : M (Option TokenType) := do
  if c == '!' then return some (if (← matchChar '=') then .bangEqual else .bang)
  else if c == '=' then return some (if (← matchChar '=') then .equalEqual else .equal)
  else if c == '>' then return some (if (← matchChar '=') then .greaterEqual else .greater)
  else if c == '<' then return some (if (← matchChar '=') then .lessEqual else .less)
  else
    return none

private def string : M Unit := do
  while (← peek) ≠ '"' && !(← isAtEnd) do
    _ ← advance

  if (← isAtEnd) then
    modify fun s => { s with error := some "Unterminated string" }
    return

  -- the closing "
  _ ← advance

  emit .string

private def scanToken : M Unit := do
  let some c ← advance | return ()

  if let some kind := scan0 c then
    emit kind
    return

  if let some kind := (← scan1 c) then
    emit kind
    return

   if c == '/' then
    if (← matchChar '/') then
      --  A comment goes until the end of the line.
      while (← peek) ≠ '\n' && !(← isAtEnd) do
        _ ← advance
    else
      emit .slash
  else if c == ' ' || c == '\t' || c == '\r' || c == '\n' then
    emit .whitespace
  else
    modify fun s => { s with error := some "oh no" }

private def scanAll : M Unit := do
  while (← peek) ≠ '\x00' do
    scanToken
  emit .EOF

def scanTokens (source : String) : (Array TokenType × Option String) :=
  let (_, s) := scanAll.run {
    input := source.toList.toArray
  }
  (s.tokens, s.error)

def scanTokensOrPanic (source : String) : Array TokenType :=
  let (tokens, error) := scanTokens source
  match error with
  | some error => panic! error
  | none => tokens


#guard scanTokensOrPanic "()+*;" ==
  #[.leftParen, .rightParen, .plus, .star, .semicolon, .EOF]

#eval scanTokens "
// this is a comment
(( )){} // grouping stuff
!*+-/=<> <= == // operators
"

#eval scanTokens "(@"

#eval scanTokens "!+"
