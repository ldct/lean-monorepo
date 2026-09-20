module

import Batteries
import Init
import Std

public section

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
  | EOF
  deriving Repr, Inhabited, BEq

structure Token where
  type : TokenType
  lexeme : String
  line : Nat
deriving Repr, Inhabited, BEq

private structure State where
  source : Array Char
  start : Nat := 0
  current : Nat := 0
  tokens : Array Token := .empty
  error : Option String := .none

private abbrev M := StateM State

private def isAtEnd : M Bool := do
  let s ← get
  return s.current ≥ s.source.size


private def peek : M Char := do
  let s ← get
  return s.source[s.current]?.getD '\x00'

-- todo - is isAtEnd equivalent to peek = '\x00'?

-- -- Scan tokens with 0 lookahead
-- def scan0 (c : Char) : Option TokenType := match c with
--   | '(' => some .leftParen
--   | ')' => some .rightParen
--   | '{' => some .leftBrace
--   | '}' => some .rightBrace
--   | ',' => some .comma
--   | '.' => some .dot
--   | '-' => some .minus
--   | '+' => some .plus
--   | ';' => some .semicolon
--   | '*' => some .star
--   | _ => none

private def incrementCurrent : M Unit := do
  modify fun s => { s with current := s.current + 1 }

private def advance : M (Option Char) := do
  let s ← get
  let some c := s.source[s.current]? | return none
  incrementCurrent
  return some c

private def advance' : M Unit := do
  _ ← advance

private def matchChar (expected : Char) : M Bool := do
  if (← isAtEnd) then return false
  if (← peek) ≠ expected then return false
  incrementCurrent
  return true

private def emit (token : Token) : M Unit :=
  modify fun s => { s with tokens := s.tokens.push token }

private def addToken (type : TokenType) : M Unit := do
  modify fun s => { s with tokens := s.tokens.push {
    type := type,
    lexeme := String.ofList (s.source[s.start:s.current].toList),
    line := 0 -- todo - add line number
  } }

private def peekNext : M Char := do
  let s ← get
  return s.source[s.current + 1]?.getD '\x00'


private def number : M Unit := do
  while (← peek).isDigit do
    advance'

  -- Look for a fractional part.
  if (← peek) == '.' && (← peekNext).isDigit then
    -- Consume the "."
    advance'
    while (← peek).isDigit do advance'

  addToken .number

private def string : M Unit := do
  while (← peek) ≠ '"' && !(← isAtEnd) do
    -- line++
    advance'

  if (← isAtEnd) then
    modify fun s => { s with error := some "Unterminated string" }
    return

  -- The closing "
  advance'

  addToken .string

private def scanToken : M Unit := do
  let some c ← advance | return ()

  if c == '(' then addToken .leftParen
  else if c == ')' then addToken .rightParen
  else if c == '{' then addToken .leftBrace
  else if c == '}' then addToken .rightBrace
  else if c == ',' then addToken .comma
  else if c == '.' then addToken .dot
  else if c == '-' then addToken .minus
  else if c == '+' then addToken .plus
  else if c == ';' then addToken .semicolon
  else if c == '*' then addToken .star

  else if c == '!' then addToken (if (← matchChar '=') then .bangEqual else .bang)
  else if c == '=' then addToken (if (← matchChar '=') then .equalEqual else .equal)
  else if c == '>' then addToken (if (← matchChar '=') then .greaterEqual else .greater)
  else if c == '<' then addToken (if (← matchChar '=') then .lessEqual else .less)

  else if c == '/' then
    if (← matchChar '/') then
      --  A comment goes until the end of the line.
      while (← peek) ≠ '\n' && !(← isAtEnd) do advance'
    else
      addToken .slash

  else if c == '"' then string

  else if c == ' ' || c == '\t' || c == '\r' || c == '\n' then
    modify fun s => s
  else if c.isDigit then
    number
  else
    modify fun s => { s with error := some "oh no" }

private def scanAll : M Unit := do
  while !(← isAtEnd) do
    modify fun s => { s with start := s.current }
    scanToken
  addToken .EOF

def scanTokens (source : String) : (Array Token × Option String) :=
  let (_, s) := scanAll.run {
    source := source.toList.toArray
  }
  (s.tokens, s.error)

def scanTokens' (source : String) : Option (Array TokenType) :=
  let (tokens, error) := scanTokens source
  match error with
  | some _ => none
  | none => some (tokens.map (fun t => t.type))

#guard scanTokens' "()+*;" == .some #[.leftParen, .rightParen, .plus, .star, .semicolon, .EOF]

#eval scanTokens' "
// this is a comment
(( )){} // grouping stuff
!*+-/=<> <= == // operators
"

#eval scanTokens' "(@"

#eval scanTokens' "!+"

-- Failed lookahead preserves the next character.
#guard scanTokens' "!+" == .some #[.bang, .plus, .EOF]

#guard scanTokens' "/+" == .some #[.slash, .plus, .EOF]

-- Comments can end at EOF.
#guard scanTokens' "//" == .some #[.EOF]

-- NUL produces an error, without truncating the remaining source.
#guard scanTokens' "+\x00-" == .none

#eval scanTokens' "123 + 123"
