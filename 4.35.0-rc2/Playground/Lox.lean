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
  | identifier (s: String)
  | string (s: String)
  | number (n: Rat)
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
  line : Nat
deriving Repr, Inhabited, BEq

private structure State where
  source : Array Char
  start : Nat := 0
  current : Nat := 0
  line : Nat := 1
  tokens : Array Token := .empty
  errors : Array String := .empty

private abbrev M := StateM State

private def isAtEnd : M Bool := do
  let s ← get
  return s.current ≥ s.source.size

private def peek : M Char := do
  let s ← get
  return s.source[s.current]?.getD '\x00'

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
    line := s.line,
  } }

private def peekNext : M Char := do
  let s ← get
  return s.source[s.current + 1]?.getD '\x00'

/-- Parse a decimal lexeme validated by `number`: digits, optionally followed by
    a decimal point and more digits. All arithmetic is exact. -/
private def parseRat (s : String) : Rat :=
  match s.splitOn "." with
  | [whole] => (whole.toNat! : Rat)
  | [whole, fractional] =>
    ((whole ++ fractional).toNat! : Rat) / ((10 ^ fractional.length : Nat) : Rat)
  | _ => panic! "Invalid decimal lexeme"

private def number : M Unit := do
  while (← peek).isDigit do
    advance'

  -- Look for a fractional part.
  if (← peek) == '.' && (← peekNext).isDigit then
    -- Consume the "."
    advance'
    while (← peek).isDigit do advance'

  let s ← get

  let substring := String.ofList (s.source[s.start:s.current].toList)

  addToken (.number (parseRat substring))

private def incrementLine : M Unit := do
  modify fun s => { s with line := s.line + 1 }

private def string : M Unit := do
  while (← peek) ≠ '"' && !(← isAtEnd) do
    if (← peek) == '\n' then incrementLine
    advance'

  if (← isAtEnd) then
    modify fun s => { s with errors := s.errors.push s!"Unterminated string at line {s.line}" }
    return

  -- The closing "
  advance'

  let s ← get
  let lexeme := String.ofList (s.source[s.start:s.current].toList)

  -- Trim the surrounding quotes
  let value := ((lexeme.dropEnd 1).toString.dropPrefix r#"""#).toString

  addToken (.string value)

private def Char.isAlpha' (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def Char.isAlphaNum (c : Char) : Bool :=
  c.isAlpha' || c.isDigit

private def keyword (s : String) : Option TokenType :=
  match s with
  | "and" => some .and
  | "class" => some .class
  | "else" => some .else
  | "false" => some .false
  | "for" => some .for
  | "fun" => some .fun
  | "if" => some .if
  | "nil" => some .nil
  | "or" => some .or
  | "print" => some .print
  | "return" => some .return
  | "super" => some .super
  | "this" => some .this
  | "true" => some .true
  | "var" => some .var
  | "while" => some .while
  | _ => none

private def identifier : M Unit := do
  while (← peek).isAlphaNum do advance'
  let s ← get
  let lexeme := String.ofList (s.source[s.start:s.current].toList)
  if let some type := keyword lexeme then
    addToken type
  else
    addToken (.identifier lexeme)

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

  else if c == ' ' || c == '\t' || c == '\r' then
    pure () -- Ignore whitespace.
  else if c == '\n' then incrementLine
  else if c.isDigit then
    number
  else if c.isAlpha' then
    identifier
  else
    modify fun s => { s with errors := s.errors.push s!"Unexpected character at line {s.line}: {c}" }

private def scanAll : M Unit := do
  while !(← isAtEnd) do
    modify fun s => { s with start := s.current }
    scanToken
  modify fun s => { s with tokens := s.tokens.push {
    type := .EOF,
    line := s.line
  } }

def scanTokens (source : String) : (Array Token × Array String) :=
  let (_, s) := scanAll.run {
    source := source.toList.toArray
  }
  (s.tokens, s.errors)

def scanTokens' (source : String) : Option (Array TokenType) :=
  let (tokens, error) := scanTokens source
  if error.size > 0 then none else some (tokens.map (fun t => t.type))

#eval scanTokens "+"

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
#guard scanTokens "+\x00-" == (#[{ type := TokenType.plus, line := 1 }, { type := TokenType.minus, line := 1 }, { type := TokenType.EOF, line := 1 }],
 #["Unexpected character at line 1: \x00"])

#guard scanTokens' "123 + 123" == .some #[.number 123, .plus, .number 123, .EOF]

#eval scanTokens' "a = 1 b = 3"

#guard scanTokens' "true and false or orchid" == .some #[.true, .and, .false, .or, .identifier "orchid", .EOF]

#eval scanTokens' r#"1 + "hello""#
