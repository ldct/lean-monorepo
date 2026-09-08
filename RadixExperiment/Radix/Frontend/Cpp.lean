import Radix.AST
import Lean

/-! A deliberately closed C++ frontend. The parser and native runtime correspondence
are trusted boundaries; parsing itself is a computable checked function. No C++
preprocessing, implicit conversions, uninitialized locals, or external calls are
accepted. Block-local names become distinct flat-frame identifiers. -/
namespace Radix.Cpp

inductive Token where
  | word : String → Token
  | text : String → Token
  deriving Repr, BEq, Inhabited

def identifierStart (c : Char) : Bool := c.isAlpha && c.toNat < 128 || c == '_'
def identifierRest (c : Char) : Bool := identifierStart c || c.isDigit

private def quoted : Nat → List Char → String → Except String (String × List Char)
  | 0, _, _ => .error "unterminated string"
  | _+1, [], _ => .error "unterminated string"
  | _+1, '"' :: cs, s => .ok (s, cs)
  | n+1, '\\' :: c :: cs, s =>
    match c with
    | 'n' => quoted n cs (s.push '\n')
    | 'r' => quoted n cs (s.push '\r')
    | 't' => quoted n cs (s.push '\t')
    | '\\' => quoted n cs (s.push '\\')
    | '"' => quoted n cs (s.push '"')
    | _ => .error "unsupported string escape"
  | n+1, c :: cs, s =>
    if c.toNat < 32 || c.toNat > 126 then .error "literal must contain printable ASCII or escapes"
    else quoted n cs (s.push c)

private def tokenizeAux : Nat → List Char → Except String (List Token)
  | 0, [] => .ok []
  | 0, _ => .error "tokenizer limit"
  | _+1, [] => .ok []
  | n+1, c :: cs => do
    if c == ' ' || c == '\n' || c == '\r' || c == '\t' then tokenizeAux n cs
    else if c == '"' then
      let (s, rest) ← quoted (cs.length+1) cs ""
      return .text s :: (← tokenizeAux n rest)
    else if identifierRest c then
      let tail := cs.takeWhile identifierRest
      return .word (String.ofList (c :: tail)) :: (← tokenizeAux n (cs.drop tail.length))
    else
      let two := String.ofList (c :: cs.take 1)
      if two == "++" || two == "--" then throw "increment and decrement are unsupported"
      if ["&&", "||", "==", "!=", "<=", ">="].contains two then
        return .word two :: (← tokenizeAux n (cs.drop 1))
      else if "{}()[];=+-*/%<>!".toList.contains c then
        return .word (String.singleton c) :: (← tokenizeAux n cs)
      else throw s!"unsupported character {c}"

def tokenize (source : String) : Except String (List Token) :=
  tokenizeAux (source.length+1) source.toList

structure Binding where
  source : String
  localId : String
  ty : Ty
  initialized : Bool := true
  deriving Inhabited
structure ParseState where
  tokens : List Token
  scopes : List (List Binding) := [[]]
  nextId : Nat := 0
  deriving Inhabited
abbrev Parser := StateT ParseState (Except String)
private def fail (s : String) : Parser α := throw s
private def peek : Parser (Option Token) := return (← get).tokens.head?
private def take : Parser Token := do
  let s ← get
  match s.tokens with
  | [] => fail "unexpected end of source"
  | t :: ts => set {s with tokens := ts}; return t
private def expect (s : String) : Parser Unit := do
  if (← take) != .word s then fail s!"expected {s}"
private def eat (s : String) : Parser Bool := do
  if (← peek) == some (.word s) then let _ ← take; return true
  else return false
private def reserved : List String :=
  ["EOF", "NULL", "EXIT_FAILURE", "EXIT_SUCCESS", "BUFSIZ", "FOPEN_MAX", "FILENAME_MAX",
   "L_tmpnam", "TMP_MAX", "SEEK_SET", "SEEK_CUR", "SEEK_END", "RAND_MAX", "MB_CUR_MAX",
   "stdin", "stdout", "stderr", "linux", "unix", "errno", "i386", "mips", "sparc", "sun", "radix_space", "solve", "main", "u64", "bool", "void", "int", "new", "delete", "free", "if", "else", "while",
   "alignas", "alignof", "and", "and_eq", "asm", "auto", "bitand", "bitor", "break", "case", "catch", "char", "char8_t", "char16_t", "char32_t", "class", "compl", "concept", "const", "consteval", "constexpr", "constinit", "const_cast", "continue", "co_await", "co_return", "co_yield", "decltype", "default", "do", "double", "dynamic_cast", "enum", "explicit", "export", "extern", "float", "for", "friend", "goto", "inline", "long", "mutable", "namespace", "noexcept", "not", "not_eq", "nullptr", "operator", "or", "or_eq", "private", "protected", "public", "register", "reinterpret_cast", "requires", "short", "signed", "sizeof", "static", "static_assert", "static_cast", "struct", "switch", "template", "this", "thread_local", "throw", "try", "typedef", "typeid", "typename", "union", "unsigned", "using", "virtual", "volatile", "wchar_t", "xor", "xor_eq",
   "return", "true", "false", "read_u64", "write_u64", "write_text", "expect_eof", "reject"]
private def name : Parser String := do
  match ← take with
  | .word w =>
    -- Restrict local names to [a-z][a-z0-9]*, avoiding standard-header
    -- and implementation-reserved macro spellings in the trusted prelude.
    if w.toList.head?.any (fun c => c >= 'a' && c <= 'z') &&
        w.toList.all (fun c => c >= 'a' && c <= 'z' || c.isDigit) && !reserved.contains w then return w
    else fail "expected non-reserved identifier"
  | _ => fail "expected identifier"
private def lookup (w : String) : Parser Binding := do
  match ((← get).scopes.flatten.find? (fun b => b.source == w)) with
  | some b => if b.initialized then return b else fail "use before initialization"
  | none => fail s!"undeclared local {w}"
private def declare (w : String) (ty : Ty) : Parser String := do
  let s ← get
  let current := s.scopes.headD []
  if current.any (fun b => b.source == w) then fail s!"duplicate declaration {w}"
  let id := s!"{w}${s.nextId}"
  set {s with nextId := s.nextId+1, scopes := ({source := w, localId := id, ty, initialized := false} :: current) :: s.scopes.drop 1}
  return id
private def markInitialized (id : String) : Parser Unit :=
  modify fun s => {s with scopes := s.scopes.map (·.map fun b => if b.localId == id then {b with initialized := true} else b)}
private def requireTy (actual expected : Ty) : Parser Unit :=
  if actual == expected then pure () else fail "type mismatch (implicit conversions are unsupported)"
private def opInfo : String → Option (Nat × BinOp × Ty × Ty)
  | "||" => some (1, .or, .bool, .bool)
  | "&&" => some (2, .and, .bool, .bool)
  | "==" => some (3, .eq, .uint64, .bool)
  | "!=" => some (3, .ne, .uint64, .bool)
  | "<" => some (4, .lt, .uint64, .bool)
  | "<=" => some (4, .le, .uint64, .bool)
  | ">" => some (4, .gt, .uint64, .bool)
  | ">=" => some (4, .ge, .uint64, .bool)
  | "+" => some (5, .add, .uint64, .uint64)
  | "-" => some (5, .sub, .uint64, .uint64)
  | "*" => some (6, .mul, .uint64, .uint64)
  | "/" => some (6, .div, .uint64, .uint64)
  | "%" => some (6, .mod, .uint64, .uint64)
  | _ => none

mutual
private def expr : Nat → Nat → Parser (Expr × Ty)
  | 0, _ => fail "expression nesting limit"
  | n+1, prec => do
    let lhs ← atom n
    infixExpr n prec lhs
private def atom : Nat → Parser (Expr × Ty)
  | 0 => fail "expression nesting limit"
  | n+1 => do
    if ← eat "(" then
      let e ← expr n 1
      expect ")"
      return e
    if ← eat "!" then
      let (e,t) ← atom n
      requireTy t .bool
      return (.unop .not e, .bool)
    if ← eat "-" then
      let (e,t) ← atom n
      requireTy t .uint64
      return (.unop .neg e, .uint64)
    match ← peek with
    | some (.word "true") => let _ ← take; return (.lit (.bool true), .bool)
    | some (.word "false") => let _ ← take; return (.lit (.bool false), .bool)
    | some (.word w) =>
      if w.toList.head?.any Char.isDigit then
        let _ ← take
        if !w.endsWith "ULL" then fail "unsigned literals require ULL"
        let digits := String.ofList (w.toList.take (w.length-3))
        if !digits.toList.all Char.isDigit || digits.isEmpty then fail "invalid decimal literal"
        if digits.length > 1 && digits.startsWith "0" then fail "octal literals are unsupported"
        let some v := digits.toNat? | fail "invalid unsigned literal"
        if v >= 2^64 then fail "unsigned literal overflow"
        return (.lit (.uint64 (UInt64.ofNat v)), .uint64)
      let w ← name
      let b ← lookup w
      if ← eat "[" then
        requireTy b.ty (.array .uint64)
        let (i,t) ← expr n 1
        requireTy t .uint64
        expect "]"
        return (.arrGet (.var b.localId) i, .uint64)
      return (.var b.localId, b.ty)
    | _ => fail "expected expression"
private def infixExpr : Nat → Nat → (Expr × Ty) → Parser (Expr × Ty)
  | 0, _, _ => fail "expression length limit"
  | n+1, minPrec, (lhs,lt) => do
    let some (.word w) ← peek | return (lhs,lt)
    let some (prec,op,argTy,resultTy) := opInfo w | return (lhs,lt)
    if prec < minPrec then return (lhs,lt)
    let _ ← take
    let (rhs,rt) ← expr n (prec+1)
    if op == .eq || op == .ne then
      if !(lt == .uint64 || lt == .bool) then fail "pointer comparison is unsupported"
      requireTy rt lt
    else requireTy lt argTy; requireTy rt argTy
    infixExpr n minPrec (.binop op lhs rhs,resultTy)
end

mutual
private def stmt : Nat → Parser Stmt
  | 0 => fail "statement nesting limit"
  | n+1 => do
    if ← eat "{" then
      modify fun s => {s with scopes := [] :: s.scopes}
      let ss ← stmts n
      modify fun s => {s with scopes := s.scopes.drop 1}
      return .block ss
    if ← eat "if" then
      expect "("
      let (e,t) ← expr n 1
      requireTy t .bool
      expect ")"
      let a ← braced n
      let b ← if ← eat "else" then braced n else pure .skip
      return .ite e a b
    if ← eat "while" then
      expect "("
      let (e,t) ← expr n 1
      requireTy t .bool
      expect ")"
      return .while e (← braced n)
    if ← eat "return" then expect ";"; return .ret (.lit .unit)
    if ← eat "u64" then
      let pointer ← eat "*"
      let w ← name
      let ty := if pointer then .array .uint64 else .uint64
      let id ← declare w ty
      expect "="
      if pointer && (← eat "new") then
        expect "u64"; expect "["
        let (e,t) ← expr n 1
        requireTy t .uint64
        expect "]"; expect "("; expect ")"; expect ";"
        markInitialized id
        return .alloc id .uint64 e
      let (e,t) ← expr n 1
      requireTy t ty
      expect ";"
      markInitialized id
      return .decl id ty e
    if ← eat "bool" then
      let w ← name
      let id ← declare w .bool
      expect "="
      let (e,t) ← expr n 1
      requireTy t .bool
      expect ";"
      markInitialized id
      return .decl id .bool e
    if ← eat "read_u64" then
      expect "("
      let b ← lookup (← name)
      requireTy b.ty .uint64
      expect ")"; expect ";"
      return .readU64 b.localId
    if ← eat "write_u64" then
      expect "("
      let (e,t) ← expr n 1
      requireTy t .uint64
      expect ")"; expect ";"
      return .writeU64 e
    if ← eat "write_text" then
      expect "("
      let .text s ← take | fail "write_text requires a literal"
      expect ")"; expect ";"
      return .writeText s
    if ← eat "reject" then
      expect "("; expect ")"; expect ";"
      return .reject
    if ← eat "expect_eof" then
      expect "("; expect ")"; expect ";"
      return .expectEof
    let b ← lookup (← name)
    if ← eat "[" then
      requireTy b.ty (.array .uint64)
      let (i,it) ← expr n 1
      requireTy it .uint64
      expect "]"; expect "="
      let (v,vt) ← expr n 1
      requireTy vt .uint64
      expect ";"
      return .arrSet (.var b.localId) i v
    expect "="
    let (e,t) ← expr n 1
    requireTy t b.ty
    expect ";"
    return .assign b.localId e
private def braced : Nat → Parser Stmt
  | 0 => fail "block nesting limit"
  | n+1 => do
    if (← peek) != some (.word "{") then fail "controlled statements require braces"
    stmt n
private def stmts : Nat → Parser (List Stmt)
  | 0 => fail "block length limit"
  | n+1 => do
    if ← eat "}" then return []
    let s ← stmt n
    return s :: (← stmts n)
end

/-- Parse only the algorithm section, including its `void solve()` declaration. -/
def parseSolve (source : String) : Except String Program := do
  let ts ← tokenize source
  let p : Parser Program := do
    expect "void"; expect "solve"; expect "("; expect ")"
    let body ← braced (ts.length * 4 + 32)
    if (← peek).isSome then fail "unexpected source after solve"
    return {funs := [], main := body}
  return (← p.run {tokens := ts}).1

/-- Exact bytes of a file at elaboration time. File changes require rebuilding the
module containing this term; the resulting constant contains the source itself. -/
syntax "cpp_file% " str : term
elab_rules : term
  | `(cpp_file% $path:str) => do
    let content ← IO.FS.readFile path.getString
    return Lean.mkStrLit content

/-- No source is accepted outside the fixed prelude and fixed entry wrapper. -/
def wrapper : String := "\nint main() { solve(); return 0; }\n"
def parseSubmissionWith (prelude source : String) : Except String Program := do
  if !source.startsWith prelude then throw "prelude does not match the trusted runtime"
  if !source.endsWith wrapper then throw "entry wrapper does not match"
  if source.length < prelude.length + wrapper.length then throw "missing solve body"
  parseSolve (String.ofList (source.toList.drop prelude.length |>.take (source.length-prelude.length-wrapper.length)))

def trustedPrelude : String := cpp_file% "runtime/radix_io.hpp"

def parseSubmission (source : String) : Except String Program :=
  parseSubmissionWith trustedPrelude source

deriving instance Lean.ToExpr for Radix.Ty
deriving instance Lean.ToExpr for Radix.Value
deriving instance Lean.ToExpr for Radix.BinOp
deriving instance Lean.ToExpr for Radix.UnaryOp
deriving instance Lean.ToExpr for Radix.Expr
deriving instance Lean.ToExpr for Radix.Stmt
deriving instance Lean.ToExpr for Radix.FunDecl
deriving instance Lean.ToExpr for Radix.Program

/-- Elaborate the checked parse to a concrete AST for tractable program proofs.
A separate parsing equation checks this mechanically generated AST. -/
syntax "cpp_program% " str : term
elab_rules : term
  | `(cpp_program% $path:str) => do
    let source ← IO.FS.readFile path.getString
    match parseSubmission source with
    | .ok p => return Lean.toExpr p
    | .error e => throwError "C++ subset parse failed: {e}"

end Radix.Cpp
