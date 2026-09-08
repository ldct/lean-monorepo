import Radix.State

namespace Radix
namespace ByteIO

def whitespace (b : UInt8) : Bool := (9 ≤ b && b ≤ 13) || b == 32

def skipWhitespace (input : ByteArray) (cursor : Nat) : Nat :=
  go (input.size - cursor) cursor
where
  go : Nat → Nat → Nat
  | 0, pos => pos
  | fuel + 1, pos =>
    if whitespace (input.get! pos) then go fuel (pos + 1) else pos

/-- The cursor on both acceptance and rejection includes bytes already consumed. -/
def readU64 (input : ByteArray) (cursor : Nat) : Option UInt64 × Nat :=
  let pos := skipWhitespace input cursor
  digits (input.size - pos) pos 0 false
where
  digits : Nat → Nat → Nat → Bool → Option UInt64 × Nat
  | 0, pos, acc, seen => (if seen then some acc.toUInt64 else none, pos)
  | fuel + 1, pos, acc, seen =>
    let b := input.get! pos
    if whitespace b then (if seen then some acc.toUInt64 else none, pos + 1)
    else if 48 ≤ b && b ≤ 57 then
      let acc' := acc * 10 + (b.toNat - 48)
      if acc' < 18446744073709551616 then digits fuel (pos + 1) acc' true
      else (none, pos + 1)
    else (none, pos + 1)

def writeU64 (n : UInt64) : ByteArray := (toString n.toNat).toUTF8
end ByteIO
end Radix
