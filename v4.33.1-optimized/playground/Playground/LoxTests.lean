module

import all Playground.Lox

theorem matchChar_prop (c : Char) (s : State) :
    (matchChar c).run s =
      if s.input[s.current]? = some c then
        (true, { s with current := s.current + 1 })
      else
        (false, s) := by
  by_cases hEnd : s.input.size ≤ s.current
  · -- At or past EOF: the lookup fails and the state is unchanged.
    have hlookup : s.input[s.current]? = none :=
      Array.getElem?_eq_none hEnd
    simp [matchChar, isAtEnd, hEnd]
    rfl
  · have hlt : s.current < s.input.size := Nat.lt_of_not_ge hEnd
    have hlookup : s.input[s.current]? = some (s.input[s.current]'hlt) :=
      Array.getElem?_eq_getElem hlt
    by_cases hchar : s.input[s.current]'hlt = c <;>
      simp [matchChar, isAtEnd, peek, incrementCurrent,
        hEnd, hlookup, hchar]
    rfl
    rfl
