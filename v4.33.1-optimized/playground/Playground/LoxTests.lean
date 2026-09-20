import Playground.Lox


theorem matchChar_prop (c : Char) (s : State) : (matchChar c).run s =
  if s.input[s.current]? = some c then
    (true, { s with current := s.current + 1 })
  else
    (false, s) := by sorry
