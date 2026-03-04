import Lean
import Lean.Data.Json.Basic
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

open Lean Json ToJson FromJson


namespace test_json

structure Wrapper: Type where
  data: Array Int
deriving ToJson, FromJson, Inhabited, Repr

def get_ledger_from_json_string (s: String): Except String Wrapper := do
  let j : Json <- Json.parse s
  let ledger : Wrapper <- fromJson? j
  return ledger

def test_str := "{
  \"data\": [1, 2, 3]
}
"
#eval (get_ledger_from_json_string test_str)


end test_json