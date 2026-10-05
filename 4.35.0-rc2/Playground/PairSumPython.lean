import Playground.PairSum
import Playground.PythonSyntax

/-!
# `ans1` and `ans5` in Python syntax

The two imperative solutions from `Playground.PairSum`, written with the
syntax defined in `Playground.PythonSyntax`.
-/

namespace Py

-- O(n²) algorithm
def ans1(A: Array Int) -> Int:
    total: Int = 0
    for i in range(len(A)):
        for j in range(i + 1, len(A)):
            total = (total + A[i] * A[j]) % MODULUS
    return total

-- O(n) cofactor loop
def ans5(A: Array Int) -> Int:
    ret: Int = 0
    cofactor = sum(A)
    for a in A:
        cofactor -= a
        ret += a * cofactor
    return ret % MODULUS

end Py

-- The Python definitions expand to the same code as the hand-written ones, so
-- every correctness proof in `Playground.PairSum` applies to them unchanged.
example : Py.ans1 = ans1 := rfl
example : Py.ans5 = ans5 := rfl

#guard Py.ans1 #[1, 2, 3] == 11
#guard Py.ans5 #[1, 2, 3] == 11
