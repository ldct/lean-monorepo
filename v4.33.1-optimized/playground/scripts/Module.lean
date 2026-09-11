module
public import Mathlib

public theorem optimized_module_check (a b : ℤ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
