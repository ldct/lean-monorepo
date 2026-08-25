import Playground.PrimeSieve.Basic

/-!
# Simproc that uses precomputed sieve hypotheses

The simproc `primeSieveSimproc` rewrites occurrences of `Nat.Prime k` (with
`k` a numeric literal) to `True` or `False` whenever the local context contains
a hypothesis of the form `_ : PrimeSieve.Valid N` with `k ≤ N`.

The user obtains the `Valid N` hypothesis once via `decide` (the sieve
precompute) and then a single `simp only [primeSieveSimproc]` collapses every
primality goal in scope. All proofs go through the kernel.
-/

namespace PrimeSieve

open Lean Meta Simp

simproc_decl primeSieveSimproc (Nat.Prime _) := fun e => do
  -- Match `Nat.Prime k`
  let_expr Nat.Prime kExpr := e | return .continue
  let some k := kExpr.nat? | return .continue
  -- Search local context for a `PrimeSieve.Valid N` hypothesis
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail then continue
    let ty ← instantiateMVars ldecl.type
    let_expr PrimeSieve.Valid NExpr := ty | continue
    let some N := NExpr.nat? | continue
    if k > N then continue
    -- Use the Lean function at meta-time to decide which side
    let isP := isPrime N k
    let nLit := mkNatLit N
    let kLit := mkNatLit k
    let hk ← mkDecideProof (← mkAppM ``LE.le #[kLit, nLit])
    let lookupVal := if isP then mkConst ``Bool.true else mkConst ``Bool.false
    let lhsExpr ← mkAppM ``PrimeSieve.isPrime #[nLit, kLit]
    let lookupTy ← mkAppM ``Eq #[lhsExpr, lookupVal]
    let lookupProof ← mkDecideProof lookupTy
    if isP then
      let primeProof ← mkAppM ``PrimeSieve.prime_of_lookup
        #[ldecl.toExpr, hk, lookupProof]
      let eqTrueProof ← mkAppM ``eq_true #[primeProof]
      return .done { expr := mkConst ``True, proof? := some eqTrueProof }
    else
      let notPrimeProof ← mkAppM ``PrimeSieve.not_prime_of_lookup
        #[ldecl.toExpr, hk, lookupProof]
      let eqFalseProof ← mkAppM ``eq_false #[notPrimeProof]
      return .done { expr := mkConst ``False, proof? := some eqFalseProof }
  return .continue

end PrimeSieve
