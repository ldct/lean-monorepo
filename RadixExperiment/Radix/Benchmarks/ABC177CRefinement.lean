import Radix.Benchmarks.InputValidation
import Radix.Benchmarks.ReferenceLoop
import Radix.Benchmarks.OptimizedLoop
import Radix.Proofs.ControlFlow
import Radix.Proofs.BlockComposition

/-! Whole-program exact-output refinement for the actual standalone sources.
The proof extracts the common executable validation from a successful reference
run, constructs both finite computation suffixes, and compares their output.
The common theorem has no input-domain predicate or testing fuel. -/
namespace Radix.Benchmarks.ABC177C

private theorem reference_split : reference.main =
    .block (prefixStatements ++ referenceStatements.drop 9) := by rfl

private theorem optimized_split : optimized.main =
    .block (prefixStatements ++ optimizedStatements.drop 9) := by rfl

/-- The linear-time submission preserves every complete successful execution of
its quadratic reference. Both programs are parsed from their standalone files. -/
theorem refinement : Refines reference optimized := by
  intro input output accepted
  obtain ⟨referenceFinal, referenceRun, referenceOutput⟩ :=
    accepted.normal (show reference.main.mayReturn = false from rfl)
  rw [reference_split, BigStep.block_append_normal_iff] at referenceRun
  obtain ⟨parsed, prefixRun, tailRun⟩ := referenceRun
  change BigStep (PState.initFromProgram reference input) inputPrefix (.normal parsed) at prefixRun
  change BigStep parsed referenceTail (.normal referenceFinal) at tailRun
  obtain ⟨n, address, _lower, upper, valid, modulus, answerZero⟩ := inputPrefix_validates prefixRun
  obtain ⟨xs, length, bounds, array⟩ := valid.toList
  obtain ⟨refFinal, refAnswer, refRun, refMath, refOutput⟩ :=
    referenceTail_total xs parsed n address valid.2.2.1 valid.1 valid.2.1
      modulus answerZero upper length bounds array
  have sameReference : refFinal = referenceFinal := by
    exact StmtResult.normal.inj (BigStep.det refRun tailRun)
  obtain ⟨optFinal, optAnswer, optRun, optMath, optOutput⟩ :=
    optimizedTail_total xs parsed n address valid.2.2.1 valid.1 valid.2.1
      modulus answerZero upper length bounds (by
        intro k x hx
        have hk : k < xs.length := List.getElem?_eq_some_iff.mp hx |>.1
        have hx' : xs[k] = x := List.getElem?_eq_some_iff.mp hx |>.2
        simpa [hx'] using array k hk)
  have answerEq : optAnswer = refAnswer := UInt64.toNat_inj.mp (optMath.trans refMath.symm)
  refine ⟨.normal optFinal, ?_, trivial, ?_⟩
  · rw [optimized_split, BigStep.block_append_normal_iff]
    exact ⟨parsed, prefixRun, optRun⟩
  · change optFinal.output = output
    rw [optOutput, answerEq, ← refOutput, sameReference, referenceOutput]

/-- A single certificate packages source identity with algorithmic refinement.
Its parsing conjuncts carry the explicitly documented native-evaluation trust. -/
theorem source_certificate :
    Cpp.parseSubmission referenceSource = .ok reference ∧
    Cpp.parseSubmission optimizedSource = .ok optimized ∧
    Refines reference optimized :=
  ⟨reference_parses, optimized_parses, refinement⟩

end Radix.Benchmarks.ABC177C
