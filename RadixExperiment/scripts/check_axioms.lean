import Radix.Benchmarks.ABC177CRefinement
import Radix.Proofs.RejectionSoundness
import Radix.Proofs.MemorySafety

-- Re-run this file even when Lake's proof artifacts are already cached.
#print axioms Radix.Benchmarks.ABC177C.refinement
#print axioms Radix.Benchmarks.ABC177C.source_certificate
#print axioms Radix.Benchmarks.ABC177C.reference_parses
#print axioms Radix.Benchmarks.ABC177C.optimized_parses
#print axioms Radix.Stmt.interp_sound
#print axioms Radix.Stmt.interp_rejected_sound
#print axioms Radix.Stmt.interp_complete
#print axioms Radix.BigStep.heap_persistent
