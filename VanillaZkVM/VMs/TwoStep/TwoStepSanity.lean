import VanillaZkVM.VMs.MemorySanity
import VanillaZkVM.VMs.TwoStep.TwoStep

/-!
# Consistency-floor model for two-step CTE

A one-segment, one-step system over `MemorySanity.exactVC` witnesses that all
hypotheses of `TwoStep.System.cte` are jointly satisfiable (I6). Its proof
objects are relation witnesses, so both argument systems are knowledge-sound by
the identity extractor. A concrete final proof is accepted, and the step is an
arithmetic `.other` transition rather than an everywhere-true
relation. A read `MemStep` is rejected for the same program counter, checking
that the explicit witness cannot select another operation class.

All declarations are private; this module adds no public API.
-/

namespace VanillaZkVM
namespace TwoStepSanity

open TwoStep
open MemorySanity

private def memFree : MemFreePredicate :=
  fun _ _ _ _ => True

private def isa : ISA.System exactVC.Index exactVC.Value where
  code := fun _ => .arith
  memFreePred := fun _ => memFree
  indexOfWord := fun word => decide (word ≠ 0)
  valueOfWord := fun word => decide (word ≠ 0)

private def segVerify (st : SegStmt exactVC) (w : SegWitness exactVC) : Prop :=
  w.states 0 = st.Sin ∧
  w.states 1 = st.Sout ∧
  ∀ j, j < 1 → isa.committedOperation (w.states j) (w.states (j + 1)) (w.steps j)

private def finalVerify
    (st : FinalStmt exactVC) (w : FinalWitness exactVC (SegWitness exactVC)) : Prop :=
  w.boundary 0 = st.S0 ∧
  w.boundary 1 = st.ST ∧
  ∀ i, i < 1 → segVerify ⟨w.boundary i, w.boundary (i + 1)⟩ (w.proofs i)

private def system : TwoStep.System where
  VC := exactVC
  Nseg := 1
  m := 1
  isa := isa
  SegProof := SegWitness exactVC
  segVerify := segVerify
  FinalProof := FinalWitness exactVC (SegWitness exactVC)
  finalVerify := finalVerify

private theorem assumptions : system.Assumptions := by
  refine ⟨?_, ?_, exactVC_complete, exactVC_positionBinding,
    exactVC_updateBinding⟩
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [TwoStep.System.ASSeg, TwoStep.System.RSeg, system, segVerify] using hverify
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [TwoStep.System.ASFinal, TwoStep.System.RFinal, system, finalVerify] using hverify

private def fullState : FullVMState exactVC :=
  ⟨0, fun _ => 0, zeroMemory⟩

private def committedState : CommittedVMState exactVC :=
  toCommitted fullState

private theorem accepts_arith_memStep :
    isa.committedOperation committedState committedState .other := by
  simp [ISA.System.committedOperation, ISA.System.selectedMemFreePred,
    isa, committedState, toCommitted, fullState, memFree, CommittedMemory.step]

private theorem rejects_read_memStep_for_arith :
    ¬isa.committedOperation committedState committedState
      (.read false false (exactVC.openProof zeroMemory false)) := by
  simp [ISA.System.committedOperation, ISA.System.selectedMemFreePred,
    isa, committedState, toCommitted, fullState, memFree,
    CommittedMemory.step, CommittedMemory.read]

private def segmentWitness : SegWitness exactVC where
  states := fun _ => committedState
  steps := fun _ => .other

private def finalWitness : FinalWitness exactVC (SegWitness exactVC) where
  boundary := fun _ => committedState
  proofs := fun _ => segmentWitness

example : system.toZkVM.verify ⟨fullState, fullState⟩ finalWitness := by
  simp [TwoStep.System.toZkVM, system, finalVerify, finalWitness,
    segmentWitness, segVerify, committedState, isa, memFree,
    ISA.System.committedOperation, ISA.System.selectedMemFreePred,
    CommittedMemory.step]

example : system.toZkVM.step fullState fullState := by
  simp [TwoStep.System.toZkVM, system, ISA.System.stepPlain,
    ISA.System.operation, isa, memFree, fullState]

example : system.toZkVM.CTE := by
  exact system.cte (by simp [system]) assumptions

end TwoStepSanity
end VanillaZkVM
