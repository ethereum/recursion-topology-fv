import VanillaZkVM.VMs.MemorySanity
import VanillaZkVM.VMs.MultiStep.MultiStep

/-!
# Consistency-floor model for multi-step CTE

A two-segment, one-step-per-segment system over `MemorySanity.exactVC` witnesses
that all hypotheses of `MultiStep.System.cte` are jointly satisfiable (I6). Each
SNARK layer uses the identity extractor; `simpa` bridges the verify/relation gap.

All declarations are private; this module adds no public API.
-/

namespace VanillaZkVM
namespace MultiStepSanity

open MultiStep
open MemorySanity

private def memFree : MemFreePredicate :=
  fun _ _ _ _ => True

private def isa : ISA.System exactVC.Index exactVC.Value where
  code := fun _ => .arith
  memFreePred := fun _ => memFree
  indexOfWord := fun word => decide (word ≠ 0)
  valueOfWord := fun word => decide (word ≠ 0)

private def leafVerify (st : RecStmt exactVC) (w : SegWitness exactVC) : Prop :=
  w.states 0 = st.S0 ∧
  w.states 1 = st.SN ∧
  ∀ j, j < 1 → isa.committedOperation (w.states j) (w.states (j + 1)) (w.steps j)

private def convertVerify (st : RecStmt exactVC) (w : SegWitness exactVC) : Prop :=
  leafVerify st w ∧ st.N = 1

private abbrev CombProof := CombineWitness exactVC (SegWitness exactVC) Empty

private def combineVerify (st : RecStmt exactVC) (w : CombProof) : Prop :=
  (match w.proofL with
   | .inl p => convertVerify ⟨st.S0, w.Smid, w.NL⟩ p
   | .inr e => nomatch e) ∧
  (match w.proofR with
   | .inl p => convertVerify ⟨w.Smid, st.SN, w.NR⟩ p
   | .inr e => nomatch e) ∧
  w.NL + w.NR = st.N ∧ 1 ∣ w.NL ∧ 1 ∣ w.NR ∧ w.NL ≥ 1 ∧ w.NR ≥ 1

private def embedVerify (st : EmbedStmt exactVC) (w : CombProof) : Prop :=
  combineVerify ⟨st.S0, st.ST, 2⟩ w

private def system : MultiStep.System where
  VC := exactVC
  Nseg := 1
  T := 2
  isa := isa
  hNseg := by omega
  hDvd := by norm_num
  hT := by omega
  LeafProof := SegWitness exactVC
  leafVerify := leafVerify
  ConvertProof := SegWitness exactVC
  convertVerify := convertVerify
  CombineProof := CombProof
  combineVerify := combineVerify
  EmbedProof := CombProof
  embedVerify := embedVerify

private def mapProof : SegWitness exactVC ⊕ Empty → SegWitness exactVC ⊕ CombProof
  | .inl p => .inl p
  | .inr e => nomatch e

private def combExtract (w : CombProof) : CombineWitness exactVC (SegWitness exactVC) CombProof :=
  ⟨mapProof w.proofL, mapProof w.proofR, w.Smid, w.NL, w.NR⟩

private theorem assumptions : system.Assumptions := by
  refine ⟨?_, ?_, ?_, ?_, exactVC_complete, exactVC_positionBinding,
    exactVC_updateBinding⟩
  · -- KS of leaf: identity extractor
    refine ⟨⟨fun _ p => p⟩, ?_⟩
    intro st p hp
    simpa [system, MultiStep.System.ASLeaf, MultiStep.System.RLeaf, leafVerify] using hp
  · -- KS of combine: combExtract maps CombProof → RCombine.Wit
    refine ⟨⟨fun st p => combExtract p⟩, ?_⟩
    intro st p hp
    simp only [system, MultiStep.System.ASCombine, MultiStep.System.RCombine,
      combineVerify, combExtract, mapProof] at hp ⊢
    obtain ⟨hL, hR, hsum, hdvL, hdvR, hgeL, hgeR⟩ := hp
    refine ⟨?_, ?_, hsum, hdvL, hdvR, hgeL, hgeR⟩
    · cases h : p.proofL with
      | inl pl => rw [h] at hL; simpa [convertVerify] using hL
      | inr e => exact nomatch e
    · cases h : p.proofR with
      | inl pr => rw [h] at hR; simpa [convertVerify] using hR
      | inr e => exact nomatch e
  · -- KS of convert: identity extractor
    refine ⟨⟨fun _ p => p⟩, ?_⟩
    intro st p hp
    simpa [system, MultiStep.System.ASConvert, MultiStep.System.RConvert, convertVerify] using hp
  · -- KS of embed: identity extractor (REmbed.Wit = CombineProof = CombProof)
    refine ⟨⟨fun _ p => p⟩, ?_⟩
    intro st p hp
    simpa [system, MultiStep.System.ASEmbed, MultiStep.System.REmbed, embedVerify] using hp

private def fullState : FullVMState exactVC :=
  ⟨0, fun _ => 0, zeroMemory⟩

private def committedState : CommittedVMState exactVC :=
  toCommitted fullState

private def segmentWitness : SegWitness exactVC where
  states := fun _ => committedState
  steps := fun _ => .other

private def combineWitness : CombProof where
  proofL := .inl segmentWitness
  proofR := .inl segmentWitness
  Smid := committedState
  NL := 1
  NR := 1

set_option linter.flexible false in
example : system.toZkVM.verify ⟨fullState, fullState⟩ combineWitness := by
  simp [MultiStep.System.toZkVM, system, embedVerify, combineVerify,
    convertVerify, leafVerify, combineWitness, segmentWitness, committedState,
    isa, memFree, ISA.System.committedOperation, ISA.System.selectedMemFreePred,
    CommittedMemory.step]

example : system.toZkVM.step fullState fullState := by
  simp [MultiStep.System.toZkVM, system, ISA.System.stepPlain,
    ISA.System.operation, isa, memFree, fullState]

example : system.toZkVM.CTE :=
  system.cte assumptions

end MultiStepSanity
end VanillaZkVM
