import VanillaZkVM.VMs.MemorySanity
import VanillaZkVM.VMs.VanillaVM.VanillaVM

/-!
# Consistency check for the assembled Vanilla VM

This file constructs a two-step example in which every assumption of
`VanillaVM.System.cte_main` holds and the final verifier accepts a proof. Each
of its two segments executes a hash operation and records the required Keccak
call in a nonempty bus. For simplicity, each commitment stores its input
directly, and each proof contains the data that its extractor returns. These
choices do not model deployed cryptography; they show that the final theorem's
assumptions can hold together and that its verifier can accept.

All declarations are private, so this file adds no public API.

## Main results
* `assumptions_and_accepted_proof` — the assumptions, an accepted recursive
  proof, and an accepted plain VM step all occur in one concrete example.
* The final private example applies `VanillaVM.System.cte_main` to that same
  example.
-/

namespace VanillaZkVM
namespace VanillaVMSanity

open Bus
open MemorySanity

/-! ## A one-step segment system -/

private def memFree : MemFreePredicate :=
  fun _ _ _ _ => True

private def isa : ISA.System exactVC.Index exactVC.Value where
  code := fun _ => .hash
  memFreePred := fun _ => memFree
  indexOfWord := fun word => decide (word ≠ 0)
  valueOfWord := fun word => decide (word ≠ 0)

private def fullState : FullVMState exactVC :=
  ⟨0, fun _ => 0, zeroMemory⟩

private def committedState : CommittedVMState exactVC :=
  MultiStep.toCommitted fullState

private def hashCall : HashCall :=
  HashCall.ofStates committedState committedState

private def segmentBus : SegmentBus :=
  ⟨[hashCall], [], []⟩

private def stepBusModel (S₁ S₂ : CommittedVMState exactVC)
    (w : MemStep exactVC) (bus : SegmentBus) : Prop :=
  w = .other ∧ S₂.mem = S₁.mem ∧
    HashCall.ofStates S₁ S₂ ∈ bus.keccakCalls

private def innerStepVerify (statement : InnerStepStmt exactVC SegmentBus)
    (trace : SegmentTrace exactVC) : Prop :=
  trace.states 0 = statement.Sin ∧
  trace.states 1 = statement.Sout ∧
  (∀ j, j < 1 →
    stepBusModel (trace.states j) (trace.states (j + 1))
      (trace.steps j) trace.bus) ∧
  statement.busCom = trace.bus

private def innerKeccakVerify (digest : SegmentBus) (bus : SegmentBus) : Prop :=
  digest = bus

private def innerPoseidonVerify (digest : SegmentBus) (bus : SegmentBus) : Prop :=
  (∀ call, call ∉ bus.poseidonCalls) ∧ digest = bus

private def innerRangeVerify (digest : SegmentBus) (bus : SegmentBus) : Prop :=
  digest = bus

private abbrev SegmentProof :=
  SegmentWitness SegmentBus (SegmentTrace exactVC)
    SegmentBus SegmentBus SegmentBus

private def segmentVerify (statement : SegmentStmt exactVC)
    (proof : SegmentProof) : Prop :=
  innerStepVerify ⟨statement.Sin, statement.Sout, proof.busCom⟩ proof.stepProof ∧
  innerKeccakVerify proof.busCom proof.keccakProof ∧
  innerPoseidonVerify proof.busCom proof.poseidonProof ∧
  innerRangeVerify proof.busCom proof.rangeProof

private def segmentSystem : Bus.System where
  VC := exactVC
  Nseg := 1
  isa := isa
  BusDigest := SegmentBus
  busHash := id
  hashChipAt := fun _ => .keccak
  binInlinePred := memFree
  rangePred := fun _ _ => True
  binDecomposition := by simp [isa, memFree]
  SegmentProof := SegmentProof
  segmentVerify := segmentVerify
  InnerStepProof := SegmentTrace exactVC
  innerStepVerify := innerStepVerify
  InnerKeccakProof := SegmentBus
  innerKeccakVerify := innerKeccakVerify
  InnerPoseidonProof := SegmentBus
  innerPoseidonVerify := innerPoseidonVerify
  InnerRangeProof := SegmentBus
  innerRangeVerify := innerRangeVerify

private theorem segment_assumptions : segmentSystem.Assumptions := by
  constructor
  · intro bus bus' h
    exact h
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [Bus.System.ASInnerStep, Bus.System.RInnerStep, segmentSystem,
      Bus.System.stepBus, stepBusModel, innerStepVerify, isa] using hverify
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [Bus.System.ASInnerKeccak, Bus.System.RInnerKeccak,
      Bus.System.RInnerChip, Bus.System.keccakChip, segmentSystem, isa,
      memFree, innerKeccakVerify] using hverify
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [Bus.System.ASInnerPoseidon, Bus.System.RInnerPoseidon,
      Bus.System.RInnerChip, Bus.System.poseidonChip, segmentSystem, isa,
      memFree, innerPoseidonVerify] using hverify
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [Bus.System.ASInnerRange, Bus.System.RInnerRange,
      Bus.System.RInnerChip, Bus.System.rangeChip, segmentSystem,
      innerRangeVerify] using hverify
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [Bus.System.ASSegment, Bus.System.RSegment, segmentSystem,
      segmentVerify] using hverify

/-! ## A depth-one recursive proof -/

private def convertVerify (statement : MultiStep.RecStmt exactVC)
    (proof : SegmentProof) : Prop :=
  segmentVerify ⟨statement.S0, statement.SN⟩ proof ∧ statement.N = 1

private abbrev CombineProof :=
  MultiStep.CombineWitness exactVC SegmentProof Empty

private def combineVerify (statement : MultiStep.RecStmt exactVC)
    (proof : CombineProof) : Prop :=
  (match proof.proofL with
   | .inl p => convertVerify ⟨statement.S0, proof.Smid, proof.NL⟩ p
   | .inr impossible => nomatch impossible) ∧
  (match proof.proofR with
   | .inl p => convertVerify ⟨proof.Smid, statement.SN, proof.NR⟩ p
   | .inr impossible => nomatch impossible) ∧
  proof.NL + proof.NR = statement.N ∧
  1 ∣ proof.NL ∧ 1 ∣ proof.NR ∧ proof.NL ≥ 1 ∧ proof.NR ≥ 1

private def embedVerify (statement : MultiStep.EmbedStmt exactVC)
    (proof : CombineProof) : Prop :=
  combineVerify ⟨statement.S0, statement.ST, 2⟩ proof

private def system : VanillaVM.System where
  segment := segmentSystem
  T := 2
  hNseg := by simp [segmentSystem]
  hDvd := by simp [segmentSystem]
  hT := by simp [segmentSystem]
  ConvertProof := SegmentProof
  convertVerify := convertVerify
  CombineProof := CombineProof
  combineVerify := combineVerify
  EmbedProof := CombineProof
  embedVerify := embedVerify

private def mapProof : SegmentProof ⊕ Empty → SegmentProof ⊕ CombineProof
  | .inl proof => .inl proof
  | .inr impossible => nomatch impossible

private def combineExtract (proof : CombineProof) :
    MultiStep.CombineWitness exactVC SegmentProof CombineProof :=
  ⟨mapProof proof.proofL, mapProof proof.proofR, proof.Smid, proof.NL, proof.NR⟩

private theorem assumptions : system.Assumptions := by
  refine ⟨segment_assumptions, ?_, ?_, ?_, exactVC_complete,
    exactVC_positionBinding, exactVC_updateBinding⟩
  · -- The convert proof already contains the segment proof it is meant to reveal.
    refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [system, segmentSystem, VanillaVM.System.toMultiStep,
      MultiStep.System.ASConvert, MultiStep.System.RConvert, convertVerify]
      using hverify
  · -- The combine proof exposes its two children and their common boundary.
    refine ⟨⟨fun _ proof => combineExtract proof⟩, ?_⟩
    intro statement proof hverify
    simp only [system, VanillaVM.System.toMultiStep,
      MultiStep.System.ASCombine, MultiStep.System.RCombine, combineVerify,
      combineExtract, mapProof] at hverify ⊢
    obtain ⟨hleft, hright, hsum, hdivLeft, hdivRight, hgeLeft, hgeRight⟩ :=
      hverify
    refine ⟨?_, ?_, hsum, hdivLeft, hdivRight, hgeLeft, hgeRight⟩
    · cases heq : proof.proofL with
      | inl leftProof =>
          rw [heq] at hleft
          simpa [convertVerify] using hleft
      | inr impossible => exact nomatch impossible
    · cases heq : proof.proofR with
      | inl rightProof =>
          rw [heq] at hright
          simpa [convertVerify] using hright
      | inr impossible => exact nomatch impossible
  · -- The embed proof is exactly the combine proof it is meant to reveal.
    refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [system, segmentSystem, VanillaVM.System.toMultiStep,
      MultiStep.System.ASEmbed, MultiStep.System.REmbed, embedVerify]
      using hverify

/-! ## One accepted proof and the main theorem -/

private def segmentTrace : SegmentTrace exactVC where
  bus := segmentBus
  states := fun _ => committedState
  steps := fun _ => .other

private def segmentProof : SegmentProof where
  busCom := segmentBus
  stepProof := segmentTrace
  keccakProof := segmentBus
  poseidonProof := segmentBus
  rangeProof := segmentBus

private def combineProof : CombineProof where
  proofL := .inl segmentProof
  proofR := .inl segmentProof
  Smid := committedState
  NL := 1
  NR := 1

private theorem accepts_segment :
    segmentVerify ⟨committedState, committedState⟩ segmentProof := by
  simp [segmentVerify, segmentProof, innerStepVerify, segmentTrace,
    stepBusModel, innerKeccakVerify, innerPoseidonVerify, innerRangeVerify,
    segmentBus, hashCall, committedState, fullState]

private theorem accepts_final_proof :
    system.toZkVM.verify ⟨fullState, fullState⟩ combineProof := by
  change embedVerify ⟨committedState, committedState⟩ combineProof
  simp [embedVerify, combineVerify, combineProof, convertVerify, accepts_segment]

private theorem accepts_plain_step :
    system.toZkVM.step fullState fullState := by
  simp [VanillaVM.System.toZkVM, VanillaVM.System.toMultiStep,
    MultiStep.System.toZkVM, system, segmentSystem, ISA.System.stepPlain,
    ISA.System.operation, isa, memFree, fullState]

/-- The final assumptions, an accepted proof, and a valid plain transition
occur in the same concrete example. This guards against proving `cte_main` only
from contradictory hypotheses, an always-rejecting verifier, or an empty step
relation. -/
private theorem assumptions_and_accepted_proof :
    system.Assumptions ∧
      system.toZkVM.verify ⟨fullState, fullState⟩ combineProof ∧
      system.toZkVM.step fullState fullState :=
  ⟨assumptions, accepts_final_proof, accepts_plain_step⟩

private example : system.toZkVM.CTE :=
  system.cte_main assumptions

end VanillaVMSanity
end VanillaZkVM
