import VanillaZkVM.VMs.MemorySanity
import VanillaZkVM.VMs.TwoStep.WithBus

/-!
# Consistency checks for the segment bus and its two-layer connection

This file constructs a small system in which all assumptions of the reusable
one-segment theorem and the two-layer CTE theorem hold. An accepted final proof
contains two one-step segments. Both execute the same Keccak call, but the
second segment's bus contains a harmless duplicate, so the two buses are
visibly different.

The bus commitment is the identity function. Each proof value directly
contains the witness returned by its extractor. These deliberately simple
choices show that the assumptions can hold together and that an accepted
execution exists; they do not model a deployed hash or SNARK.

All declarations are private, so this file adds no public API.

## Main checks
* `segmentAssumptions` and `assumptions` — the one-segment and complete
  two-layer sets of assumptions can hold at the same time.
* `accepts_proof_with_different_buses` — one accepted final proof uses unequal
  buses in its two segments.
* `accepts_poseidon_transition` and `accepts_range_checked_transition` — the
  other bus lists support their intended transitions.
* `rejects_keccak_call_in_poseidon_chip`, `rejects_missing_hash_call`, and
  `rejects_missing_range_entry` — chip selection and required entries affect
  acceptance.
* The final private example instantiates the complete CTE theorem.
-/

namespace VanillaZkVM
namespace BusTwoStepSanity

open Bus

/-! ## A fixed hash program and exact memory commitment -/

private def memFree : MemFreePredicate := fun _ _ _ _ => True

private def isa : ISA.System MemorySanity.exactVC.Index MemorySanity.exactVC.Value where
  code := fun _ => .hash
  memFreePred := fun _ => memFree
  indexOfWord := fun word => decide (word ≠ 0)
  valueOfWord := fun word => decide (word ≠ 0)

private def fullState : FullVMState MemorySanity.exactVC :=
  ⟨0, fun _ => 0, fun _ => false⟩

private def committedState : CommittedVMState MemorySanity.exactVC :=
  ⟨fullState.pc, fullState.regs, MemorySanity.exactVC.commit fullState.mem⟩

private def hashCall : HashCall :=
  HashCall.ofStates committedState committedState

private def firstBus : SegmentBus :=
  ⟨[hashCall], [], []⟩

private def secondBus : SegmentBus :=
  ⟨[hashCall, hashCall], [], []⟩

private theorem segment_buses_are_different : firstBus ≠ secondBus := by
  intro h
  have hlength := congrArg (fun bus : SegmentBus => bus.keccakCalls.length) h
  simp [firstBus, secondBus] at hlength

/-! ## Verifiers whose proofs directly contain their witnesses -/

private def stepBusModel (S₁ S₂ : CommittedVMState MemorySanity.exactVC)
    (w : MemStep MemorySanity.exactVC) (bus : SegmentBus) : Prop :=
  w = .other ∧ S₂.mem = S₁.mem ∧ HashCall.ofStates S₁ S₂ ∈ bus.keccakCalls

private def innerStepVerify
    (statement : InnerStepStmt MemorySanity.exactVC SegmentBus)
    (trace : SegmentTrace MemorySanity.exactVC) : Prop :=
  trace.states 0 = statement.Sin ∧
  trace.states 1 = statement.Sout ∧
  (∀ j, j < 1 →
    stepBusModel (trace.states j) (trace.states (j + 1)) (trace.steps j) trace.bus) ∧
  statement.busCom = trace.bus

private def innerKeccakVerify (digest : SegmentBus) (bus : SegmentBus) : Prop :=
  digest = bus

private def innerPoseidonVerify (digest : SegmentBus) (bus : SegmentBus) : Prop :=
  (∀ call, call ∉ bus.poseidonCalls) ∧ digest = bus

private def innerRangeVerify (digest : SegmentBus) (bus : SegmentBus) : Prop :=
  digest = bus

private abbrev SegmentProof :=
  SegmentWitness SegmentBus (SegmentTrace MemorySanity.exactVC)
    SegmentBus SegmentBus SegmentBus

private def segmentVerify (statement : SegmentStmt MemorySanity.exactVC)
    (proof : SegmentProof) : Prop :=
  innerStepVerify ⟨statement.Sin, statement.Sout, proof.busCom⟩ proof.stepProof ∧
  innerKeccakVerify proof.busCom proof.keccakProof ∧
  innerPoseidonVerify proof.busCom proof.poseidonProof ∧
  innerRangeVerify proof.busCom proof.rangeProof

private def segmentSystem : Bus.System where
  VC := MemorySanity.exactVC
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
  InnerStepProof := SegmentTrace MemorySanity.exactVC
  innerStepVerify := innerStepVerify
  InnerKeccakProof := SegmentBus
  innerKeccakVerify := innerKeccakVerify
  InnerPoseidonProof := SegmentBus
  innerPoseidonVerify := innerPoseidonVerify
  InnerRangeProof := SegmentBus
  innerRangeVerify := innerRangeVerify

private def poseidonSegmentSystem : Bus.System :=
  { segmentSystem with hashChipAt := fun _ => .poseidon }

private def binISA : ISA.System MemorySanity.exactVC.Index MemorySanity.exactVC.Value where
  code := fun _ => .bin
  memFreePred := fun _ => memFree
  indexOfWord := fun word => decide (word ≠ 0)
  valueOfWord := fun word => decide (word ≠ 0)

private def binSegmentSystem : Bus.System :=
  { segmentSystem with
    isa := binISA
    binInlinePred := memFree
    rangePred := fun _ _ => True
    binDecomposition := by simp [binISA, memFree] }

/-! ## A final proof joining two segment proofs -/

private abbrev FinalProof := TwoStep.FinalWitness MemorySanity.exactVC SegmentProof

private def finalVerify (statement : TwoStep.FinalStmt MemorySanity.exactVC)
    (proof : FinalProof) : Prop :=
  proof.boundary 0 = statement.S0 ∧
  proof.boundary 2 = statement.ST ∧
  ∀ i, i < 2 →
    segmentVerify ⟨proof.boundary i, proof.boundary (i + 1)⟩ (proof.proofs i)

private def system : Bus.TwoStepSystem where
  segment := segmentSystem
  m := 2
  FinalProof := FinalProof
  finalVerify := finalVerify

/-! ## All assumptions hold together -/

private theorem segmentAssumptions : segmentSystem.Assumptions := by
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

private theorem assumptions : system.Assumptions := by
  refine ⟨segmentAssumptions, ?_, MemorySanity.exactVC_complete,
    MemorySanity.exactVC_positionBinding, MemorySanity.exactVC_updateBinding⟩
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [Bus.TwoStepSystem.toTwoStep, TwoStep.System.ASFinal,
      TwoStep.System.RFinal, system, segmentSystem, finalVerify,
      segmentVerify] using hverify

/-! ## An accepted two-segment execution with different buses -/

private def segmentTrace (bus : SegmentBus) : SegmentTrace MemorySanity.exactVC where
  bus := bus
  states := fun _ => committedState
  steps := fun _ => .other

private def segmentProof (bus : SegmentBus) : SegmentProof where
  busCom := bus
  stepProof := segmentTrace bus
  keccakProof := bus
  poseidonProof := bus
  rangeProof := bus

private def finalProof : FinalProof where
  boundary := fun _ => committedState
  proofs := fun i => if i = 0 then segmentProof firstBus else segmentProof secondBus

private theorem accepts_segment (bus : SegmentBus)
    (hcall : hashCall ∈ bus.keccakCalls)
    (hposeidon : ∀ call, call ∉ bus.poseidonCalls) :
    segmentVerify ⟨committedState, committedState⟩ (segmentProof bus) := by
  have hcall' : HashCall.ofStates committedState committedState ∈ bus.keccakCalls := by
    simpa [hashCall] using hcall
  simp [segmentVerify, segmentProof, innerStepVerify, segmentTrace,
    stepBusModel, innerKeccakVerify, innerPoseidonVerify, innerRangeVerify,
    hcall', hposeidon]

private theorem accepts_final_proof :
    system.toZkVM.verify ⟨fullState, fullState⟩ finalProof := by
  change finalVerify ⟨committedState, committedState⟩ finalProof
  refine ⟨rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  · simpa [finalProof] using
      accepts_segment firstBus (by simp [firstBus]) (by simp [firstBus])
  · simpa [finalProof] using
      accepts_segment secondBus (by simp [secondBus]) (by simp [secondBus])

/-- The accepted proof and unequal buses occur in the same model. No assumption
forces buses belonging to different segments to be equal. -/
private theorem accepts_proof_with_different_buses :
    system.toZkVM.verify ⟨fullState, fullState⟩ finalProof ∧
      firstBus ≠ secondBus :=
  ⟨accepts_final_proof, segment_buses_are_different⟩

/-! ## The Poseidon and range paths are usable -/

private def poseidonBus : SegmentBus :=
  ⟨[], [hashCall], []⟩

/-- A call assigned to Keccak by the fixed program cannot be checked as a
Poseidon call. -/
private theorem rejects_keccak_call_in_poseidon_chip :
    ¬segmentSystem.poseidonChip poseidonBus := by
  simp [Bus.System.poseidonChip, segmentSystem, isa, poseidonBus, hashCall]

private theorem accepts_poseidon_transition :
    poseidonSegmentSystem.stepWithBus committedState committedState
      ⟨poseidonBus, .other⟩ := by
  simp [Bus.System.stepWithBus, Bus.System.stepBus, Bus.System.keccakChip,
    Bus.System.poseidonChip, Bus.System.rangeChip, poseidonSegmentSystem,
    segmentSystem, isa, poseidonBus, hashCall, memFree]

private def rangeBus : SegmentBus :=
  ⟨[], [], [BusState.ofState committedState]⟩

private theorem accepts_range_checked_transition :
    binSegmentSystem.stepWithBus committedState committedState
      ⟨rangeBus, .other⟩ := by
  simp [Bus.System.stepWithBus, Bus.System.stepBus, Bus.System.keccakChip,
    Bus.System.poseidonChip, Bus.System.rangeChip, binSegmentSystem, binISA,
    segmentSystem, rangeBus, memFree]

/-- Removing the required Keccak call makes the hash transition fail. -/
private theorem rejects_missing_hash_call :
    ¬segmentSystem.stepBus committedState committedState .other ⟨[], [], []⟩ := by
  simp [Bus.System.stepBus, segmentSystem, isa]

/-- Removing the required range entry makes the binary transition fail. -/
private theorem rejects_missing_range_entry :
    ¬binSegmentSystem.stepBus committedState committedState .other ⟨[], [], []⟩ := by
  simp [Bus.System.stepBus, binSegmentSystem, binISA, segmentSystem, memFree]

private example : system.toZkVM.CTE := by
  exact system.cte (by simp [system, segmentSystem]) assumptions

end BusTwoStepSanity
end VanillaZkVM
