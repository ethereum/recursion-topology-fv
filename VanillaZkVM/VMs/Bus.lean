import VanillaZkVM.Preliminaries.ArgumentSystem
import VanillaZkVM.Preliminaries.HashCommitment
import VanillaZkVM.VMs.ISA

/-!
# Reusable segment-bus extraction

The segment trace does not check every expensive operation by itself. Instead,
it records hash calls and range-check inputs in a bus. Three separate chip
proofs check the Keccak, Poseidon, and range-check parts of that bus. The segment
proof verifies those chip proofs together with the segment-trace proof under one
public bus commitment.

The paper calls the four smaller proofs “inner proofs” because one segment
proof verifies all four of them. The step proof checks the segment's state
transitions; the other three proofs check the Keccak, Poseidon, and range-check
entries recorded in the segment's bus.

## Main definitions
* `SegmentBus` — the Keccak calls, Poseidon calls, and range-check inputs from
  one segment.
* `System.stepBus` and `System.stepWithBus` — the committed-state step before
  and after the three bus checks are included.
* `System.RSegment` — the segment relation that verifies the four inner proofs
  under one bus commitment.

## Main results
* `System.stepWithBus_committedOperation` — a bus-checked transition satisfies
  the existing committed ISA operation with the same memory witness.
* `System.segment_extract` — an accepted segment proof yields a valid segment
  trace in which the step, Keccak, Poseidon, and range-check proofs use the same
  bus.

This file does not choose how segment proofs are combined into a final proof.

Paper: bus layout in ch02; `eq:step-expanded`, `eq:step-bus2`,
`eq:rel-inner-step`, the three inner-chip relations, `R_1`, and `lem:segment`.
-/

namespace VanillaZkVM
namespace Bus

/-! ## Data recorded in one segment's bus -/

/-- The program counter and registers of a VM state, omitting memory.

Bus entries for hash and range operations do not need to duplicate memory:
these operations are required separately to leave the memory commitment
unchanged. `BusState` stores exactly the data their chip predicates inspect.

Paper: the state data in the bus entries of ch03. -/
structure BusState where
  pc : Word
  regs : ℕ → Word

/-- Remove the memory field from a VM state before placing it in the bus. -/
def BusState.ofState {Mem : Type} (S : VMStateWith Mem) : BusState :=
  ⟨S.pc, S.regs⟩

/-- One hash-precompile call, represented by its input and output register
states. Whether it is Keccak or Poseidon is determined by the fixed program and
stored in the corresponding list of `SegmentBus`.

Paper: `(op, S₁, S₂)` precompile entries in the bus definition in ch03. -/
structure HashCall where
  input : BusState
  output : BusState

/-- The hash call made by a transition between two VM states. -/
def HashCall.ofStates {Mem₁ Mem₂ : Type} (S₁ : VMStateWith Mem₁)
    (S₂ : VMStateWith Mem₂) : HashCall :=
  ⟨BusState.ofState S₁, BusState.ofState S₂⟩

/-- The bus belonging to one execution segment.

The paper writes these entries as one mixed collection. Lean uses three lists
so that a Keccak proof receives only Keccak calls, a Poseidon proof receives
only Poseidon calls, and the range proof receives only range-check inputs. The
bus commitment still covers all three lists together.

The paper leaves the concrete collection representation unspecified. Here,
list order and duplicate entries are part of the committed bus value, while the
chip predicates below use list membership and therefore check every occurrence
the same way.

Every hash or range-checked transition must place its required entry in these
lists, and every stored entry must pass the corresponding chip check. The
relation does not require the lists to contain each call exactly once, so an
additional valid entry or duplicate is allowed. This is the same deliberate
strengthening discussed after `eq:step-expanded`.

Paper: the bus definition in ch03. -/
structure SegmentBus where
  keccakCalls : List HashCall
  poseidonCalls : List HashCall
  rangeChecks : List BusState

/-- The two hash checks represented by the ISA's single `hash` operation
class. The fixed program says which one applies at each program counter.

This is the Issue 3 five-class simplification of the separate Keccak and
Poseidon operations in ch03.

Paper: the Keccak and Poseidon branches of `eq:step-expanded` and
`eq:step-bus2` (ch03). -/
inductive HashChip where
  | keccak
  | poseidon
  deriving DecidableEq, Repr

/-- Information kept for one transition after extracting a segment proof: the
segment's bus and the `MemStep` used to check this transition. Every transition
inside one extracted segment uses the same `bus`; different segments may use
different buses.

Paper: the bus and `πᵐᵉᵐ_i` output by `lem:segment`. -/
structure StepAux (VC : VectorCommitment) where
  bus : SegmentBus
  memory : MemStep VC

/-! ## Inner and segment statements -/

/-- Public statement of one bus-backed segment: its committed input and output
states.

This type belongs to the reusable bus layer. Concrete systems map their own
first-layer statements to it; for example, the two-layer connection maps its
segment boundary statement to these two fields.

Paper: statement of `R_1` in ch04. -/
structure SegmentStmt (VC : VectorCommitment) where
  Sin : CommittedVMState VC
  Sout : CommittedVMState VC

/-- Public input of the inner segment-trace proof: the two committed boundary
states and the commitment to the segment bus.

Paper: public input of `R_{0,step}` in `eq:rel-inner-step` (ch04). -/
structure InnerStepStmt (VC : VectorCommitment) (Digest : Type) where
  Sin : CommittedVMState VC
  Sout : CommittedVMState VC
  busCom : Digest

/-- Data recovered from the inner segment-trace proof: one bus, the committed
states, and one memory witness for every transition.

Paper: witness of `R_{0,step}` in `eq:rel-inner-step` (ch04). -/
structure SegmentTrace (VC : VectorCommitment) where
  bus : SegmentBus
  states : ℕ → CommittedVMState VC
  steps : ℕ → MemStep VC

/-- Witness of the segment circuit `R_1`: a common bus commitment and the four
inner proofs checked under it.

Paper: witness of `R_1` (ch04). -/
structure SegmentWitness (Digest InnerStepProof InnerKeccakProof
    InnerPoseidonProof InnerRangeProof : Type) where
  busCom : Digest
  stepProof : InnerStepProof
  keccakProof : InnerKeccakProof
  poseidonProof : InnerPoseidonProof
  rangeProof : InnerRangeProof

/-! ## Parameters of the segment bus proof system -/

/-- The proof system for one bus-backed segment.

`VC`, `Nseg`, and `isa` specify the committed state type, segment length, and
fixed program. The remaining fields give the bus commitment and the proof types
and verifiers for the segment proof and its four inner proofs. Nothing here
chooses how segment proofs are combined into a complete execution.

The representative ISA has one `hash` class and one `bin` class. `hashChipAt`
states whether a hash instruction at a given program counter uses Keccak or
Poseidon. `binInlinePred` and `rangePred` state the two parts of a range-checked
binary operation. `binDecomposition` requires those parts together to mean
exactly the already-defined `ISA.System.memFreePred .bin`. In other words, it
records how the fixed ISA divides a binary operation between the step proof and
the range proof; it is not a cryptographic assumption.

Paper: operation split in `eq:step-expanded` (ch03) and the proof systems for
`R_{0,*}` and `R_1` (ch04). -/
structure System where
  VC : VectorCommitment
  Nseg : ℕ
  isa : ISA.System VC.Index VC.Value
  BusDigest : Type
  busHash : SegmentBus → BusDigest
  hashChipAt : Word → HashChip
  binInlinePred : MemFreePredicate
  rangePred : Word → (ℕ → Word) → Prop
  binDecomposition : ∀ pc₁ regs₁ pc₂ regs₂,
    isa.memFreePred .bin pc₁ regs₁ pc₂ regs₂ ↔
      binInlinePred pc₁ regs₁ pc₂ regs₂ ∧ rangePred pc₁ regs₁
  SegmentProof : Type
  segmentVerify : SegmentStmt VC → SegmentProof → Prop
  InnerStepProof : Type
  innerStepVerify : InnerStepStmt VC BusDigest → InnerStepProof → Prop
  InnerKeccakProof : Type
  innerKeccakVerify : BusDigest → InnerKeccakProof → Prop
  InnerPoseidonProof : Type
  innerPoseidonVerify : BusDigest → InnerPoseidonProof → Prop
  InnerRangeProof : Type
  innerRangeVerify : BusDigest → InnerRangeProof → Prop

namespace System

variable (sys : System)

/-- The commitment used for the complete segment bus. It uses the bus type and
hash function stored in `System`, so the collision-resistance assumption below
refers to exactly the same function as the four proof statements.

Paper: `Com_bus` and `def:bus-cr`. -/
def busCommitment : HashCommitment where
  Domain := SegmentBus
  Digest := sys.BusDigest
  hash := sys.busHash

/-! ## The predicates checked by the segment trace and chips -/

/-- Every Keccak call recorded in the bus is a hash instruction assigned to the
Keccak chip by the fixed program, and it satisfies the ISA's register predicate
for a hash operation. Memory equality is checked by `stepBus`, where the
complete committed states are available.

Paper: `φ_keccak(B)` in ch03. -/
def keccakChip (bus : SegmentBus) : Prop :=
  ∀ call, call ∈ bus.keccakCalls →
    sys.isa.code call.input.pc = .hash ∧
    sys.hashChipAt call.input.pc = .keccak ∧
    sys.isa.memFreePred .hash
      call.input.pc call.input.regs call.output.pc call.output.regs

/-- Every Poseidon call recorded in the bus is a hash instruction assigned to
the Poseidon chip by the fixed program, and it satisfies the ISA's register
predicate for a hash operation.

Paper: `φ_poseidon(B)` in ch03. -/
def poseidonChip (bus : SegmentBus) : Prop :=
  ∀ call, call ∈ bus.poseidonCalls →
    sys.isa.code call.input.pc = .hash ∧
    sys.hashChipAt call.input.pc = .poseidon ∧
    sys.isa.memFreePred .hash
      call.input.pc call.input.regs call.output.pc call.output.regs

/-- Every range-check entry recorded in the bus satisfies the range condition
specified by the fixed ISA.

Paper: `φ_range(B)` in ch03. -/
def rangeChip (bus : SegmentBus) : Prop :=
  ∀ state, state ∈ bus.rangeChecks → sys.rangePred state.pc state.regs

/-- The committed transition predicate checked by the inner segment-trace
circuit before the chip proofs are added.

* reads, writes, and ordinary arithmetic use the existing
  `ISA.System.committedOperation` predicate;
* a hash step must preserve committed memory and record its input/output in the
  Keccak or Poseidon list selected by the fixed program;
* a binary/range-checked step checks its ordinary register update inline,
  preserves memory, and records its input register state for the range chip.

The memory witness is explicit because read and write openings must remain
available to the later memory-reconstruction proof.

Paper: `φ̂_step,bus` in `eq:step-bus2` (ch03), under the five-class ISA
simplification recorded in `docs/CORRESPONDENCE.md`. -/
def stepBus (Ŝ₁ Ŝ₂ : CommittedVMState sys.VC)
    (w : MemStep sys.VC) (bus : SegmentBus) : Prop :=
  match sys.isa.code Ŝ₁.pc with
  | .read => sys.isa.committedOperation Ŝ₁ Ŝ₂ w
  | .write => sys.isa.committedOperation Ŝ₁ Ŝ₂ w
  | .arith => sys.isa.committedOperation Ŝ₁ Ŝ₂ w
  | .hash =>
      w = .other ∧ Ŝ₂.mem = Ŝ₁.mem ∧
        match sys.hashChipAt Ŝ₁.pc with
        | .keccak => HashCall.ofStates Ŝ₁ Ŝ₂ ∈ bus.keccakCalls
        | .poseidon => HashCall.ofStates Ŝ₁ Ŝ₂ ∈ bus.poseidonCalls
  | .bin =>
      w = .other ∧
      sys.binInlinePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧
      Ŝ₂.mem = Ŝ₁.mem ∧ BusState.ofState Ŝ₁ ∈ bus.rangeChecks

/-- The complete committed step after the three chip predicates have been
checked on the same bus. `StepAux.memory` supplies the opening used by a memory
operation, and `StepAux.bus` supplies the one bus shared by the segment.

Paper: `φ̂_step` in `eq:step-bus2` (ch03). -/
def stepWithBus (Ŝ₁ Ŝ₂ : CommittedVMState sys.VC)
    (aux : StepAux sys.VC) : Prop :=
  sys.stepBus Ŝ₁ Ŝ₂ aux.memory aux.bus ∧
  sys.keccakChip aux.bus ∧ sys.poseidonChip aux.bus ∧ sys.rangeChip aux.bus

/-- Once all three chip predicates hold on the bus used by a transition, the
transition satisfies the existing committed ISA relation.

For a hash call, membership in the selected hash list lets the corresponding
chip predicate prove `memFreePred .hash`. For a range-checked binary operation,
membership in the range list proves `rangePred`, which combines with the inline
part through `binDecomposition`. The other operation classes were already
checked completely by `stepBus`.

The conclusion preserves `aux.memory`, rather than merely proving that some
memory witness exists. This lets the first extractor in a recursive proof
retain the exact read/write opening recovered from the segment proof. It also
implies the committed-step predicate between the two states required by
`StepInterface.BusBridge`. A concrete VM can obtain that weaker statement by
saying that `aux.memory` is the memory witness whose existence the interface
requires.

Paper: the implication from `eq:step-bus2` to the committed operation
predicate used by `lem:segment` and `prop:memory-extractability`. -/
theorem stepWithBus_committedOperation :
    ∀ Ŝ₁ Ŝ₂ aux, sys.stepWithBus Ŝ₁ Ŝ₂ aux →
      sys.isa.committedOperation Ŝ₁ Ŝ₂ aux.memory := by
  rintro Ŝ₁ Ŝ₂ ⟨bus, w⟩ ⟨hstep, hkeccak, hposeidon, hrange⟩
  unfold stepBus at hstep
  cases hcode : sys.isa.code Ŝ₁.pc
  case read =>
    rw [hcode] at hstep
    exact hstep
  case write =>
    rw [hcode] at hstep
    exact hstep
  case arith =>
    rw [hcode] at hstep
    exact hstep
  case hash =>
    rw [hcode] at hstep
    obtain ⟨hw, hmem, hcall⟩ := hstep
    change w = .other at hw
    subst w
    have hregisters : sys.isa.memFreePred .hash
        Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs := by
      cases hchip : sys.hashChipAt Ŝ₁.pc
      · rw [hchip] at hcall
        exact (hkeccak (HashCall.ofStates Ŝ₁ Ŝ₂) hcall).2.2
      · rw [hchip] at hcall
        exact (hposeidon (HashCall.ofStates Ŝ₁ Ŝ₂) hcall).2.2
    refine ⟨?_, Or.inr (Or.inl hcode)⟩
    simp only [CommittedMemory.step]
    simpa [ISA.System.selectedMemFreePred, hcode] using And.intro hregisters hmem.symm
  case bin =>
    rw [hcode] at hstep
    obtain ⟨hw, hinline, hmem, hentry⟩ := hstep
    change w = .other at hw
    subst w
    have hrangeAt : sys.rangePred Ŝ₁.pc Ŝ₁.regs :=
      hrange (BusState.ofState Ŝ₁) hentry
    have hregisters : sys.isa.memFreePred .bin
        Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs :=
      (sys.binDecomposition Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs).2 ⟨hinline, hrangeAt⟩
    refine ⟨?_, Or.inr (Or.inr hcode)⟩
    simp only [CommittedMemory.step]
    simpa [ISA.System.selectedMemFreePred, hcode] using And.intro hregisters hmem.symm

/-! ## The four inner relations and the segment relation -/

/-- `R_{0,step}`: an `Nseg`-transition committed trace. Hash and range checks
are recorded in one bus, and that bus hashes to the digest in the public
statement.

Paper: `eq:rel-inner-step` (ch04). -/
def RInnerStep : Relation where
  Stmt := InnerStepStmt sys.VC sys.BusDigest
  Wit := SegmentTrace sys.VC
  rel := fun st w =>
    w.states 0 = st.Sin ∧
    w.states sys.Nseg = st.Sout ∧
    (∀ j, j < sys.Nseg →
      sys.stepBus (w.states j) (w.states (j + 1)) (w.steps j) w.bus) ∧
    st.busCom = sys.busHash w.bus

/-- The inner segment-trace argument system `Π_{0,step}`.

Paper: the argument system for `R_{0,step}` in ch04. -/
def ASInnerStep : ArgumentSystem sys.RInnerStep where
  Proof := sys.InnerStepProof
  verify := sys.innerStepVerify

/-- Shared Lean definition for the three inner chip relations: the recovered
bus passes the selected chip check and hashes to the digest in the public
statement. The three named relations below correspond to the paper. -/
def RInnerChip (pred : SegmentBus → Prop) : Relation where
  Stmt := sys.BusDigest
  Wit := SegmentBus
  rel := fun busCom bus => pred bus ∧ busCom = sys.busHash bus

/-- `R_{0,keccak}`: all Keccak entries in the committed bus are correct.

Paper: `eq:rel-inner-keccak` (ch04). -/
def RInnerKeccak : Relation := sys.RInnerChip sys.keccakChip

/-- `R_{0,poseidon}`: all Poseidon entries in the committed bus are correct.

Paper: `eq:rel-inner-poseidon` (ch04). -/
def RInnerPoseidon : Relation := sys.RInnerChip sys.poseidonChip

/-- `R_{0,range}`: all range-check entries in the committed bus are correct.

Paper: `eq:rel-inner-range` (ch04). -/
def RInnerRange : Relation := sys.RInnerChip sys.rangeChip

/-- The inner Keccak argument system `Π_{0,keccak}`.

Paper: the argument system for `R_{0,keccak}` in ch04. -/
def ASInnerKeccak : ArgumentSystem sys.RInnerKeccak where
  Proof := sys.InnerKeccakProof
  verify := sys.innerKeccakVerify

/-- The inner Poseidon argument system `Π_{0,poseidon}`.

Paper: the argument system for `R_{0,poseidon}` in ch04. -/
def ASInnerPoseidon : ArgumentSystem sys.RInnerPoseidon where
  Proof := sys.InnerPoseidonProof
  verify := sys.innerPoseidonVerify

/-- The inner range-check argument system `Π_{0,range}`.

Paper: the argument system for `R_{0,range}` in ch04. -/
def ASInnerRange : ArgumentSystem sys.RInnerRange where
  Proof := sys.InnerRangeProof
  verify := sys.innerRangeVerify

/-- `R_1`, the segment relation. Its witness contains one bus commitment and
four proofs; all four verifiers receive that same commitment. The buses are not
part of this witness: they are recovered later from the four proofs.
`segment_extract` uses collision resistance to prove that those four recovered
buses are equal.

Paper: `R_1` (ch04). -/
def RSegment : Relation where
  Stmt := SegmentStmt sys.VC
  Wit := SegmentWitness sys.BusDigest sys.InnerStepProof sys.InnerKeccakProof
    sys.InnerPoseidonProof sys.InnerRangeProof
  rel := fun st w =>
    sys.innerStepVerify ⟨st.Sin, st.Sout, w.busCom⟩ w.stepProof ∧
    sys.innerKeccakVerify w.busCom w.keccakProof ∧
    sys.innerPoseidonVerify w.busCom w.poseidonProof ∧
    sys.innerRangeVerify w.busCom w.rangeProof

/-- The segment argument system `Π_1`. `RSegment` specifies the witness that
knowledge soundness of the configured segment verifier must recover.

Paper: the argument system for `R_1` in ch04. -/
def ASSegment : ArgumentSystem sys.RSegment where
  Proof := sys.SegmentProof
  verify := sys.segmentVerify

/-! ## Extraction assumptions and one-segment result -/

/-- The facts assumed by the segment extraction theorem but not proved in this file:
knowledge soundness of the segment proof and its four inner proofs, together
with collision resistance of the bus commitment. Listing them in one structure
makes every cryptographic assumption used by `segment_extract` visible at the
theorem call site. Assumptions about how segment proofs are later combined or
verified belong to the concrete VM that consumes this segment layer.

Paper: assumptions of `lem:segment`. -/
structure Assumptions (sys : System) : Prop where
  collisionResistant : CollisionResistant sys.busCommitment
  innerStepSound : KnowledgeSound sys.ASInnerStep
  innerKeccakSound : KnowledgeSound sys.ASInnerKeccak
  innerPoseidonSound : KnowledgeSound sys.ASInnerPoseidon
  innerRangeSound : KnowledgeSound sys.ASInnerRange
  segmentSound : KnowledgeSound sys.ASSegment

/-- A recovered segment trace is valid when it has the claimed endpoints and
every transition passes `stepWithBus` with the segment's one bus and its own
memory witness.

This definition permits two recovered segments to contain different buses.
It requires only that every transition inside a particular segment uses that
segment's bus.

Paper: winning condition of `lem:segment`. -/
def segmentValid (st : SegmentStmt sys.VC)
    (tr : SegmentTrace sys.VC) : Prop :=
  tr.states 0 = st.Sin ∧
  tr.states sys.Nseg = st.Sout ∧
  ∀ j, j < sys.Nseg →
    sys.stepWithBus (tr.states j) (tr.states (j + 1)) ⟨tr.bus, tr.steps j⟩

/-- **One-segment extraction (`lem:segment`).** From any accepted segment
proof, recover the segment trace and its bus. The four proof extractors may
initially return different buses, but each bus hashes to the digest in the
segment witness. Collision resistance proves that the three chip buses equal
the segment-trace bus, so all chip checks apply to that one bus.

The result retains the bus and memory witness of every transition. It does not
compare this bus with the bus of any other segment.

Paper: `lem:segment` (ch05), in the perfect collision-resistance model required
by `docs/INVARIANTS.md` I8. -/
theorem segment_extract (h : sys.Assumptions) :
    ∃ E : SegmentStmt sys.VC → sys.SegmentProof → SegmentTrace sys.VC,
      ∀ (x : SegmentStmt sys.VC) (p : sys.SegmentProof),
        sys.segmentVerify x p → sys.segmentValid x (E x p) := by
  obtain ⟨hcr, hstepSound, hkeccakSound, hposeidonSound, hrangeSound,
    hsegmentSound⟩ := h
  obtain ⟨Esegment, hEsegment⟩ := hsegmentSound
  obtain ⟨Estep, hEstep⟩ := hstepSound
  obtain ⟨Ekeccak, hEkeccak⟩ := hkeccakSound
  obtain ⟨Eposeidon, hEposeidon⟩ := hposeidonSound
  obtain ⟨Erange, hErange⟩ := hrangeSound
  refine ⟨fun x p =>
      let w := Esegment.extract x p
      Estep.extract ⟨x.Sin, x.Sout, w.busCom⟩ w.stepProof, ?_⟩
  intro x p hp
  let w := Esegment.extract x p
  have hw : sys.RSegment.rel x w := hEsegment x p hp
  obtain ⟨hstepVerify, hkeccakVerify, hposeidonVerify, hrangeVerify⟩ := hw
  let stepTrace := Estep.extract ⟨x.Sin, x.Sout, w.busCom⟩ w.stepProof
  let keccakBus := Ekeccak.extract w.busCom w.keccakProof
  let poseidonBus := Eposeidon.extract w.busCom w.poseidonProof
  let rangeBus := Erange.extract w.busCom w.rangeProof
  have hstepRel : sys.RInnerStep.rel ⟨x.Sin, x.Sout, w.busCom⟩ stepTrace :=
    hEstep _ _ hstepVerify
  have hkeccakRel : sys.RInnerKeccak.rel w.busCom keccakBus :=
    hEkeccak _ _ hkeccakVerify
  have hposeidonRel : sys.RInnerPoseidon.rel w.busCom poseidonBus :=
    hEposeidon _ _ hposeidonVerify
  have hrangeRel : sys.RInnerRange.rel w.busCom rangeBus :=
    hErange _ _ hrangeVerify
  obtain ⟨hstart, hend, hsteps, hstepHash⟩ := hstepRel
  obtain ⟨hkeccakChip, hkeccakHash⟩ := hkeccakRel
  obtain ⟨hposeidonChip, hposeidonHash⟩ := hposeidonRel
  obtain ⟨hrangeChip, hrangeHash⟩ := hrangeRel
  have hbusKeccak : stepTrace.bus = keccakBus :=
    hcr stepTrace.bus keccakBus (hstepHash.symm.trans hkeccakHash)
  have hbusPoseidon : stepTrace.bus = poseidonBus :=
    hcr stepTrace.bus poseidonBus (hstepHash.symm.trans hposeidonHash)
  have hbusRange : stepTrace.bus = rangeBus :=
    hcr stepTrace.bus rangeBus (hstepHash.symm.trans hrangeHash)
  have hkeccakUnified : sys.keccakChip stepTrace.bus := by
    rw [hbusKeccak]
    exact hkeccakChip
  have hposeidonUnified : sys.poseidonChip stepTrace.bus := by
    rw [hbusPoseidon]
    exact hposeidonChip
  have hrangeUnified : sys.rangeChip stepTrace.bus := by
    rw [hbusRange]
    exact hrangeChip
  exact ⟨hstart, hend, fun j hj =>
    ⟨hsteps j hj, hkeccakUnified, hposeidonUnified, hrangeUnified⟩⟩

end System
end Bus
end VanillaZkVM
