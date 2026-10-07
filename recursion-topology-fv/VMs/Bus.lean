import «recursion-topology-fv».Preliminaries.ArgumentSystem
import «recursion-topology-fv».Preliminaries.HashCommitment
import «recursion-topology-fv».VMs.ISA

/-!
# An example bus and segment extraction

A *segment* is `Nseg` VM steps. Its *segment trace* is the list of its states. Some checks are expensive to do at each
step: hash calls, or binary operations requiring range-checks. So we record them in a *bus*, and three *chips* check
them separately:

```text
  segment trace            bus                 chips
   │ read, write, arith
   │ hash (Keccak)    ──→  keccakCalls    ──→  Keccak
   │ hash (Poseidon)  ──→  poseidonCalls  ──→  Poseidon
   │ bin              ──→  rangeChecks    ──→  range
   ▼
```

One segment has five proofs:

```text
              segment proof              verifies the four proofs below
   ┌────────┬───────┴──────┬──────────┐
  step    Keccak      Poseidon      range       inner proofs
  proof   proof       proof         proof
          └──────── chip proofs ────────┘
```

* The *step proof* (`RInnerStep`) checks each step. For a hash call or a range check, it checks
  that the bus has an entry, not that the entry is correct.
* Each *chip proof* (`RInnerKeccak`, `RInnerPoseidon`, `RInnerRange`) checks that all entries
  of one bus list are correct.
* The *segment proof* (`RSegment`) verifies the four *inner* proofs. "Inner" means "verified
  inside the segment proof".

The inner verifiers see only `busCom`, a hash of the bus. So extraction gives four buses, one
from each inner proof. Collision resistance of the hash makes them equal (`segment_extract`).

## Main definitions
* `SegmentBus` — the three lists of the bus.
* `System` — all parameters: the program, the bus hash, and the five verifiers.
* `System.stepBus` — one step, as the step proof checks it.
* `System.stepWithBus` — the same step, plus the three chip checks.

## Main results
* `System.stepWithBus_committedOperation` — a step that passes `stepWithBus` is a valid
  `ISA.System.committedOperation` step.
* `System.segment_extract` — from an accepted segment proof, we get a valid segment trace.

Paper: Fig. `img:segments` (ch02); `eq:step-bus2`, `eq:rel-inner-step`, `R_1`, `def:bus-cr`,
and `lem:segment`.
-/

namespace VanillaZkVM
namespace Bus

/-! ## Data recorded in one segment's bus -/

/-- The program counter and registers of a VM state.

Paper: the state data in the bus entries of ch03. -/
structure BusState where
  /-- The program counter. -/
  pc : Word
  /-- The registers. -/
  regs : ℕ → Word

/-- Remove the memory field from a VM state before placing it in the bus. -/
def BusState.ofState {Mem : Type} (S : VMStateWith Mem) : BusState :=
  ⟨S.pc, S.regs⟩

/-- One hash-precompile call. The list of `SegmentBus` that holds it tells if it is Keccak or
Poseidon.

Paper: `(op, S₁, S₂)` precompile entries in the bus definition in ch03. -/
structure HashCall where
  /-- The state before the call. -/
  input : BusState
  /-- The state after the call. -/
  output : BusState

/-- The hash call made by a transition between two VM states. -/
def HashCall.ofStates {Mem₁ Mem₂ : Type} (S₁ : VMStateWith Mem₁)
    (S₂ : VMStateWith Mem₂) : HashCall :=
  ⟨BusState.ofState S₁, BusState.ofState S₂⟩

/-- The bus of one segment.

Paper: the bus definition in ch03. -/
structure SegmentBus where
  keccakCalls : List HashCall
  poseidonCalls : List HashCall
  rangeChecks : List BusState

/-- The two hash checks represented by the ISA's single `hash` operation
class. The fixed program says which one applies at each program counter.

Paper: the Keccak and Poseidon branches of `eq:step-expanded` and
`eq:step-bus2` (ch03). -/
inductive HashChip where
  | keccak
  | poseidon
  deriving DecidableEq, Repr

/-- Data kept for one transition after a segment proof is extracted.

Paper: the bus and `πᵐᵉᵐ_i` output by `lem:segment`. -/
structure StepAux (VC : VectorCommitment) where
  /-- The bus of the segment. All transitions in one segment use the same bus. -/
  bus : SegmentBus
  /-- The memory witness that checks this transition. -/
  memory : MemStep VC

/-! ## Inner and segment statements -/

/-- Public statement of one bus-backed segment. Concrete systems map their own segment
statements to this type.

Paper: statement of `R_1` in ch04. -/
structure SegmentStmt (VC : VectorCommitment) where
  /-- The committed input state. -/
  Sin : CommittedVMState VC
  /-- The committed output state. -/
  Sout : CommittedVMState VC

/-- Public input of the inner step proof.

Paper: public input of `R_{0,step}` in `eq:rel-inner-step` (ch04). -/
structure InnerStepStmt (VC : VectorCommitment) (Digest : Type) where
  /-- The committed input state. -/
  Sin : CommittedVMState VC
  /-- The committed output state. -/
  Sout : CommittedVMState VC
  /-- The commitment to the segment bus. -/
  busCom : Digest

/-- Data recovered from the inner step proof.

Paper: witness of `R_{0,step}` in `eq:rel-inner-step` (ch04). -/
structure SegmentTrace (VC : VectorCommitment) where
  /-- The one bus of the segment. -/
  bus : SegmentBus
  /-- The committed states. -/
  states : ℕ → CommittedVMState VC
  /-- The memory witness of each transition. -/
  steps : ℕ → MemStep VC

/-- Witness of the segment circuit `R_1`.

Paper: witness of `R_1` (ch04). -/
structure SegmentWitness (Digest InnerStepProof InnerKeccakProof
    InnerPoseidonProof InnerRangeProof : Type) where
  /-- The bus commitment. All four inner proofs are checked against it. -/
  busCom : Digest
  /-- The inner step proof. -/
  stepProof : InnerStepProof
  /-- The inner Keccak proof. -/
  keccakProof : InnerKeccakProof
  /-- The inner Poseidon proof. -/
  poseidonProof : InnerPoseidonProof
  /-- The inner range proof. -/
  rangeProof : InnerRangeProof

/-! ## Parameters of the segment bus proof system -/

/-- The proof system for one bus-backed segment. It does not say how segment proofs are combined.

Paper: operation split in `eq:step-expanded` (ch03) and the proof systems for
`R_{0,*}` and `R_1` (ch04). -/
structure System where
  /-- The vector commitment for memory. -/
  VC : VectorCommitment
  /-- The number of steps in one segment. -/
  Nseg : ℕ
  /-- The fixed program. -/
  isa : ISA.System VC.Index VC.Value
  /-- The type of bus commitments. -/
  BusDigest : Type
  /-- The hash that commits to a bus. -/
  busHash : SegmentBus → BusDigest
  /-- Tells if the `hash` instruction at a program counter uses Keccak or Poseidon. -/
  hashChipAt : Word → HashChip
  /-- The part of a `bin` operation that the step proof checks. -/
  binInlinePred : MemFreePredicate
  /-- The part of a `bin` operation that the range proof checks. -/
  rangePred : Word → (ℕ → Word) → Prop
  /-- The two parts together mean exactly `isa.memFreePred .bin`. This is a fact about the
  fixed ISA, not a cryptographic assumption. -/
  binDecomposition : ∀ pc₁ regs₁ pc₂ regs₂,
    isa.memFreePred .bin pc₁ regs₁ pc₂ regs₂ ↔
      binInlinePred pc₁ regs₁ pc₂ regs₂ ∧ rangePred pc₁ regs₁
  /-- The segment proof. -/
  SegmentProof : Type
  /-- The segment verifier. -/
  segmentVerify : SegmentStmt VC → SegmentProof → Prop
  /-- The inner step proof. -/
  InnerStepProof : Type
  /-- The inner step verifier. -/
  innerStepVerify : InnerStepStmt VC BusDigest → InnerStepProof → Prop
  /-- The inner Keccak proof. -/
  InnerKeccakProof : Type
  /-- The inner Keccak verifier. -/
  innerKeccakVerify : BusDigest → InnerKeccakProof → Prop
  /-- The inner Poseidon proof. -/
  InnerPoseidonProof : Type
  /-- The inner Poseidon verifier. -/
  innerPoseidonVerify : BusDigest → InnerPoseidonProof → Prop
  /-- The inner range proof. -/
  InnerRangeProof : Type
  /-- The inner range verifier. -/
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

/-- The committed transition predicate checked by the inner step proof
before the chip proofs are added.

* reads, writes, and ordinary arithmetic use the existing
  `ISA.System.committedOperation` predicate;
* a hash step must preserve committed memory and record its input/output in the
  Keccak or Poseidon list selected by the fixed program;
* a binary/range-checked step checks its ordinary register update inline,
  preserves memory, and records its input register state for the range chip.

The memory witness is explicit because read and write openings must remain
available to the later memory-reconstruction proof.

Paper: `φ̂_step,bus` in `eq:step-bus2` (ch03), under the five-class ISA
simplification. -/
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
retain the exact read/write opening recovered from the segment proof. With
`aux.memory` as the witness, it also gives `ISA.System.committedStep` between
the two states.

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

/-- The inner step argument system `Π_{0,step}`.

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

/-- The cryptographic assumptions of `segment_extract`, in one place so that the call site
shows all of them.

Paper: assumptions of `lem:segment`. -/
structure Assumptions (sys : System) : Prop where
  /-- The bus commitment is collision resistant. -/
  collisionResistant : CollisionResistant sys.busCommitment
  /-- The inner step proof is knowledge sound. -/
  innerStepSound : KnowledgeSound sys.ASInnerStep
  /-- The inner Keccak proof is knowledge sound. -/
  innerKeccakSound : KnowledgeSound sys.ASInnerKeccak
  /-- The inner Poseidon proof is knowledge sound. -/
  innerPoseidonSound : KnowledgeSound sys.ASInnerPoseidon
  /-- The inner range proof is knowledge sound. -/
  innerRangeSound : KnowledgeSound sys.ASInnerRange
  /-- The segment proof is knowledge sound. -/
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
the bus of the step proof, so all chip checks apply to that one bus.

The result retains the bus and memory witness of every transition. It does not
compare this bus with the bus of any other segment.

Paper: `lem:segment` (ch05), with perfect (probability-free) collision
resistance. -/
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
