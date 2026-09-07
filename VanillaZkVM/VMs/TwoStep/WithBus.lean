import VanillaZkVM.VMs.Bus
import VanillaZkVM.VMs.TwoStep.TwoStep

/-!
# TwoStep VM with the reusable segment bus

This module connects `Bus.System.segment_extract` to the repository's
non-recursive two-layer VM. It is a small connection module, not part of the
reusable bus definition:
`VMs/Bus.lean` knows how to validate and extract one segment, while this file
shows how a final proof can join many such segments and reconstruct full
memory.

## Main definitions
* `TwoStepSystem` — one reusable bus system together with the final proof that
  joins `m` segment proofs.
* `TwoStepSystem.Execution` — the state trace, bus, and memory witnesses
  recovered separately for every segment.
* `TwoStepSystem.toZkVM` — the existing two-layer full-memory VM instantiated
  with the bus-backed segment verifier.

## Main results
* `TwoStepSystem.busBridge` — turns the reusable bus implication into the
  `StepInterface.BusBridge` statement required by this VM.
* `TwoStepSystem.execution_extract` — extracts every segment, retains its own
  bus, and concatenates the state traces.
* `TwoStepSystem.cte` — memory reconstruction turns the concatenated committed
  trace into a valid full-memory execution.

This file provides the Issue 5 `ZkVM`, whose segment proofs use the reusable
bus checks, without making those checks depend on `TwoStep`. The assembled
recursive VM in `VMs/VanillaVM/VanillaVM.lean` instead uses the same
`Bus.System` for its base segment proofs.

Paper: `lem:segment`, Steps 4--6 of `thm:main`, and `def:cte` (ch05),
specialized here to a non-recursive two-layer way of combining proofs.
-/

namespace VanillaZkVM
namespace Bus

/-! ## Connecting the bus system to the two-layer VM -/

/-- A reusable bus-backed segment proof together with a final proof that joins
`m` such segments.

`segment` contains only the one-segment bus definitions and verifiers. The
additional fields here are needed only by the non-recursive demonstration VM;
a recursive VM can consume `segment` without them.

Paper: the non-recursive specialization of the segment chaining in Steps 4--5 of
`thm:main` (ch05). -/
structure TwoStepSystem where
  segment : Bus.System
  m : ℕ
  FinalProof : Type
  finalVerify : TwoStep.FinalStmt segment.VC → FinalProof → Prop

namespace TwoStepSystem

variable (sys : TwoStepSystem)

/-- View this combined system as the existing two-layer system. Its segment verifier is
the reusable bus verifier after translating the identical pair of boundary
states into `Bus.SegmentStmt`.

Paper: the non-recursive two-layer specialization of `R_1` and the final
aggregation step in ch04. -/
def toTwoStep : TwoStep.System where
  VC := sys.segment.VC
  Nseg := sys.segment.Nseg
  m := sys.m
  isa := sys.segment.isa
  SegProof := sys.segment.SegmentProof
  segVerify := fun st p => sys.segment.segmentVerify ⟨st.Sin, st.Sout⟩ p
  FinalProof := sys.FinalProof
  finalVerify := sys.finalVerify

/-- The assumptions used by the non-recursive execution theorem: all
one-segment bus assumptions, knowledge soundness of the final proof that joins
the segment proofs, and the memory-commitment properties needed to reconstruct
the complete memory.

`sys.toTwoStep.Assumptions` is enough to extract an ordinary TwoStep trace, but
not enough for `execution_extract`: its segment extractor returns only states
and memory witnesses. `execution_extract` must also return each segment's bus,
which requires `sys.segment.Assumptions`.

Paper: `lem:segment` and the final-proof extraction in Steps 1--5 of
`thm:main`, restricted to the two-layer arrangement. -/
structure Assumptions (sys : TwoStepSystem) : Prop where
  /-- The assumptions needed to extract each accepted segment proof and check
  its bus. -/
  segment : sys.segment.Assumptions
  /-- An accepted final proof reveals the segment boundary states and proofs. -/
  finalSound : KnowledgeSound sys.toTwoStep.ASFinal
  /-- Openings produced from an honestly committed memory are accepted. -/
  complete : sys.segment.VC.Complete
  /-- One memory commitment cannot open to two values at the same address. -/
  positionBinding : sys.segment.VC.PositionBinding
  /-- A commitment accepted after a write represents the correctly updated
  memory. -/
  updateBinding : sys.segment.VC.UpdateBinding

/-- State the reusable bus result in the form required by this concrete VM.
`stepWithBus_committedOperation` retains a particular memory witness; this
theorem supplies that same value to prove that a suitable witness exists.

Paper: the implication from `eq:step-bus2` to the committed step used by
`lem:segment` and `prop:memory-extractability`. -/
theorem busBridge :
    sys.toTwoStep.memoryStepInterface.BusBridge sys.segment.stepWithBus := by
  intro Ŝ₁ Ŝ₂ aux hstep
  change sys.segment.isa.committedStep Ŝ₁ Ŝ₂
  exact ⟨aux.memory,
    sys.segment.stepWithBus_committedOperation Ŝ₁ Ŝ₂ aux hstep⟩

/-! ## Applying the segment theorem across one complete execution -/

/-- Information recovered from a complete non-recursive proof: the committed boundary
state between adjacent segments and one independently recovered bus/state
trace for every segment.

Paper: the segment outputs retained in Steps 4--5 of `thm:main` (ch05). -/
structure Execution (sys : TwoStepSystem) where
  boundary : ℕ → CommittedVMState sys.segment.VC
  segments : ℕ → SegmentTrace sys.segment.VC

/-- Join the recovered segment state traces. Bus data stays in `segments`; only
the state traces are concatenated.

Paper: Step 5 of `thm:main` (ch05). -/
def Execution.trace (execution : Execution sys) :
    ℕ → CommittedVMState sys.segment.VC :=
  concatTrace sys.segment.Nseg execution.boundary
    (fun i => (execution.segments i).states) sys.m

/-- A recovered execution is valid when every segment passes the reusable bus
relation and the concatenated states form the committed execution claimed by
the final statement. Each `segments i` has its own bus; no condition compares
buses belonging to different segments.

Paper: Steps 4--5 of `thm:main` (ch05). -/
def Execution.Valid (x : TwoStep.FinalStmt sys.segment.VC)
    (execution : Execution sys) : Prop :=
  (∀ i, i < sys.m →
    sys.segment.segmentValid
      ⟨execution.boundary i, execution.boundary (i + 1)⟩
      (execution.segments i)) ∧
  sys.toTwoStep.CommittedTraceValid x (execution.trace sys)

/-- Build the result returned by `execution_extract`. Callers use its
correctness theorem rather than this helper directly. -/
private def extractedExecution
    (Efinal : Extractor sys.toTwoStep.RFinal sys.toTwoStep.ASFinal)
    (Esegment : SegmentStmt sys.segment.VC → sys.segment.SegmentProof →
      SegmentTrace sys.segment.VC)
    (x : TwoStep.FinalStmt sys.segment.VC) (p : sys.FinalProof) : Execution sys :=
  let finalWitness := Efinal.extract
    (show sys.toTwoStep.RFinal.Stmt from x)
    (show sys.toTwoStep.ASFinal.Proof from p)
  { boundary := finalWitness.boundary
    segments := fun i =>
      Esegment ⟨finalWitness.boundary i, finalWitness.boundary (i + 1)⟩
        (finalWitness.proofs i) }

/-- **Whole-execution extraction for the non-recursive two-layer VM.** Extract
the final witness, apply the reusable `segment_extract` theorem to every
accepted segment proof, and join the resulting state traces with
`chain_flatten`.

The returned value retains every segment's own bus and `MemStep` values. State
concatenation occurs only after `busBridge` has proved that each bus-checked
transition satisfies the existing committed ISA relation.
This theorem uses the segment and final-proof fields of `Assumptions`; the
memory fields in the same structure are used later by `cte`.

Paper: `lem:segment` applied per segment and Steps 4--5 of `thm:main` (ch05). -/
theorem execution_extract (hNseg : 0 < sys.segment.Nseg) (h : sys.Assumptions) :
    ∃ E : TwoStep.FinalStmt sys.segment.VC → sys.FinalProof → Execution sys,
      ∀ (x : TwoStep.FinalStmt sys.segment.VC) (p : sys.FinalProof),
        sys.finalVerify x p → (E x p).Valid sys x := by
  obtain ⟨Esegment, hEsegment⟩ := sys.segment.segment_extract h.segment
  obtain ⟨Efinal, hEfinal⟩ := h.finalSound
  refine ⟨sys.extractedExecution Efinal Esegment, ?_⟩
  intro x p hp
  let finalWitness := Efinal.extract x p
  have hfinal : sys.toTwoStep.RFinal.rel x finalWitness := hEfinal x p hp
  obtain ⟨hboundaryStart, hboundaryEnd, hsegmentVerify⟩ := hfinal
  let segments : ℕ → SegmentTrace sys.segment.VC := fun i =>
    Esegment ⟨finalWitness.boundary i, finalWitness.boundary (i + 1)⟩
      (finalWitness.proofs i)
  have hsegmentValid : ∀ i, i < sys.m →
      sys.segment.segmentValid
        ⟨finalWitness.boundary i, finalWitness.boundary (i + 1)⟩
        (segments i) := by
    intro i hi
    apply hEsegment
    simpa [toTwoStep] using hsegmentVerify i hi
  have hsegmentStart : ∀ i, i < sys.m →
      (segments i).states 0 = finalWitness.boundary i :=
    fun i hi => (hsegmentValid i hi).1
  have hsegmentEnd : ∀ i, i < sys.m →
      (segments i).states sys.segment.Nseg = finalWitness.boundary (i + 1) :=
    fun i hi => (hsegmentValid i hi).2.1
  have hcommittedStep : ∀ i, i < sys.m → ∀ j, j < sys.segment.Nseg →
      sys.segment.isa.committedStep (segments i |>.states j)
        (segments i |>.states (j + 1)) := by
    intro i hi j hj
    exact sys.busBridge _ _ ⟨(segments i).bus, (segments i).steps j⟩
      ((hsegmentValid i hi).2.2 j hj)
  obtain ⟨htraceStart, htraceEnd, htraceStep⟩ :=
    chain_flatten sys.segment.isa.committedStep sys.segment.Nseg sys.m
      hNseg finalWitness.boundary (fun i => (segments i).states)
      hsegmentStart hsegmentEnd hcommittedStep
  refine ⟨?_, ⟨?_, ?_, ?_⟩⟩
  · simpa [extractedExecution, finalWitness, segments] using hsegmentValid
  · simpa [Execution.trace, extractedExecution, finalWitness, segments, toTwoStep] using
      htraceStart.trans hboundaryStart
  · simpa [Execution.trace, extractedExecution, finalWitness, segments, toTwoStep] using
      htraceEnd.trans hboundaryEnd
  · simpa [Execution.trace, extractedExecution, finalWitness, segments, toTwoStep] using htraceStep

/-! ## The demonstration VM and its CTE theorem -/

/-- The full-memory two-layer zkVM whose segment verifier is backed by the
reusable bus system. Its state and step predicate remain `FullVMState` and
`ISA.System.stepPlain`.

Paper: the non-recursive two-layer specialization of `def:zkvm`. -/
def toZkVM : ZkVM := sys.toTwoStep.toZkVM

/-- Correct-trace extractability for the two-layer bus demonstration.

`execution_extract` supplies a committed execution while preserving the bus
evidence for each segment. The existing memory theorem then reconstructs a
full-memory trace satisfying `ISA.System.stepPlain`.

This is not the complete recursive VanillaVM theorem. Its purpose is to show
that the reusable segment result can be used in an actual `ZkVM`; the assembled
module connects that result to the recursive proof system.

Paper: `lem:segment`, Steps 4--6 of `thm:main`, and `def:cte` (ch05), specialized
to the two-layer arrangement. -/
theorem cte (hNseg : 0 < sys.segment.Nseg) (h : sys.Assumptions) :
    sys.toZkVM.CTE := by
  obtain ⟨E, hE⟩ := sys.execution_extract hNseg h
  refine ⟨fun x p =>
      let committedStatement : TwoStep.FinalStmt sys.segment.VC :=
        ⟨TwoStep.toCommitted x.S0, TwoStep.toCommitted x.ST⟩
      let execution := E committedStatement p
      reconstructTrace (execution.trace sys)
        (chooseMemStep sys.segment.isa.committedOperation (execution.trace sys)) x.S0, ?_⟩
  intro x p hp
  let committedStatement : TwoStep.FinalStmt sys.segment.VC :=
    ⟨TwoStep.toCommitted x.S0, TwoStep.toCommitted x.ST⟩
  let execution := E committedStatement p
  have hverify : sys.finalVerify committedStatement p := by
    simpa [toZkVM, toTwoStep, TwoStep.System.toZkVM, committedStatement] using hp
  have hexecution : execution.Valid sys committedStatement := hE _ _ hverify
  simpa [toZkVM, toTwoStep, execution] using
    sys.toTwoStep.traceValid_full h.complete h.positionBinding h.updateBinding x
      (execution.trace sys)
      hexecution.2

end TwoStepSystem
end Bus
end VanillaZkVM
