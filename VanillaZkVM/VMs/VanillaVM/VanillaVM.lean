import VanillaZkVM.VMs.Bus
import VanillaZkVM.VMs.MultiStep.MultiStep

/-!
# The recursive Vanilla VM with segment buses

This file connects the two independently verified parts of the construction.
`Bus.System.segment_extract` checks one segment and recovers its committed
states, memory-opening data, and bus. It also proves that the step, Keccak,
Poseidon, and range-check proofs all used that same bus. `MultiStep.System`
then uses the segment proof as the base case of its recursive
convert/combine/embed proof tree.

The connection does not separately assume that accepted segment proofs can be
extracted. It derives that fact from the bus theorem, using
`Bus.System.stepWithBus_committedOperation` to show that every recovered
transition passes the bus checks and executes the operation selected by the
fixed program.

## Main definitions
* `System` — the segment-bus system together with the three recursive proof
  layers and their size conditions.
* `System.toMultiStep` — the existing recursive system using the segment
  verifier for its base proofs.
* `System.Assumptions` — every proof-system and commitment assumption used by
  the final theorem.
* `System.toZkVM` — the resulting full-memory zkVM.

## Main results
* `System.cte_main` — in the project's probability-free model, every accepted
  proof for the assembled VM yields a valid full-memory execution trace.

The theorem checks the reduction structure of `thm:main`; it does not supply
running-time or success-probability bounds. The paper itself also notes that
composing straight-line (non-rewinding) extraction through recursive proof
systems relies on an idealized relativized-SNARK assumption (`rem:idealized`).

Paper: the zkVM construction in ch03--ch04 and `thm:main` in ch05.
-/

namespace VanillaZkVM
namespace VanillaVM

/-- The assembled Vanilla VM system for the project's probability-free model.

`segment` contains the bus commitment and the segment/inner proof systems.
The remaining fields contain the convert, combine, and embed proof systems.
Their statements use the same memory commitment, segment length, and fixed ISA
as `segment` by construction.

Paper: `def:zkvm` (ch05), with the proof systems `Π_0` through `Π_4`. -/
structure System where
  /-- The fixed program, memory and bus commitments, and proof systems for one
  segment. -/
  segment : Bus.System
  /-- Total number of VM steps in the complete execution. -/
  T : ℕ
  /-- A segment contains at least one step. -/
  hNseg : 0 < segment.Nseg
  /-- The segment length divides the complete execution length. -/
  hDvd : segment.Nseg ∣ T
  /-- The complete execution contains at least two segments. -/
  hT : T ≥ 2 * segment.Nseg
  /-- Type of proofs that wrap one accepted segment proof. -/
  ConvertProof : Type
  /-- Verifier for proofs that wrap one accepted segment proof. -/
  convertVerify : MultiStep.RecStmt segment.VC → ConvertProof → Prop
  /-- Type of proofs that join two smaller recursive proofs. -/
  CombineProof : Type
  /-- Verifier for proofs that join two smaller recursive proofs. -/
  combineVerify : MultiStep.RecStmt segment.VC → CombineProof → Prop
  /-- Type of the final proof for the complete execution. -/
  EmbedProof : Type
  /-- Verifier for the final proof. -/
  embedVerify : MultiStep.EmbedStmt segment.VC → EmbedProof → Prop

namespace System

variable (sys : System)

/-- Use the bus-checked segment proof as the base proof of the recursive system.

The segment verifier receives only the two boundary states because its length
is the fixed value `segment.Nseg`. `MultiStep.RConvert` separately requires the
recursive statement's step count to equal that value.

Paper: `R_1` feeding `R_2`, followed by `R_3` and `R_4` (ch04). -/
def toMultiStep : MultiStep.System where
  VC := sys.segment.VC
  Nseg := sys.segment.Nseg
  T := sys.T
  isa := sys.segment.isa
  hNseg := sys.hNseg
  hDvd := sys.hDvd
  hT := sys.hT
  LeafProof := sys.segment.SegmentProof
  leafVerify := fun st p => sys.segment.segmentVerify ⟨st.S0, st.SN⟩ p
  ConvertProof := sys.ConvertProof
  convertVerify := sys.convertVerify
  CombineProof := sys.CombineProof
  combineVerify := sys.combineVerify
  EmbedProof := sys.EmbedProof
  embedVerify := sys.embedVerify

/-- The full-memory zkVM obtained from the assembled bus and recursion system.
Its step predicate is the representative ISA's `stepPlain`, and its verifier
commits the claimed initial and final memories before running the embed
verifier.

Paper: the concrete zkVM and boundary commitments used by `thm:main` (ch05). -/
def toZkVM : ZkVM := sys.toMultiStep.toZkVM

/-- Every cryptographic fact that `cte_main` takes as an assumption rather than
proving in this file.

`segment` contains collision resistance of the bus commitment and knowledge
soundness of the segment proof and its four inner proofs. The next three fields
cover the recursive proof layers. The final three fields are the memory
commitment properties needed to reconstruct full memory.

There is no separate assumption that the base segment proof can be extracted:
`leaf_sound` below derives this from `segment`.

Paper: the assumptions charged by `thm:main` (ch05), in the perfect model. -/
structure Assumptions (sys : System) : Prop where
  /-- The assumptions needed to extract a valid trace and one common bus from
  an accepted segment proof. -/
  segment : sys.segment.Assumptions
  /-- An accepted convert proof reveals the segment proof that it wraps. -/
  convertSound : KnowledgeSound sys.toMultiStep.ASConvert
  /-- An accepted combine proof reveals its two child proofs and their shared
  boundary state. -/
  combineSound : KnowledgeSound sys.toMultiStep.ASCombine
  /-- An accepted final proof reveals an accepted combine proof for the
  complete execution. -/
  embedSound : KnowledgeSound sys.toMultiStep.ASEmbed
  /-- Openings produced from an honestly committed memory are accepted. -/
  complete : sys.segment.VC.Complete
  /-- One memory commitment cannot open to two values at the same address. -/
  positionBinding : sys.segment.VC.PositionBinding
  /-- A commitment accepted after a write represents the correctly updated
  memory. -/
  updateBinding : sys.segment.VC.UpdateBinding

/-- Show that an accepted base segment proof yields a valid committed trace,
as required by the recursive system. This follows from the complete
one-segment bus theorem. After that theorem has checked the hash and range data
against one bus, the recursive proof only needs the resulting committed trace. -/
private theorem leaf_sound (h : sys.segment.Assumptions) :
    KnowledgeSound sys.toMultiStep.ASLeaf := by
  obtain ⟨E, hE⟩ := sys.segment.segment_extract h
  refine ⟨⟨fun st p =>
    let tr := E ⟨st.S0, st.SN⟩ p
    ⟨tr.states, tr.steps⟩⟩, ?_⟩
  intro st p hp
  change sys.segment.segmentVerify ⟨st.S0, st.SN⟩ p at hp
  have hvalid := hE ⟨st.S0, st.SN⟩ p hp
  change
    (E ⟨st.S0, st.SN⟩ p).states 0 = st.S0 ∧
    (E ⟨st.S0, st.SN⟩ p).states sys.segment.Nseg = st.SN ∧
    ∀ j, j < sys.segment.Nseg →
      sys.segment.isa.committedOperation
        ((E ⟨st.S0, st.SN⟩ p).states j)
        ((E ⟨st.S0, st.SN⟩ p).states (j + 1))
        ((E ⟨st.S0, st.SN⟩ p).steps j)
  refine ⟨hvalid.1, hvalid.2.1, ?_⟩
  intro j hj
  exact sys.segment.stepWithBus_committedOperation _ _
    ⟨(E ⟨st.S0, st.SN⟩ p).bus,
      (E ⟨st.S0, st.SN⟩ p).steps j⟩
    (hvalid.2.2 j hj)

/-- Put the assembled system's assumptions into the form expected by the
reusable recursion theorem. -/
private theorem multi_step_assumptions (h : sys.Assumptions) :
    sys.toMultiStep.Assumptions :=
  ⟨sys.leaf_sound h.segment, h.combineSound, h.convertSound, h.embedSound,
    h.complete, h.positionBinding, h.updateBinding⟩

/-- **Main probability-free security theorem for the assembled Vanilla VM.**

An accepted embed proof is recursively reduced to its base segment proofs. For
each segment, `segment_extract` proves that the step, Keccak, Poseidon, and
range-check proofs used the same bus, and it recovers committed transitions
that follow the fixed program. The recursive extractor joins those segment
traces, and the memory theorem reconstructs a full-memory execution between
the claimed initial and final states.

All cryptographic assumptions are listed in `Assumptions`; in particular, the
ability to extract an accepted base segment proof follows from the bus
assumptions rather than being postulated independently.

Paper: qualitative, perfect-model form of `thm:main` (ch05). -/
theorem cte_main (h : sys.Assumptions) : sys.toZkVM.CTE := by
  change sys.toMultiStep.toZkVM.CTE
  exact sys.toMultiStep.cte (sys.multi_step_assumptions h)

end System
end VanillaVM
end VanillaZkVM
