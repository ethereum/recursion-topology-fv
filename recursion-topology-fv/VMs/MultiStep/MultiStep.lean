import «recursion-topology-fv».Specification.Cte
import «recursion-topology-fv».VMs.ISA
import «recursion-topology-fv».VMs.Memory

/-!
# Multi-layer recursion → `MultiStepVM`

The paper's recursion tower over an **abstract leaf SNARK**, replacing the flat
two-layer merge in `TwoStep`. Three recursion layers — `convert` (1-to-1),
`combine` (binary 2-to-1, self-recursive), `embed` (final cap) — compose into a
`ZkVM` instance whose CTE proof unrolls a binary tree of combine nodes.

The leaf SNARK is abstract: its proof type and verifier are parameters, so the
tower does not depend on the bus. The leaf *relation* is concrete —
a segment of committed steps, each agreeing with the operation the fixed program
selects (`ISA.System.committedOperation`).

## Main definitions
* `MultiStep.System` — the system parameters.
* `RLeaf` / `RConvert` / `RCombine` / `REmbed` — the layer relations.
* `buildTrace` — the **explicit** tree-unrolling extraction procedure.
* `toZkVM` — the `ZkVM` instance over full-memory states.

## Main results
* `combine_tree` — tree-unrolling extraction: given straight-line extractors for
  the leaf, convert, and combine SNARKs, `buildTrace` turns any accepting
  convert-or-combine proof for `N` steps into a valid committed trace. Proved by
  well-founded induction on `N`. Generalizes `chain_flatten` from lists to trees.
* `committedTrace_extract` — embed + tree extraction produces a committed trace.
* `cte` — CTE for `MultiStepVM`, composing the SNARK half with memory
  reconstruction.

Paper: ch04 (`R_2`, `R_3`, `R_4`, `fig:topo`), `lem:convert`/`combine`/`embed`,
`rem:wellfounded`.
-/

namespace VanillaZkVM
namespace MultiStep

/-! # Definitions -/

/-! ## Data types -/

/-- Segment witness. Same shape as `TwoStep.SegWitness`; each VM declares its own. -/
structure SegWitness (VC : VectorCommitment) where
  /-- The committed states. -/
  states : ℕ → CommittedVMState VC
  /-- One `MemStep` per transition. -/
  steps : ℕ → MemStep VC

/-- Statement of the leaf, convert, and combine relations. -/
structure RecStmt (VC : VectorCommitment) where
  /-- The committed start state. -/
  S0 : CommittedVMState VC
  /-- The committed end state. -/
  SN : CommittedVMState VC
  /-- The number of steps from `S0` to `SN`. -/
  N : ℕ

/-- Statement of the embed layer. It has no step count, because `T` is a fixed system
parameter. Paper: `R_4` statement in ch04. -/
structure EmbedStmt (VC : VectorCommitment) where
  /-- The committed start state. -/
  S0 : CommittedVMState VC
  /-- The committed end state. -/
  ST : CommittedVMState VC

/-- Witness of the combine relation. Paper: `R_3` witness in ch04. -/
structure CombineWitness (VC : VectorCommitment) (ConvertProof CombineProof : Type) where
  /-- The left child proof, from convert or combine. -/
  proofL : ConvertProof ⊕ CombineProof
  /-- The right child proof, from convert or combine. -/
  proofR : ConvertProof ⊕ CombineProof
  /-- The committed state between the two children. -/
  Smid : CommittedVMState VC
  /-- The step count of the left child. -/
  NL : ℕ
  /-- The step count of the right child. -/
  NR : ℕ

/-- The `Stmt` of the zkVM. Paper: full-state boundaries in `def:cte` (ch05). -/
structure FinalStmtFull (VC : VectorCommitment) where
  /-- The full start state. -/
  S0 : FullVMState VC
  /-- The full end state. -/
  ST : FullVMState VC

/-- Commit a full state's memory, yielding the corresponding committed state. -/
def toCommitted {VC : VectorCommitment} (S : FullVMState VC) : CommittedVMState VC :=
  ⟨S.pc, S.regs, VC.commit S.mem⟩

/-! ## System -/

/-- The multi-step recursion system. Paper: ch04 recursion tower, with an abstract leaf
SNARK. -/
structure System where
  /-- The memory commitment scheme. -/
  VC : VectorCommitment
  /-- The number of steps in one segment. -/
  Nseg : ℕ
  /-- The total number of steps. -/
  T : ℕ
  /-- The fixed program and its plain/committed operation predicates. Shared with
  `TwoStep`. -/
  isa : ISA.System VC.Index VC.Value
  /-- A segment has at least one step. -/
  hNseg : 0 < Nseg
  /-- `T` is a whole number of segments. -/
  hDvd : Nseg ∣ T
  /-- There are at least two segments. -/
  hT : T ≥ 2 * Nseg
  /-- The leaf proof. -/
  LeafProof : Type
  /-- The leaf verifier. It is abstract: knowledge soundness gives a `SegWitness`, so the
  recursion tower does not depend on the bus. -/
  leafVerify : RecStmt VC → LeafProof → Prop
  /-- The convert proof. -/
  ConvertProof : Type
  /-- The convert verifier. -/
  convertVerify : RecStmt VC → ConvertProof → Prop
  /-- The combine proof. -/
  CombineProof : Type
  /-- The combine verifier. -/
  combineVerify : RecStmt VC → CombineProof → Prop
  /-- The embed (final) proof. -/
  EmbedProof : Type
  /-- The embed (final) verifier. -/
  embedVerify : EmbedStmt VC → EmbedProof → Prop

namespace System

variable (sys : System)

def m : ℕ := sys.T / sys.Nseg

/-! ## The zkVM -/

/-- **The multi-step zkVM.** Its state is the *full-memory* VM state; its step
is `ISA.System.step`, the operation the fixed program selects at `code[pc]`;
its statement carries full boundary states; its verifier commits the boundaries
and defers to the embed SNARK.

Paper: `def:cte` and `prop:memory-extractability` (ch05). The recursion tower
stands where the two-step toy has a flat merge, over the same fixed-program ISA
step; the bus is omitted. -/
def toZkVM : ZkVM where
  State := FullVMState sys.VC
  step := sys.isa.step
  T := sys.T
  Stmt := FinalStmtFull sys.VC
  PrivInput := Unit
  initial := fun x _ => x.S0
  terminal := fun x _ => x.ST
  Proof := sys.EmbedProof
  verify := fun x p => sys.embedVerify ⟨toCommitted x.S0, toCommitted x.ST⟩ p

/-! ## Relations -/

/-- The leaf relation: a trace of `Nseg` committed steps from `S0` to `SN`,
each certified by its `MemStep` witness. Knowledge soundness of the leaf SNARK
extracts the intermediate committed states.

Paper: the segment-level relation; `R_{0,step}` simplified (no bus). Each step
must agree with the operation the fixed program selects, so a proof cannot claim
a read where the program calls for a write. -/
def RLeaf : Relation where
  Stmt := RecStmt sys.VC
  Wit := SegWitness sys.VC
  rel := fun st w =>
    w.states 0 = st.S0 ∧
    w.states sys.Nseg = st.SN ∧
    ∀ j, j < sys.Nseg →
      sys.isa.committedOperation (w.states j) (w.states (j + 1)) (w.steps j)

/-- The leaf argument system. -/
def ASLeaf : ArgumentSystem sys.RLeaf where
  Proof := sys.LeafProof
  verify := sys.leafVerify

/-- `R_2` **convert** (1-to-1): wraps a leaf proof, enforcing `N = Nseg`.

Paper: `lem:convert` (ch04). -/
def RConvert : Relation where
  Stmt := RecStmt sys.VC
  Wit := sys.LeafProof
  rel := fun st p => sys.leafVerify st p ∧ st.N = sys.Nseg

/-- Argument system `Π_2` for convert. -/
def ASConvert : ArgumentSystem sys.RConvert where
  Proof := sys.ConvertProof
  verify := sys.convertVerify

/-- `R_3` **combine** (binary 2-to-1): two children, each accepted by either
`Π_convert` or `Π_combine`, chained through a midpoint. Side conditions enforce
well-foundedness (`rem:wellfounded`): `N_L + N_R = N` with both `≥ Nseg` and
divisible by `Nseg`, so each child's step count is strictly less than the
parent's.

Paper: `lem:combine` (ch04). -/
def RCombine : Relation where
  Stmt := RecStmt sys.VC
  Wit := CombineWitness sys.VC sys.ConvertProof sys.CombineProof
  rel := fun st w =>
    (match w.proofL with
     | .inl p => sys.convertVerify ⟨st.S0, w.Smid, w.NL⟩ p
     | .inr p => sys.combineVerify ⟨st.S0, w.Smid, w.NL⟩ p) ∧
    (match w.proofR with
     | .inl p => sys.convertVerify ⟨w.Smid, st.SN, w.NR⟩ p
     | .inr p => sys.combineVerify ⟨w.Smid, st.SN, w.NR⟩ p) ∧
    w.NL + w.NR = st.N ∧
    sys.Nseg ∣ w.NL ∧ sys.Nseg ∣ w.NR ∧
    w.NL ≥ sys.Nseg ∧ w.NR ≥ sys.Nseg

/-- Argument system `Π_3` for combine. -/
def ASCombine : ArgumentSystem sys.RCombine where
  Proof := sys.CombineProof
  verify := sys.combineVerify

/-- `R_4` **embed** (final): wraps a combine proof for the full execution.

Paper: `lem:embed` (ch04). -/
def REmbed : Relation where
  Stmt := EmbedStmt sys.VC
  Wit := sys.CombineProof
  rel := fun st p => sys.combineVerify ⟨st.S0, st.ST, sys.T⟩ p

/-- Argument system `Π_4` for embed. -/
def ASEmbed : ArgumentSystem sys.REmbed where
  Proof := sys.EmbedProof
  verify := sys.embedVerify

/-! ## Assumptions -/

/-- The cryptographic assumptions of `cte` for the recursive zkVM. Paper:
`lem:convert`/`lem:combine`/`lem:embed` (ch04), `prop:memory-extractability`, `thm:main` (ch05). -/
structure Assumptions (sys : System) : Prop where
  /-- Knowledge soundness of the leaf/segment SNARK `Π_leaf`. -/
  ksLeaf : KnowledgeSound sys.ASLeaf
  /-- Knowledge soundness of the combine SNARK `Π_3`. -/
  ksCombine : KnowledgeSound sys.ASCombine
  /-- Knowledge soundness of the convert SNARK `Π_2`. -/
  ksConvert : KnowledgeSound sys.ASConvert
  /-- Knowledge soundness of the embed SNARK `Π_4`. -/
  ksEmbed : KnowledgeSound sys.ASEmbed
  /-- Openings produced from an honestly committed memory are accepted. -/
  complete : sys.VC.Complete
  /-- One memory commitment cannot open to two values at one address. -/
  positionBinding : sys.VC.PositionBinding
  /-- An accepted write commitment represents the correctly updated memory. -/
  updateBinding : sys.VC.UpdateBinding

/-! ## Committed trace validity -/

/-- A trace of `N` committed steps from `S0` to `SN`, each certified by
`committedStep`. The committed-level analogue of `ZkVM.TraceValid`, spelled out
here because the committed layer carries no `ZkVM` of its own. -/
def CommittedTraceValid (S0 SN : CommittedVMState sys.VC)
    (Ŝ : ℕ → CommittedVMState sys.VC) (N : ℕ) : Prop :=
  Ŝ 0 = S0 ∧ Ŝ N = SN ∧
  ∀ k, k < N → sys.isa.committedStep (Ŝ k) (Ŝ (k + 1))

/-! ## Tree-unrolling extraction

`buildTrace` is the extraction *procedure*: an explicit recursive walk of the
proof tree. At a leaf (`N = Nseg`) it runs convert-then-leaf extraction and
returns the segment's own committed states. At an internal node (`N > Nseg`) it
runs combine extraction to obtain the midpoint and the two child proofs, recurses
on both halves, and glues the results at `N_L`.

It is a *total* function, so it must answer on inputs no honest verifier would
produce. A convert proof claiming `N > Nseg`, a combine proof claiming
`N = Nseg`, and a combine witness whose child counts do not decrease all return
the constant trace at `S0`. The guard is `N ≤ Nseg` rather than `N = Nseg`, so a
convert proof claiming `N < Nseg` instead takes the leaf branch and returns
whatever states extraction hands back. `combine_tree` assumes `Nseg ∣ N` and
`N ≥ Nseg`, which rules out all four. Keeping the branches explicit is what makes
the extractor a real algorithm rather than an appeal to choice.

Termination is the well-founded measure of `rem:wellfounded`: the `dite` guard
puts `w.NL < N` and `w.NR < N` in scope at exactly the two recursive calls.

Paper: `lem:combine` tree unrolling (ch04), `rem:wellfounded`. -/
def buildTrace
    (El : Extractor sys.RLeaf sys.ASLeaf)
    (Ec : Extractor sys.RConvert sys.ASConvert)
    (Ecb : Extractor sys.RCombine sys.ASCombine)
    (S0 SN : CommittedVMState sys.VC) (N : ℕ)
    (p : sys.ConvertProof ⊕ sys.CombineProof) : ℕ → CommittedVMState sys.VC :=
  if N ≤ sys.Nseg then
    match p with
    | .inl cp => (El.extract ⟨S0, SN, N⟩ (Ec.extract ⟨S0, SN, N⟩ cp)).states
    | .inr _ => fun _ => S0
  else
    match p with
    | .inl _ => fun _ => S0
    | .inr cp =>
      if _h : (Ecb.extract ⟨S0, SN, N⟩ cp).NL < N ∧ (Ecb.extract ⟨S0, SN, N⟩ cp).NR < N then
        fun k =>
          if k ≤ (Ecb.extract ⟨S0, SN, N⟩ cp).NL then
            buildTrace El Ec Ecb S0 (Ecb.extract ⟨S0, SN, N⟩ cp).Smid
              (Ecb.extract ⟨S0, SN, N⟩ cp).NL (Ecb.extract ⟨S0, SN, N⟩ cp).proofL k
          else
            buildTrace El Ec Ecb (Ecb.extract ⟨S0, SN, N⟩ cp).Smid SN
              (Ecb.extract ⟨S0, SN, N⟩ cp).NR (Ecb.extract ⟨S0, SN, N⟩ cp).proofR
              (k - (Ecb.extract ⟨S0, SN, N⟩ cp).NL)
      else fun _ => S0
  termination_by N
  decreasing_by
  · omega
  · omega

end System

/-! # Proofs -/

namespace System

variable (sys : System)

/-! ## System parameter properties -/

theorem T_ge_Nseg : sys.T ≥ sys.Nseg :=
  le_trans (Nat.le_mul_of_pos_left sys.Nseg (by omega)) sys.hT

/-! ## Tree-unrolling correctness -/

/-- **Tree-unrolling extraction (correctness).** Given straight-line extractors
for the leaf, convert, and combine SNARKs, `buildTrace` turns any accepting
convert-or-combine proof for `N` steps into a valid committed trace. Proved by
well-founded induction on `N`.

Paper: `lem:combine` (ch04). The proof uses strong induction on `N`; the current
qualitative statement does not count combine nodes. Quantitative `(m-1)`
accounting is deferred. -/
theorem combine_tree
    (El : Extractor sys.RLeaf sys.ASLeaf)
    (hEl : ∀ x p, sys.leafVerify x p → sys.RLeaf.rel x (El.extract x p))
    (Ec : Extractor sys.RConvert sys.ASConvert)
    (hEc : ∀ x p, sys.convertVerify x p → sys.RConvert.rel x (Ec.extract x p))
    (Ecb : Extractor sys.RCombine sys.ASCombine)
    (hEcb : ∀ x p, sys.combineVerify x p → sys.RCombine.rel x (Ecb.extract x p)) :
    ∀ (N : ℕ), sys.Nseg ∣ N → N ≥ sys.Nseg →
      ∀ (S0 SN : CommittedVMState sys.VC) (p : sys.ConvertProof ⊕ sys.CombineProof),
        (match p with
         | .inl cp => sys.convertVerify ⟨S0, SN, N⟩ cp
         | .inr cp => sys.combineVerify ⟨S0, SN, N⟩ cp) →
        sys.CommittedTraceValid S0 SN (sys.buildTrace El Ec Ecb S0 SN N p) N := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro hN_dvd hN_ge S0 SN p hverify
  have hNseg_pos := sys.hNseg
  rw [buildTrace.eq_def]
  by_cases hle : N ≤ sys.Nseg
  · -- **Leaf.** N = Nseg (since N ≥ Nseg ∧ N ≤ Nseg), so the proof must be a
    -- convert proof and convert → leaf extraction returns the segment's trace.
    have hNeq : N = sys.Nseg := le_antisymm hle hN_ge
    subst hNeq
    rw [if_pos hle]
    cases p with
    | inr cp =>
      -- A combine proof here is impossible: its children each cover at least
      -- `Nseg` steps, forcing `N ≥ 2 * Nseg`.
      exfalso
      have hrel := hEcb _ cp hverify
      dsimp only [RCombine] at hrel
      obtain ⟨_, _, hsum, _, _, hNL, hNR⟩ := hrel
      omega
    | inl cp =>
      dsimp only
      have hrel_c := hEc _ cp hverify
      dsimp only [RConvert] at hrel_c
      obtain ⟨hleaf_v, _⟩ := hrel_c
      have hrel_l := hEl _ _ hleaf_v
      dsimp only [RLeaf] at hrel_l
      obtain ⟨hstart, hend, hstep_rel⟩ := hrel_l
      refine ⟨hstart, hend, ?_⟩
      intro k hk
      exact ⟨_, hstep_rel k hk⟩
  · -- **Node.** N > Nseg, so the proof must be a combine proof; extract through
    -- it and recurse on both halves.
    rw [if_neg hle]
    cases p with
    | inl cp =>
      -- A convert proof here is impossible: `R_2` pins `N = Nseg`.
      exfalso
      have hrel := hEc _ cp hverify
      dsimp only [RConvert] at hrel
      obtain ⟨_, hN⟩ := hrel
      omega
    | inr cp =>
      dsimp only
      have hrel := hEcb _ cp hverify
      dsimp only [RCombine] at hrel
      obtain ⟨hvL, hvR, hsum, hdvL, hdvR, hgeL, hgeR⟩ := hrel
      -- Well-foundedness: both children are ≥ Nseg and sum to N, so both are < N.
      have hguard : (Ecb.extract ⟨S0, SN, N⟩ cp).NL < N ∧
          (Ecb.extract ⟨S0, SN, N⟩ cp).NR < N := ⟨by omega, by omega⟩
      rw [dif_pos hguard]
      set w := Ecb.extract ⟨S0, SN, N⟩ cp with hw
      -- Recurse on both subtrees.
      obtain ⟨hL0, hLN, hLstep⟩ := ih w.NL hguard.1 hdvL hgeL S0 w.Smid w.proofL hvL
      obtain ⟨hR0, hRN, hRstep⟩ := ih w.NR hguard.2 hdvR hgeR w.Smid SN w.proofR hvR
      -- Stitch: left trace on [0, NL], right trace shifted onto [NL, N].
      refine ⟨?_, ?_, ?_⟩
      · -- Start: k = 0 ≤ NL
        simp only [Nat.zero_le, ↓reduceIte]; exact hL0
      · -- End: k = N > NL
        have hN_gt_NL : ¬ (N ≤ w.NL) := by omega
        simp only [hN_gt_NL, ↓reduceIte]
        have hN_sub : N - w.NL = w.NR := by omega
        rw [hN_sub]; exact hRN
      · -- Steps: left portion, the seam at k = NL, and the right portion.
        intro k hk
        dsimp only
        by_cases hk1 : k + 1 ≤ w.NL
        · -- Both k and k+1 in the left trace
          have hk0 : k ≤ w.NL := by omega
          simp only [hk0, hk1, ↓reduceIte]
          exact hLstep k (by omega)
        · by_cases hk2 : k ≤ w.NL
          · -- Seam: k ≤ NL but k+1 > NL, so k = NL
            have hkeq : k = w.NL := le_antisymm hk2 (by omega)
            subst hkeq
            simp only [le_refl, hk1, ↓reduceIte]
            have hsub : w.NL + 1 - w.NL = 1 := by omega
            rw [hsub]
            -- the left trace's endpoint *is* the right trace's start: both are `Smid`
            rw [hLN.trans hR0.symm]
            exact hRstep 0 (by omega)
          · -- Both in the right trace
            simp only [hk2, hk1, ↓reduceIte]
            have hsub : k + 1 - w.NL = (k - w.NL) + 1 := by omega
            rw [hsub]
            exact hRstep (k - w.NL) (by omega)

/-! ## The committed-trace extraction -/

/-- **Committed-trace extraction.** If all four SNARKs are knowledge-sound, there
is a committed-trace extractor turning every accepting embed proof into a
committed trace from `x.S0` to `x.ST` of length `T`.

The extractor exhibited is `buildTrace` run on the combine proof that embed
extraction returns — a named procedure, not a choice from an existential.
This theorem uses the four proof-system fields of `Assumptions`; the memory
fields in the same structure are used later by `cte` to reconstruct full
memory.

Paper: `lem:embed` composed with `lem:combine` tree unrolling (ch04). -/
theorem committedTrace_extract (h : sys.Assumptions) :
    ∃ E : EmbedStmt sys.VC → sys.EmbedProof → (ℕ → CommittedVMState sys.VC),
      ∀ (x : EmbedStmt sys.VC) (p : sys.EmbedProof),
        sys.embedVerify x p →
          sys.CommittedTraceValid x.S0 x.ST (E x p) sys.T := by
  obtain ⟨ksLeaf, ksCombine, ksConvert, ksEmbed, _, _, _⟩ := h
  obtain ⟨El, hEl⟩ := ksLeaf
  obtain ⟨Ecb, hEcb⟩ := ksCombine
  obtain ⟨Ec, hEc⟩ := ksConvert
  obtain ⟨Ee, hEe⟩ := ksEmbed
  refine ⟨fun x p =>
    sys.buildTrace El Ec Ecb x.S0 x.ST sys.T (.inr (Ee.extract x p)), ?_⟩
  intro x p hp
  exact sys.combine_tree El hEl Ec hEc Ecb hEcb sys.T sys.hDvd sys.T_ge_Nseg
    x.S0 x.ST (.inr (Ee.extract x p)) (hEe x p hp)

/-! ## The Memory ↔ MultiStep bridge -/

/-- A valid committed trace yields a valid full-memory trace: `trace_mem_extract`
reconstructs full memory along the trace, and
`ISA.System.committedOperation_step` shows that each reconstructed transition
satisfies `ISA.System.step`, upgrading `CommittedTraceValid` to `TraceValid`.

Paper: `prop:memory-extractability` and `rem:mem-inheritance` (ch05). -/
theorem traceValid_full
    (hComplete : sys.VC.Complete) (hpos : sys.VC.PositionBinding)
    (hupd : sys.VC.UpdateBinding)
    (x : FinalStmtFull sys.VC) (Ŝ : ℕ → CommittedVMState sys.VC)
    (hval : sys.CommittedTraceValid (toCommitted x.S0) (toCommitted x.ST) Ŝ sys.T) :
    sys.toZkVM.TraceValid x ()
      (reconstructTrace Ŝ (chooseMemStep sys.isa.committedOperation Ŝ) x.S0) := by
  obtain ⟨hstart, hend, hsteprel⟩ := hval
  -- the invariant seed holds definitionally (committed initial = commit of full initial)
  have hseed : CommitInv (Ŝ 0) x.S0 := by rw [hstart]; exact ⟨rfl, rfl, rfl⟩
  -- Choose a `MemStep` passing both the memory checks and the program checks at
  -- each transition; keeping the program checks is what lets us prove `isa.step`
  -- once memory has been reconstructed.
  have hopC : ∀ k, k < sys.T →
      sys.isa.committedOperation (Ŝ k) (Ŝ (k + 1))
        (chooseMemStep sys.isa.committedOperation Ŝ k) :=
    fun k hk => chooseMemStep_spec sys.isa.committedOperation Ŝ k (hsteprel k hk)
  have hstepC : ∀ k, k < sys.T →
      CommittedMemory.step sys.isa.selectedMemFreePred (Ŝ k) (Ŝ (k + 1))
        (chooseMemStep sys.isa.committedOperation Ŝ k) :=
    fun k hk => (hopC k hk).1
  obtain ⟨hinv, hstepF⟩ :=
    trace_mem_extract hComplete hpos hupd sys.isa.selectedMemFreePred sys.T Ŝ
      (chooseMemStep sys.isa.committedOperation Ŝ) x.S0 hseed hstepC
  refine ⟨rfl, ?_, ?_⟩
  · -- terminal state equals `x.ST`
    show reconstructTrace Ŝ (chooseMemStep sys.isa.committedOperation Ŝ) x.S0 sys.T = x.ST
    set ST' := reconstructTrace Ŝ (chooseMemStep sys.isa.committedOperation Ŝ) x.S0 sys.T
      with hST'
    have hci : CommitInv (Ŝ sys.T) ST' := hinv sys.T (le_refl _)
    rw [hend] at hci
    simp only [toCommitted] at hci
    obtain ⟨hpc, hreg, hmem⟩ := hci
    have e3 : ST'.mem = x.ST.mem := mem_eq_of_commit_eq hComplete hpos hmem
    calc ST' = (⟨ST'.pc, ST'.regs, ST'.mem⟩ : FullVMState sys.VC) := rfl
      _ = ⟨x.ST.pc, x.ST.regs, x.ST.mem⟩ := by rw [← hpc, ← hreg, e3]
      _ = x.ST := rfl
  · -- Every reconstructed transition executes the operation selected by
    -- `code[pc]`, so it satisfies the VM's step predicate.
    intro i hi
    change i < sys.T at hi
    exact sys.isa.committedOperation_step _ _ _ _ _
      (hinv i (by omega)) (hinv (i + 1) (by omega)) (hopC i hi) (hstepF i hi)

/-- **CTE for the multi-step VM.** Under its collected proof-system and memory
commitment assumptions, the multi-step VM is correct-trace extractable over
full-memory states, with `ZkVM.step` the fixed-program ISA predicate.

The two halves meet here: `committedTrace_extract` supplies the explicit
committed-trace extractor (`buildTrace` under an embed extraction), and
`traceValid_full` lifts it to full memory. The extractor exhibited for `CTE` is
that named procedure composed with reconstruction — no choice principle is
applied to the conclusion.

Paper: `def:cte`, `prop:memory-extractability`, `rem:mem-inheritance` (ch05),
and `lem:convert`/`combine`/`embed` (ch04). -/
theorem cte (h : sys.Assumptions) :
    sys.toZkVM.CTE := by
  obtain ⟨E, hE⟩ := sys.committedTrace_extract h
  exact ⟨fun x p =>
      ((), reconstructTrace (E ⟨toCommitted x.S0, toCommitted x.ST⟩ p)
        (chooseMemStep sys.isa.committedOperation
          (E ⟨toCommitted x.S0, toCommitted x.ST⟩ p)) x.S0),
    fun x p hp =>
      sys.traceValid_full h.complete h.positionBinding h.updateBinding x _
        (hE ⟨toCommitted x.S0, toCommitted x.ST⟩ p hp)⟩

end System
end MultiStep
end VanillaZkVM
