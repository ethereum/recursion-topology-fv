# PLAN — development issues for the Vanilla zkVM Lean formalization

This is the working plan: **10 dependency-ordered issues** taking us from the current two-step toy
to a formalized main security theorem for the full vanilla VM (`thm:main`). Issue 2 was withdrawn
and Issue 10 added; every other issue keeps the number it has always had, so 2 is simply skipped.
It supersedes the
free-form task list in `benedikt-plan.md` (whose relevant items it incorporates)
and is the authoritative scope (I2).

**How to read an issue.** Each has: *Goal · Depends on · Assigned · Reuse · New public surface ·
Deliverables · Math companion · Review requirement (where assigned; human, not delegatable) ·
Skills & conventions · Paper anchor.* Everything is written on a branch per issue and merged into `main`
(`CONVENTIONS.md` §4).

**Collaborators & roles.**
- **Implementers:** Yavor (RovayL), Dmitry (khovratovich), Jessica (j-cqy).
- **Reviewers only (for now):** Benedikt (b-wagn).
- **George (asn-d6): reviewer now, likely to join as an implementer.** When he does, his natural
  slots (he is a paper co-author, so strongest on structure/topology) are: the redundant **human**
  second attempt at the tree-unrolling lemma in **Issue 4**, and co-lead of the **Issue 7** capstone.
  Until then he stays a reviewer. **Rule:** whoever implements an issue cannot be its reviewer — if
  George takes an issue, its reviewer shifts to Benedikt (or another non-author).

**Assignments follow the code people have already written** (git-verified):
Yavor owns memory reconstruction (`pr5`/`yl-memory-reconstruction`) and authored
the former `Bus.lean` prototype, now retained only in git history;
Dmitry owns the memory→abstract-VM integration (`memory-integration`, full-memory CTE) and the
cost/reduction experiments (`cost-twostep`, `cost-bus-reduction`); Jessica owns the security-model
study (Issue 8) and the keyed/algorithmic CR variant (`cr-algorithmic`) — both bounded and
self-closing. **Jessica leaves soon, so Issues 10 and 6 are unassigned** and must not be scheduled
against her; Issue 8's report is the handover artifact for whoever takes them.

**Redundancy (by design).** Issue **1** carries two independent memory integrations (Yavor's
Bus-wired core vs Dmitry's abstract-VM full-memory CTE) that must prove the same statement, and Issue
**9** re-derives the statements independently. This cross-validation is deliberate (Hicks).

---

## Dependency graph

```
Qualitative track — reaches the main theorem in the perfect model:

        ┌─────────────────────────── Issue 0  (freeze KERNEL + scaffolding)  ← blocks all
        │
        ├── Issue 1  memory  → TwoStepWithMemory          (Yavor + Dmitry, redundant)
        ├── Issue 3  ISA ops {read, write, arith, hash, bin} (Yavor)
        └── Issue 4  multi-layer recursion → MultiStepVM   (Dmitry)   [abstract leaf — no bus needed]

   Issue 5  bus per segment, wired into a VM   (Yavor)   depends 0,3     ← intentionally LATE
   Issue 7  full Vanilla VM + cte_main (perfect model)  (Dmitry + Yavor)  depends 1,3,4,5

Quantitative track — turns `cte_main` from an implication into an explicit bound. Runs after, never gates:

   Issue 8   security-model study: advantages, runtime, reuse    (Jessica)   depends 0
   Issue 10  explicit-advantage foundation (constants only)      (TBD)       depends 8
   Issue 6   explicit per-layer reductions, with real advantages (Dmitry + TBD)  depends 1,3,4,5,7,10

Rolling alongside everything:

   Issue 9  independent re-derivation + audit matrix + vacuity (Yavor + Dmitry)  depends 0

   Issue 2  withdrawn — number retired, not reused.
```

Critical path: **0 → {1,3,4,5} → 7**. Recursion (4) is built over an **abstract** leaf relation, so
it does **not** wait for the bus (5) — that is why the bus is scheduled late.

The quantitative track is deliberately **off** the critical path. `cte_main` is provable in the
perfect model, so probabilities must not gate it; Issue 6 strengthens the finished theorem instead of
standing between the layers and it.

**Every issue produces or extends a math companion** (`docs/math-companion.md`, following the
precedent Dmitry set on `memory-integration`): the pen-and-paper statements matching the Lean, kept
in lockstep. This is a hard deliverable, not optional.

---

## Issue 0 — Freeze the core *kernel* & stand up the review scaffolding
- **Goal.** Cleanly separate (0) crypto preliminaries, (1) abstract zkVM + security definition,
  (2) concrete VM, (3) proofs; and **freeze the kernel** (I4) — *not* all of `Preliminaries/`. The
  kernel is the stable heart Hicks says to polish; the commitment layer is explicitly left
  provisional (see below).
- **Depends on.** — (first).
- **Assigned.** Dmitry (kernel interfaces) + Yavor (scaffolding & docs).
- **Reuse.** Current `main` `Preliminaries/ArgumentSystem.lean` / `Specification/{Zkvm,Cte}.lean`
  (refactor, don't rewrite). No branch code.
- **Frozen kernel (I4).** `Relation`, `ArgumentSystem`, `Extractor`, `KnowledgeSound`; abstract
  `ZkVM`, `TraceValid`, `Rstar`, `CTE`, `cte_iff_knowledgeSound`; plus the Lean-only consistency
  signatures `StepInterface`, `StepInterface.MemoryBridge`, and `StepInterface.BusBridge`.
  **Provisional (NOT frozen — expected to change):** `VectorCommitment`'s binding predicates —
  `PuncturedBinding` is known to be **insufficient** and is **replaced by `UpdateBinding`**
  in Issue 1; `Complete` is made explicit there; and `CollisionResistant` may gain a
  keyed/algorithmic variant (Jessica's `cr-algorithmic`). These live in
  `Preliminaries/VectorCommitment.lean` and `Preliminaries/HashCommitment.lean` but are
  marked provisional in their docstrings and are free to change without a constitutional amendment.
- **New public surface (3 source declarations).** `StepInterface` (whose three structure fields are
  its committed-step API), `StepInterface.MemoryBridge`, and `StepInterface.BusBridge`. These are
  the minimum coordination surface needed by Issues 1, 3, and 5; `ZkVM.step` is reused as the
  canonical plain predicate rather than duplicated. All other changes reorganize existing
  declarations or add private validation examples.
- **Deliverables.** (a) `Preliminaries/` = definitions only, kernel vs provisional clearly separated;
  proofs/instances moved out. (b) `docs/` scaffolding ratified: `INVARIANTS.md`, `CORRESPONDENCE.md`,
  `CONVENTIONS.md`, `docs/sessions/TEMPLATE.md`, `docs/LESSONS_LEARNED.md`,
  `SKILLS/adversarial-review.md` ported from finality. (c) CI: `lake build` + `#print axioms` +
  a `CORRESPONDENCE` row-elaboration check and repo-wide I7 hygiene check. (d) Freeze the step
  contract in `VMs/Step.lean` / `docs/STEP_INTERFACES.md`: `ZkVM.step` is the plain predicate,
  `stepCommitted` is the memory-layer predicate, and `stepWithBus` feeds it through the bus bridge;
  concrete bodies belong to Issues 1, 3, and 5.
- **Math companion.** Establish `docs/math-companion.md` with the kernel definitions written
  out on paper; every later issue appends to it.
- **Review requirement.** Ordinary collaborator PR review; there is no additional joint
  Benedikt/George ratification gate for Issue 0. Dmitry signed the paper-facing core rows on
  2026-07-29. Independent re-derivation and rolling audits remain Issue 9.
- **Skills & conventions.** `/simplify` on the refactor; `/security-review` on the definitions.
  `CONVENTIONS.md` §1–2. No existing declaration changes behavior; validation and interface
  scaffolding may be additive.
- **Paper anchor.** The revision pinned in `docs/PAPER_REVISION.md`: ch03 (`R*`), ch05
  (`def:extractable`, `def:cte`, `rem:cte-ks`).
- **Scope amendment (approved 2026-07-29, Dmitry).** Add exactly three public step-interface
  declarations, close the discovered I7 enumeration/string-literal gaps, record the corrected
  fixed-`T` CTE semantics (with the available paper commit pinned for PR confirmation), and drop the
  previously stated Benedikt/George joint-review requirement.

## Issue 1 — Committed memory → `TwoStepWithMemory` (CTE from memory-commitment properties)
- **Goal.** Make the two-step VM operate on *committed* memory and prove it CTE **assuming**
  properties of the memory commitment scheme — reconstruct the full `Addr→Byte` memory from a
  committed-state trace + per-step opening witnesses. **Introduce `UpdateBinding` to replace the
  insufficient `PuncturedBinding`** and formalize `prop:memory-extractability`.
- **Depends on.** Issue 0.
- **Assigned.** **Redundant:** Yavor (base: `pr5`'s Bus-wired reconstruction core — his code) **and**
  Dmitry (`memory-integration`'s abstract-VM full-memory CTE); reconcile to one `Memory.lean`
  core at the end. *Review: George (and/or Benedikt).*
- **Reuse.** **`pr5`** — best base (trace-level `trace_mem_extract`, boundary-exact, only branch with
  concrete non-vacuity checks incl. `appendBitVC_not_updateBinding`; already replaces punctured with
  update binding). **`memory-integration`** — its full-memory `Twostep` integration + its
  `math-companion.md` (incorporate into the project companion). **`yl-memory-reconstruction`** — docs
  reference (identical Lean to pr5; skim `AXIOM_AUDIT.md`). **DROP `memory-recon`** (destructive,
  least complete). Re-apply hunks onto current `main` (§4).
- **New public surface (max ~5).** `UpdateBinding` (+ break witness), `FullVMState`/`CommitInv`,
  the concrete `committedStep` predicate underlying `StepInterface.stepCommitted`,
  `step_mem_extract`, and `trace_mem_extract`. `TwoStepWithMemory` is realized as
  `TwoStep.System.toZkVM`, an *instance* of the abstract `ZkVM` (I5), rather than as a duplicate
  security definition. Deprecate/remove `PuncturedBinding` in the same PR.
- **Deliverables.** Reconciled `VMs/Memory.lean` core, the `TwoStepWithMemory` instance, `cte`
  (CTE over *full* memory), `MemorySanity`-style non-vacuity instances, and a concrete proof of
  `StepInterface.MemoryBridge`.
- **Math companion.** Write the memory-extractability proposition and the read/write commitment
  equations into `math-companion.md` (Dmitry already drafted much of this on `memory-integration`).
- **Review requirement (human — George).** Confirm `UpdateBinding` matches `def:binding` and is
  the update-realizability guarantee missing from the retired punctured condition (the paper treats
  position binding and update binding as independent); that `CommitInv` is the right invariant; and
  that Yavor's and Dmitry's two integrations prove *the same* statement. Approve the Issue-1
  `CORRESPONDENCE` rows; run the vacuity probe.
- **Skills & conventions.** `/security-review` (definitions), `/simplify`, adversarial-review at
  session end. Derive from `VectorCommitment`; do not re-declare frozen kernel notions.
- **Paper anchor.** ch02 (`Com_mem`, `def:binding`), ch03 (`φ̂_read`/`φ̂_write`),
  `prop:memory-extractability`.

## Issue 2 — *withdrawn: extract-or-break*

The extract-or-break framework is abandoned. Its purpose was to expose reduction structure without
probabilities — "a broken guarantee yields either a witness or a named assumption break". In the
perfect model there is no probabilistic bad event, so that shape reduces to the implication each
layer lemma already is (compare `TwoStep.System.cte`, which takes its assumptions as hypotheses and
collects them in `Assumptions`), while obliging every layer to adopt a vocabulary for the privilege.

Explicit reductions remain a goal. They need real success probabilities first: see **Issue 10** for
the foundation and **Issue 6** for the reductions themselves.

The number is retired rather than reused, so Issues 3–9 keep their existing labels. The paper's own
`lem:segment` argument is still an extract-or-collision one; abandoning the *framework* only means we
do not build reusable Lean vocabulary for that shape, not that the bus proof changes character.

## Issue 3 — ISA operations: a small representative op set `{read, write, arith, hash, bin}`
- **Goal.** Replace the fully-opaque step predicate with a **small, representative** op taxonomy —
  memory `read`/`write`, `arith` (arithmetic), `hash` (hash-call precompiles, collapsing
  keccak/poseidon), and `bin` (binary/bitwise ops) — and the disjunctive `φ_step := ⋁_op φ_op`.
  **Deliberately do not model the paper's full 20-opcode taxonomy**; op *semantics* stay opaque
  black-box predicates. We model the *structure* (memory-free split, which class defers to a chip).
- **Depends on.** Issue 0. (Soft-coordinates with Issue 1 for `read`/`write`, Issue 5 for chip routing.)
- **Assigned.** Yavor (his memory work already defines `readC`/`writeC`/`readF`/`writeF`).
  *Review: George.*
- **Reuse.** Yavor's own read/write predicates from `pr5`. Otherwise new.
- **New public surface (max ~4).** An `ISA` operation type (the 5-class op set + per-op predicate
  split `φ_op`/`φ'_op`), the memory-free/memory-equation decomposition, and the disjunctive
  `stepPred`.
- **Deliverables.** `ISA.lean`: the 5 op classes, `φ'_op`/`φ_op` split, `φ_read`/`φ_write` with their
  memory equations, and `φ_step` as the disjunction; a lemma that non-memory ops don't mutate
  memory. The resulting `ISA.stepPlain` is used as the concrete `ZkVM.step`, not a parallel relation.
- **Math companion.** Write the 5-class step predicate and the read/write memory equations.
- **Review requirement (human — George).** Confirm the 5-class set is a faithful *representative*
  simplification of ch03 (fetch conjunct `code[pc]=op` present; `φ_step` neither stronger nor weaker
  than the disjunction over these classes). Approve the op-predicate `CORRESPONDENCE` rows, noting
  the deliberate simplification from 20 ops.
- **Skills & conventions.** `/simplify` (factor the classes via a family — I10), `/code-review`.
  Paper-vocabulary names.
- **Paper anchor.** ch01 (step relation, memory ops), ch03 (op taxonomy, `φ_step`) — simplified.

## Issue 4 — Multi-layer recursion → `MultiStepVM` (convert / combine / embed)
- **Goal.** Replace the flat two-layer merge with the paper's recursion tower over an **abstract
  leaf** relation: `R_2` convert (1-to-1), `R_3` combine (binary 2-to-1, self-recursive, well-founded
  by strictly-decreasing step counts), `R_4` embed (final, `T ≥ 2·N_seg`). Provide an explicit
  **tree-unrolling** extractor and correctness lemma generalizing `chain_flatten` from a list to the
  binary recursive proof shape. Quantitative `(m-1)` combine-node accounting is deferred to Issue 6.
- **Depends on.** Issue 0. (Uses an abstract leaf — does **not** depend on the bus, Issue 5.)
- **Assigned.** Dmitry (his `cost-twostep` shows he works on the merge/two-step structure).
  *Review: George + Benedikt. Redundant tree-lemma attempt via the Issue-9 autonomous re-derivation.*
- **Reuse.** None directly; `chain_flatten` is the pattern to generalize.
- **New public surface (max ~6).** `RConvert`/`RCombine`/`REmbed` (derived via `Relation`),
  `buildTrace`, the `combine_tree` correctness lemma, and `MultiStepVM` as a `ZkVM` instance.
  Well-foundedness side conditions live inside the relation, not as public lemmas.
- **Deliverables.** `MultiStep.lean` with the three relations, the explicit recursive extractor and
  its correctness lemma, the `MultiStepVM` instance, and its CTE (perfect model) via composed
  extraction over an abstract leaf.
- **Math companion.** Write the recursive proof shape, the well-founded measure, and the unrolling
  lemma.
- **Review requirement (human — George).** Confirm the well-founded measure (child step counts
  strictly `< N`; `N=N_seg` base vacuous by arithmetic, per `rem:wellfounded`); that unbalanced
  recursive decompositions are admitted (only `N_L+N_R=N` + divisibility); and that `embed`'s
  `T≥2N_seg` is enforced. Confirm the redundant re-derivation proves the same statement.
- **Skills & conventions.** `/security-review`, `/simplify`. Generalize — don't fork — `chain_flatten`.
  Heavy branch-point comments on the induction (finality style).
- **Paper anchor.** ch04 (`R_2`,`R_3`,`R_4`, `fig:topo`), `lem:convert`/`combine`/`embed`,
  `rem:wellfounded`.

## Issue 5 — Bus functionality per segment, wired into a VM  *(scheduled late)*
- **Goal.** Build the segment/bus layer **properly**. The former `Bus.lean`
  playground prototype was removed from the active tree because it was not
  ground truth; consult it only in git history. Then lift
  single-segment extraction across a whole execution: `m` segments each with their own
  internally-consistent bus `B̂_i`, concatenated by `concatTrace`/`chain_flatten` into one length-`T`
  trace carrying per-segment `StepAux`/bus data. Slotted **late** because the recursion tower (Issue
  4) is built over an abstract leaf and does not need it.
- **Depends on.** Issue 0, Issue 3 (chips consume the op taxonomy).
- **Assigned.** Yavor (author of the prototype). *Review: Benedikt.*
- **Reuse.** The deleted prototype from git history as *reference only* — reimplement to the frozen kernel and the
  Issue-3 ISA; do not treat its `segment_extract` as done. `cost-bus-reduction` reference for the
  future cost combinators. Reuse `concatTrace`/`chain_flatten` from the kernel (do not duplicate).
- **New public surface (max ~3).** A bus-backed segment relation + a `Bus`-backed VM as an *instance*
  of the abstract `ZkVM`, plus the lifting lemma (segment extraction ∘ concatenation).
- **Deliverables.** The proper segment/bus layer, a proof of `StepInterface.BusBridge`, a
  `Bus`-backed VM instance, and the per-execution lifting theorem threading per-segment `StepAux`.
- **Math companion.** Write the bus, `φ̂_step` bus-deferral, and the per-execution lift.
- **Review requirement (human — Benedikt).** Confirm the redone layer faithfully realizes
  `lem:segment` — bus unification, with collision resistance of `Com_bus` consumed as a hypothesis —
  that per-segment buses are **not** claimed
  equal across segments (only internally consistent), and that concatenation preserves the boundary
  chaining `thm:main` Steps 4–5 need. Confirm `chain_flatten` is reused, not reimplemented.
- **Skills & conventions.** `/simplify`, `/security-review`. Reuse the frozen concatenation lemma (I5).
- **Paper anchor.** ch02 (bus, segments), `lem:segment`, `thm:main` Steps 4–5.

## Issue 6 — Explicit per-layer reductions, with real advantages
- **Goal.** Restate every layer's guarantee (memory, bus, convert, combine, embed) as an explicit
  reduction with a *quantitative* conclusion, and compose them into `thm:main`'s weighted sum
  (`1, m-1, m, m·(…+cr), Σ_{k=1}^T(pos+upd)`). This upgrades `cte_main` from "holds under these
  assumptions" to "is broken with at most this advantage". Every coefficient is an explicit
  constant; no negligibility claim enters the chain.
- **Why this comes after advantages.** With perfect predicates there is no failure event to bound,
  so a reduction collapses into the implication the layer lemma already is. Placeholder advantages
  would be worse than none: nothing would constrain the coefficients, so the formalization could not
  be wrong — an I6 vacuity failure by construction. Real advantages are what make the weighted sum a
  checkable claim.
- **Depends on.** Issue 10 (advantages must exist), the layers 1, 3, 4, 5, and Issue 7 (the assembly
  it re-derives quantitatively).
- **Assigned.** Dmitry (cost/composition) + owner TBD (reductions). *Review: Benedikt + George, one per
  half.*
- **Reuse.** Issue 10's advantage layer; `cost-twostep`/`cost-bus-reduction` as reference for how an
  explicit reduction `Alg` and its cost were written.
- **New public surface (max ~4).** Per-layer reduction statements over Issue 10's vocabulary. No new
  security *definitions* — those are Issue 10's.
- **Deliverables.** Each layer lemma restated as an advantage bound; an internal counting lemma tied
  to the reduction's actual traversal, showing that `m` segment leaves cause `m-1` combine
  invocations; the composed `thm:main` bound with its real coefficients; `cte_main` re-derived
  quantitatively, superseding Issue 7's qualitative form without contradicting it.
- **Math companion.** The per-layer reductions and the summed bound.
- **Review requirement (human — Dmitry/Benedikt).** Confirm each reduction targets the *correct*
  assumption (Hicks: *what* you reduce to matters), that the coefficient structure matches
  `thm:main`, and that no reduction is vacuous. Running-time bookkeeping may still be deferred (I9);
  say so explicitly rather than implying it is covered.
- **Skills & conventions.** `/security-review` mandatory. Reductions = plain `def`s + `≤` statements.
- **Paper anchor.** ch05 §5.2 (all layer lemmas, `prop:memory-extractability`), `thm:main` bound.

## Issue 7 — Assemble the full Vanilla VM & state the main theorem
- **Goal.** Compose Issues 1+3+4+5 into the full `zkVM = ({φ_op}, Com_bus, Com_mem, Π_0..Π_4)` and
  state + prove the top-level CTE theorem in the **perfect model**: given knowledge soundness of
  `Π_0..Π_4`, the memory-commitment binding properties, and collision resistance of `Com_bus`, the
  full VM is correct-trace extractable. This is the qualitative Lean analogue of `thm:main`; Issue 6
  later replaces the hypothesis bundle with `thm:main`'s advantage bound. Tie the outermost CTE
  statement to `VMState`/`CommittedVMState` via `Com_mem` (the `Commit(mem_0/T)` step the abstract
  statement currently omits).
- **Depends on.** Issues 1, 3, 4, 5. Deliberately **not** Issue 6: the theorem is provable in the
  perfect model, so it must not wait on the advantage foundation.
- **Assigned.** Dmitry + Yavor (capstone). *Review: Benedikt + George.*
- **Reuse.** Everything above.
- **New public surface (max ~2).** The full `VanillaVM` instance + `cte_main`. Nothing else public.
- **Deliverables.** The assembled VM; `cte_main` with its assumptions collected in one trust-base
  structure (the pattern `TwoStep.System.Assumptions` already sets); and a `docs/` note recording the
  paper's own idealization caveat (`rem:idealized`: relativized SNARKs don't exist → validates
  reduction *structure*, not concrete security). Note there too that the Lean bound stays a concrete
  inequality by choice — the absence of `negl` is the Issue-10 scope decision, not an omission.
- **Math companion.** Write `thm:main` and its assembly from the layer lemmas.
- **Review requirement (human — Dmitry + Benedikt).** Confirm `cte_main` is the faithful
  *qualitative* Lean form of `thm:main`, that the trust base names every assumption the paper charges
  for, that the boundary-commitment step is present, and that the idealization caveat is documented.
  Approve the `thm:main` row — fidelity yes; completeness stays open until Issue 6 supplies the bound.
  Full `#print axioms cte_main`.
- **Skills & conventions.** `/security-review`, `/simplify`, adversarial-review. Final public surface
  + `cte_main` must be readable and ≈ paper length (I10) — measure it.
- **Paper anchor.** ch05 (`thm:main`, zkVM system definition, `rem:idealized`).

## Issue 8 — (Parallel) security-model study: advantages, runtime, and dependency reuse
- **Goal.** Decide *how* to lift the perfect model to explicit-constant security (advantages, running
  time of reductions) and report feasibility/size/dependencies. Asymptotics are out of scope by
  decision — the question is how to express concrete bounds, not whether to go asymptotic. Still a
  report, not core Lean — **nothing merges into core here** (I8). Also the "not reinventing the
  wheel" reuse study (mathlib/VCVio/arklib), and a recommendation on whether to adopt the
  keyed/algorithmic CR variant (`cr-algorithmic`).
- **Gates.** Issue 10 does not start until this report is accepted: it chooses VCVio-vs-from-scratch
  and bounds Issue 10's public surface. A go/no-go here is a genuine decision point, not a formality —
  "stay perfect indefinitely" is an admissible outcome, in which case Issues 10 and 6 stay unstarted
  and `cte_main` remains the qualitative theorem.
- **Depends on.** Issue 0 (otherwise independent).
- **Assigned.** Jessica (reductions/concrete-security fit; benedikt-plan's "concrete bounds" and
  "reuse" tasks). *Review: Dmitry + Benedikt.*
- **Reuse.** **VCVio**: `Security.lean` (advantage decoupled from game; reduction/game-hop/hybrid
  meta-theorems) + `HardnessAssumptions/DiffieHellman.lean` (reduction-as-function template). Its
  `Asymptotics/Negligible.lean` is *not* needed under the constants-only scope. **Cost:**
  `cost-twostep`'s `Cost.lean` (superset with `seqRange`) as the exact-cost reference.
- **New public surface.** None in core. Output = a `docs/` report + an isolated prototype branch.
- **Deliverables.** `docs/security-model-report.md` (perfect vs explicit-constant recommendation;
  cost of a `PMF` re-foundation; when/if to import VCVio; a map of our frozen kernel to VCVio
  equivalents so a later swap is mechanical) + a throwaway prototype lifting **one** lemma to
  advantages as a size probe. The report must be readable by someone who never spoke to its author:
  it is the handover document for Issues 10 and 6.
- **Math companion.** N/A (a report, not core Lean) — but the VCVio-mapping table lives in the report.
- **Review requirement (human — Dmitry + Benedikt).** Review the *recommendation*: is perfect still
  the right default? Is our `KnowledgeSound` translatable to VCVio's? Decide go/no-go on Issue 10, and
  if go, fix its public-surface budget here (I2). (Hicks: keep the door open, don't walk through yet.)
- **Skills & conventions.** Strictly out of `main`'s core build (isolated branch/dir). Cheaper
  models + subagents to read VCVio; store findings in files.
- **Paper anchor.** ch05 advantages; `rem:idealized`.

## Issue 9 — (Rolling, redundant) independent re-derivation + audit matrix + vacuity sweep
- **Goal.** The independent-certificate track Hicks endorsed: in a **separate** repo/branch, have
  agents formalize the statements from *informal* requirements **without** the paper, then match
  against the paper as an independent correctness certificate. Simultaneously keep `CORRESPONDENCE.md`
  current and run periodic vacuity/axiom sweeps.
- **Depends on.** Issue 0; then rolls alongside 1–7 (audits each as it lands).
- **Assigned.** Yavor + Dmitry (benedikt-plan's documentation/communication task), redundant
  re-derivation driven by an autonomous agent under their oversight. *Review: George.*
- **Reuse.** finality's `AUDIT.md`, `SKILLS/adversarial-review.md`, `spec_index` idea, session ledger;
  VCVio's `docs/agents/*.md` per-topic guide format once layers stabilize.
- **New public surface.** None.
- **Deliverables.** A maintained `CORRESPONDENCE.md` with reviewer sign-offs; periodic
  `docs/sessions/` audit entries; the independent re-derivation write-up; a `docs/agents/` guide set.
- **Math companion.** The re-derivation's own companion is compared against the main one.
- **Review requirement (human — George; re-derivation judged by Dmitry).** For each audited issue, a
  reviewer other than its author performs the `CONVENTIONS.md` §6 definition audit and signs the row.
  For the re-derivation, Dmitry judges whether the independently-derived statements *mean the same
  thing* as the paper's — a human "these coincide" is precisely the payoff.
- **Skills & conventions.** adversarial-review skill; fan-out independent skeptics; CONFIRMED-only
  findings; revert all injected probes.
- **Paper anchor.** whole paper (matrix); `rem:cte-ks`/`thm:main` for the re-derivation target.


## Issue 10 — Explicit-advantage foundation (concrete constants, no asymptotics)
- **Goal.** Build the machinery a quantitative statement needs, and only that: randomized
  adversaries and real-valued advantages at *fixed* parameters. **No negligibility, no
  security-parameter families, no PPT predicate** — a bound is an explicit expression, not an
  asymptotic claim. This is the cheapest thing that makes Issue 6's weighted sum checkable. Then
  restate `KnowledgeSound`, `PositionBinding`, `UpdateBinding`, and `CollisionResistant` as
  advantage-bounded predicates, with today's perfect predicates recovered as the zero-advantage case
  so no existing theorem silently changes meaning.
- **Depends on.** Issue 8 (its accepted recommendation and surface budget). Independent of the
  qualitative track — it touches `Preliminaries/`, not the VM layers.
- **Assigned.** Unassigned (owner TBD; Dmitry, or George if he joins as an implementer).
  *Review: Dmitry + Benedikt.*
- **Reuse.** Whatever Issue 8 recommends: VCVio's `Security.lean` advantage pattern, or a minimal
  `PMF`-based layer of our own. Negligibility and PPT machinery are out of scope, so VCVio's
  `Asymptotics/` and its unimplemented `WorstCasePolyTime`/`ExpectedPolyTime` are not in play.
- **New public surface.** Bounded by the Issue-8 report before work starts (I2 — no unbounded scope).
  Expect an advantage vocabulary plus one restated predicate per assumption.
- **Deliverables.** The advantage layer; the four assumption predicates in quantitative form; for
  each, a lemma that the perfect predicate is its zero-advantage instance; `Preliminaries/`
  restructured so the perfect and quantitative notions sit side by side rather than one replacing the
  other.
- **Math companion.** The quantitative definitions written beside the perfect ones, so a reviewer can
  see they are the same notion at different resolution.
- **Review requirement (human — Dmitry + Benedikt).** Confirm the quantitative predicates are the
  standard ones, and that every perfect-model theorem is genuinely recovered rather than weakened —
  the zero-advantage lemmas are the evidence, and their absence is a blocker. This issue lifts I8's
  "perfect / probability-free" stance as far as explicit constants and no further, so it carries an
  `INVARIANTS.md` I8 amendment of exactly that width in the same PR.
- **Paper anchor.** ch05 advantages (`Adv^ks_Π`, `Adv^pos_Com`, `Adv^upd_Com`, `Adv^cr_Com`);
  the paper's `negl` statements are deliberately not formalized.

---

## Branch disposition summary (from `docs/branch-analysis.md`)

| Branch | Author | Disposition | Used by |
|---|---|---|---|
| `pr5` | Yavor | **REUSE — best memory base** (Bus-wired, sanity checks, already update-binding) | Issue 1 |
| `memory-integration` | Dmitry | REUSE (abstract-VM full-memory CTE + math-companion), cross-validate | Issue 1 |
| `cr-algorithmic` | Jessica | REUSE as provisional CR variant (keyed/algorithmic) | Issue 8/10 |
| `cost-twostep` | Dmitry | REFERENCE (most complete cost/`Cost.lean` superset) | Issue 6/8/10 |
| `cost-bus-reduction` | Dmitry | REFERENCE (cost combinators, toy) | Issue 6/8 |

All cost/CR branches predate PR #4 — **re-apply hunks, don't merge wholesale** (`CONVENTIONS.md` §4).

Not tracked further (rationale in `docs/branch-analysis.md`): `memory-recon`, `extract-or-collision`,
`yl-memory-reconstruction` (identical Lean to `pr5`), and the deleted `Bus.lean` prototype — git
history only, explicitly not ground truth; Issue 5 redoes it.
