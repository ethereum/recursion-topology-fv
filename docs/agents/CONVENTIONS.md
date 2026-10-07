# CONVENTIONS — how we write code, use agents, and review

This file is binding for every branch merged into `main`. Rules that are
*constitutional* live in [`INVARIANTS.md`](../INVARIANTS.md); this file is the day-to-day operational
layer.

---

## 1. Lean style (inherited from VCVio + our current code)

- **File prologue, fixed order:** module docstring `/-! # Title … -/` first? No — **imports come
  before any docstring** (a real compile error otherwise; `finality` logged this twice). Order:
  `import …`, blank line, then the module docstring `/-! # … -/`.
- **Module docstring** opens with `# Title`, a short paragraph, then `## Main definitions` /
  `## Main results` bullet lists that *name* the key declarations without restating them. Our
  `Specification/Cte.lean` and `VMs/Memory.lean` already do this — match that density.
- **Section headers use `/-! ## Title -/` doc-comments, never ASCII banners** (`-- ====`). If a
  section is big enough to want a loud header, it usually wants its own `namespace` or file.
- **Naming (Mathlib convention):** types/structures/classes `UpperCamelCase`; term-level functions
  `lowerCamelCase`; theorems/lemmas `snake_case` in `{head}_{op}_{rhs}` form
  (`cte_iff_knowledgeSound`, `chain_flatten`). **Names mirror the paper's vocabulary** — no
  invented jargon (`finality` enforces this in review).
- **Declaration docstrings are ahistorical.** Describe *what a definition is / what a theorem
  states*. Never write "renamed from", "replaces X", "previously" — docstrings are read cold.
  (VCVio hard rule.)
- **`structure`, not `class`, for data/interfaces.** Abstract objects (`ZkVM`, `VectorCommitment`,
  a future `Reduction`) are plain `structure`s parameterized over their abstract pieces — matching
  both our code and VCVio/finality. Reserve typeclasses for genuine ambient capabilities, scoped as
  narrowly as possible (one `variable`/`section` per group of lemmas that truly share it).
- **`autoImplicit` stays off** (already set in `lakefile.toml`). Every variable explicit. Never
  silence a linter locally to dodge a warning; if an exception is truly needed, comment why.
- **One namespace per file/topic**, matching the file's main definition
  (`namespace VanillaZkVM … namespace TwoStep …`).
- **Adversaries/reductions are plain functions**, and efficiency is a *separate predicate* applied
  to them — never a field bundled into the adversary type (VCVio).
- **Scaffolding that is intentionally unused-yet is marked in its docstring** ("retained as
  scaffolding"), not deleted and not silently left dangling (VCVio pattern).

## 2. Minimal-surface & anti-redundancy rules (I2, I6)

- **Declare your new public surface in the PR.** List every new *public* definition and justify why
  it can't be `private` or derived from an abstract one. Reviewers reject public defs that
  duplicate an abstract notion.
- **Derive, don't re-state.** New VM = instance of `ZkVM`. New relation = built via `Relation`. New
  security property = phrased with the core definitions (I1). If you find yourself copying the
  shape of `KnowledgeSound`/`CTE`, stop — you almost certainly want to instantiate, not fork.
- **One canonical step chain.** `ZkVM.step` is `ISA.System.step`. The committed step
  `ISA.System.committedStep` and the bus step `Bus.System.stepWithBus` connect to it only through
  theorems (`Bus.System.stepWithBus_committedOperation`, `ISA.System.committedOperation_step`,
  `trace_mem_extract`). Do not introduce a parallel public binary "step" relation in a convenience
  module.
- **Anti-duplication protocol (Hicks trick):** before writing a new helper, search for an existing
  one (`Grep`, and read the docstrings in `Preliminaries/`/`Specification/`). If an agent produces a
  duplicate, the fix is: point it at the canonical definition, and have it add/extend a short
  `docs/reuse-notes.md` entry ("to do X, use `Y` in `Z.lean`"). That note then prevents recurrence.
- **Compactness is a review target (I6):** the public defs + main theorems must not be materially
  longer than the paper. Run `/simplify` (the reuse/simplification skill) on your diff before
  opening the PR and note what it changed.

## 3. Reductions & idealization (I5)

- Stay in the **perfect / probability-free** model. Do not import VCVio. Do not add `λ`/`negl`/
  running-time.
- Model reductions **lightweight**: state each layer's guarantee as an implication from named
  assumptions, and collect those assumptions in one trust-base structure per system — the pattern
  `TwoStep.System.Assumptions` sets. In the perfect model that *is* the reduction: there is no
  probabilistic bad event to exhibit, so routing it through a break-witness adds vocabulary without
  adding content. Break-witness records such as `UpdateBindingBreak` remain welcome where they let a
  countermodel name a concrete violation.
- When advantage bookkeeping is eventually added, follow the
  VCVio *pattern* (not the code):
  advantage is a plain numeric function decoupled from game shape; a reduction is a concrete
  `def : Adv → Adv'`; the theorem is a `≤` inequality; composition is generic lemmas. Design so a
  later swap to VCVio's `SecurityGame`/`Negligible` is mechanical.
- Running time stays a placeholder until explicitly scoped. Keep reductions a *finite composition
  of finitely many sub-adversaries* so the eventual cost is a finite sum (Hicks).

## 4. Git / branch workflow

- **Branch per issue**, named `<issue-slug>` (e.g. `memory-twostep`, `recursion-multistep`),
  branched from `main`, PR'd back into `main`.
- Keep `lake build` green at the start and end of every session (I7). Commit messages are
  imperative and cite the issue.
- Do not commit or push unless a human asks. Never skip hooks or bypass signing.

## 5. Skills to use (Claude Code)

| Skill / command | When |
|---|---|
| `/simplify` | Before every PR — reuse/simplification/efficiency cleanup on the diff (enforces I2/I6). |
| `/code-review` | On your own working diff before requesting human review — catches bugs the reviewer shouldn't have to. |
| `/security-review` | On any branch that touches a security *definition* or a reduction. |
| [adversarial-review](adversarial-review.md) (see §6) | Session-end audit. |
| `/init`, reuse-notes | When onboarding a new subsystem; keep `docs/reuse-notes.md` current. |

Model guidance (Hicks + cost): use the strong interactive model for **definitions and theorem
statements** (novel material — I1/I7); delegate proof-hole filling, mechanical refactors, and
large-repo reading to cheaper models / background subagents, and have them **write their output to
a file** for pickup.

## 6. Review process (per-task; NOT fully delegatable)

Every PR gets appropriate human review whose core is **not delegatable to an agent** (the reviewer
must understand the notions). The standing checklist:

1. **Definition audit (the 80%).** Read every *new public definition* and the *headline theorem
   statement*. Confirm the abstraction is the *right* one — e.g. "is this really update-binding?",
   "does this `CTE` instance quantify the trace the way the paper does?". This is the load-bearing
   human act (I1). Check fidelity **and** completeness — beware "faithful but partial".
2. **Non-vacuity (I3).** Confirm the theorem's hypotheses are satisfiable (model / instance /
   counterexample witness present) and that no two assumptions jointly imply `False`. Ask an agent
   to *attempt* to derive `False` from the assumption bundle as a probe.
3. **Surface & redundancy (I2/I6).** Confirm the new public surface is minimal and justified, and
   that nothing duplicates an abstract notion.
4. **Axioms (I4).** `#print axioms <headline>` shows only the permitted set; the repo-wide hygiene
   gate reports no `sorry`, direct `sorryAx`, `admit`, `native_decide`, or new `axiom`.
5. **Legibility.** Names match paper vocabulary; proofs comment *why* at branch points.

Adversarial-review skill (session end, from `finality`): fan out independent skeptics along named
dimensions — (a) soundness/vacuity, (b) kernel-truth re-verification (`#print axioms`, rebuild),
(c) gate/CI integrity, (d) docs/overclaim — each blind to the others, then triage to CONFIRMED vs
SUSPECTED (a finding is real only once reproduced). Any probe an agent injects (a weakened
assertion) must be reverted and `git status` re-checked clean.

## 7. Math companion (required deliverable, every issue)

Every issue produces or extends `docs/math-companion.md` — the pen-and-paper statements that
match the Lean, kept in lockstep (the precedent Dmitry set on the `memory-integration` branch). For
each new public definition or headline theorem, the companion states it in ordinary mathematical
notation with the paper citation, so a reviewer can compare *paper ↔ companion ↔ Lean* without
reading proof internals. A PR that adds Lean definitions without updating the companion is
incomplete. The companion and the Lean must agree; discrepancies are review blockers.

## 8. Lessons

- **Lessons:** recurring footguns go in `docs/agents/LESSONS_LEARNED.md`, clustered by theme, each with a
  **guard** (a CI check, an invariant, or a checklist item) — "a finding without a guard will
  recur".
