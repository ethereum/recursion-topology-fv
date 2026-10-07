# INVARIANTS — the project constitution

These are the non-negotiable rules for the lean-vanillavm formalization. They hold at **all**
times; changing any of them requires explicit human sign-off (a PR that edits this file, approved
by at least one of Benedikt/Dmitry). Both humans and agents check work against this list, and cite
the invariant number (I1, I2, …) when a decision depends on it. Modeled on the `finality` repo's
`INVARIANTS.md`.

- **I1 — Definitions are load-bearing; polish them, not the proofs.** ~80% of review effort goes
  into a small set of **core definitions** (`KnowledgeSound`, `CTE`, the abstract `ZkVM`,
  commitment binding notions, and the reduction/advantage vocabulary). Helper lemmas and proof
  internals matter only insofar as they type-check and are non-vacuous (I3); they may be
  produced/refactored freely.

- **I2 — Minimal public surface; everything derives from the abstract.** Each new module exposes
  the **smallest possible** set of new public definitions (state the count in the PR). Every VM
  variant is an *instance* of the abstract `ZkVM`; every concrete relation/argument-system is
  *derived* from `Relation`/`ArgumentSystem`; every security property is stated via the core
  definitions (I1). Anything not needed by another module is `private` or `local`. A new public
  definition that merely re-states an abstract one is a review blocker. In particular,
  `ZkVM.step` is the canonical plain-step predicate: later ISA code supplies that field rather than
  declaring a disconnected top-level relation.

- **I3 — Non-vacuity is mandatory.** Every headline theorem must be accompanied by evidence its
  hypotheses are satisfiable — a model, an instance, or a concrete counterexample witness (as in
  `knowledgeSound_trivialAS`, the accepting model in `VMs/TwoStep/TwoStepSanity.lean`, and pr5's
  `appendBitVC_not_updateBinding`). A theorem whose assumptions jointly imply `False` is treated as
  a bug. Every PR runs the vacuity check (see `agents/CONVENTIONS.md`).

- **I4 — Axiom hygiene, CI-checked.** The permitted axiom set is `{propext, Classical.choice,
  Quot.sound}`. There is currently no `sorry`/`admit` allowlist: no `sorry`, `sorryAx`, `admit`,
  `native_decide`, or new `axiom` is permitted in project source. A future exception requires an
  explicit amendment and a machine-checked allowlist, not PR prose alone. `#print axioms <headline
  theorem>` is part of every PR.

- **I5 — Crypto is idealized "perfect/probability-free" until deliberately lifted.** See IDEALIZATION.md.

- **I6 — Legible and compact.** The final set of public definitions plus the main theorems must be
  human-readable and not materially longer than the paper's statements. Redundancy introduced by
  agents is a defect (see the anti-duplication rule in `agents/CONVENTIONS.md`). Target: the whole
  development stays on the order of a couple thousand lines.

- **I7 — Autonomy contract.** An agent session may run unsupervised only if: it starts from a
  named bootstrap and a fresh read of this file + `agents/CONVENTIONS.md`; the
  build is green (`lake build`) at start and end; and it closes with an audit (`agents/CONVENTIONS.md`
  review checklist) and an axiom/`sorry` ledger diff. Novel
  material (I1) is done interactively or with extensive up-front documentation, because agents
  anchor on training-data analogues for novel-but-familiar-looking notions.
