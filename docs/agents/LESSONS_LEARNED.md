# LESSONS LEARNED

Recurring footguns, clustered by theme. **Every lesson carries a guard** — a CI check,
an invariant, or a checklist item — because "a finding without a guard will recur"
(CONVENTIONS.md §8). When a session hits a new recurring problem, add it here with its
guard; when a guard becomes a CI check, note that.

## Lean / build

- **Imports come before the module docstring.** `/-! # … -/` before any `import` is a
  real compile error. Order is: `import …`, blank line, then the module docstring.
  Logged twice in `finality`.
  **Guard:** CONVENTIONS.md §1 (file prologue, fixed order); caught by `lake build` in CI.

- **`autoImplicit` off means every variable is explicit.** A "mysterious" universe or
  type error is often a variable Lean would have auto-bound elsewhere. Declare it.
  **Guard:** `autoImplicit = false` in `lakefile.toml`; do not silence the linter locally.

## Definitions / abstraction (the load-bearing 80%, I1)

- **"Faithful but partial" is a distinct failure mode.** A Lean statement can mean the
  paper statement yet cover only a fragment of it. Review fidelity and completeness
  separately.
  **Guard:** CONVENTIONS.md §6.1.

- **"Needed for this reduction" does not mean logical implication.** The paper
  defines position binding and update binding as independent properties.
  `appendBitVC` proves that the punctured non-equivocation condition plus position
  binding does not imply update binding; it does not prove that update binding
  implies position binding.
  **Guard:** the `def:binding` companion text and the append-bit countermodel;
  reject "strictly stronger" wording unless both implication directions have
  actually been checked.

- **An opaque predicate cannot constrain values absent from its type.**
  `MemFreePredicate` sees only PCs and register files, so it cannot by itself tie a
  separate `MemStep.addr`/`value` field to particular registers. The current
  theorem is therefore a memory-only slice; the ISA layer must add those equations.
  In prose, name this formal type as `MemStep` or a “`MemStep` witness”; the
  generic term “descriptor” is neither a Lean declaration nor paper vocabulary.
  **Guard:** `ISA.System.committedOperation` performs the concrete
  `MemStep`/register/program wiring, and `TwoStep.System.toZkVM.step` is
  `ISA.System.step`; review rejects either a disconnected step predicate
  or generic synonyms for formal witness types.

- **A two-endpoint refinement is not an inductive reconstruction theorem.**
  A lemma that proves the paper's conditional proposition when `CommitInv` is
  supplied for both endpoint states is not enough. A trace extractor additionally
  needs to construct the next full memory and prove `CommitInv` for it from the
  current represented state; assuming that conclusion would hide the
  commitment-swap gap.
  **Guard:** `trace_mem_extract` constructs each represented next state.

- **Agents anchor on training-data analogues for novel-but-familiar notions.** A
  definition that "looks like" a standard one may be silently bent toward the textbook
  version. Novel material (I1) is written interactively or with heavy up-front docs.
  **Guard:** INVARIANTS.md I7; human definition audit (CONVENTIONS.md §6.1).

## Naming / documentation

- **Parallel predicate families get namespaces, not letter suffixes.** `stepC`/`stepF`
  made every reader carry a decoder ring; `CommittedMemory.step` / `FullMemory.step`
  names the state type at each use site, and the type checker already enforces the
  split. Corollary: never `open` such a namespace — opening erases exactly the
  distinction it encodes.
  **Guard:** "use qualified names, do not `open`" notes in `VMs/Memory.lean`; review
  rejects new one-letter variant suffixes on paired declarations (CONVENTIONS.md §1).

- **Comments must survive without the conversation that produced them.** Session-local
  metaphors ("the two worlds") and undefined adjectives ("classified", 12 occurrences)
  read as jargon to a fresh reader — the target reader had to ask what "classified"
  meant. Use paper vocabulary (citable in the `Paper:` line) or describe the mechanism
  ("a case split over the `MemStep` witness"). Same family as the "descriptor" rule
  above.
  **Guard:** docstring review checks vocabulary against the paper and Lean identifiers
  (CONVENTIONS.md §6).

- **A rename's risk lives in the docs, not the Lean.** `lake build` fully verifies the
  code side of a pure rename; drift lands in prose. Update living docs
  (math-companion.md).
  **Guard:** repo-wide grep for the old name before declaring a rename done.

## Vacuity / axioms

- **A theorem with unsatisfiable hypotheses is a bug (I3).** Every headline theorem
  needs a model / instance / counterexample witness (cf. `knowledgeSound_trivialAS`,
  pr5's `appendBitVC_not_updateBinding`).
  **Guard:** vacuity probe in the adversarial-review skill; INVARIANTS.md I3.

- **Axiom set is fixed at `{propext, Classical.choice, Quot.sound}`.** No `native_decide`,
  no new `axiom`, no untracked `sorry`.
  **Guard:** headline `#print axioms` plus the repo-wide source/module hygiene gate in CI
  (INVARIANTS.md I4).

- **The default Lake target is not the whole source tree.** A new `.lean` file that is not
  imported by `recursion-topology-fv.lean` is ignored by bare `lake build`; the umbrella file itself is
  also missed by a `recursion-topology-fv/**/*.lean`-only source glob. Either gap can hide an anonymous
  `sorry` or direct `sorryAx`.
  **Guard:** `scripts/ci_checks.py` inventories the umbrella plus every submodule, explicitly
  builds/imports each discovered module, and self-tests the enumeration.

- **A hygiene scanner must lex non-code, not merely delete comments.** Deleting comments
  shifts diagnostic line numbers, and scanning string literals makes harmless prose such as
  `"sorry"` fail CI.
  **Guard:** the CI lexer blanks nested comments and strings while preserving newlines;
  `--self-test` exercises both behavior and direct-`sorryAx` detection.
