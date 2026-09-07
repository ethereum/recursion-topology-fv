# Issue 1 — memory reconstruction

This note gives a human-readable overview of the memory-reconstruction
formalization. It is intended to guide review of the definitions and theorem
statements; the line-by-line paper correspondence remains in
[`CORRESPONDENCE.md`](CORRESPONDENCE.md), and the ordinary mathematical
statements remain in [`math-companion.md`](math-companion.md).

## `Preliminaries/VectorCommitment.lean`

The goal of the Issue 1 additions is to define `UpdateBinding`. If `m'` is `m`
updated at one address, and the same opening proof verifies the old value
against `commit m` and the new value against a candidate commitment `C'`, then
`C'` must equal `commit m'`. This prevents accepted commitments after a write
that do not represent the correctly updated memory.

- **Position binding.** If two openings at the same address verify against the
  same commitment, then they reveal the same value.
- **Update binding.** Consider memories `m` and `m'`, a fixed address `addr`,
  and a new value `x`. Suppose that `m'` equals `m` everywhere except at
  `addr`, where its value is `x`. If the same opening proof verifies the old
  value against `commit m` and `x` against a candidate updated commitment
  `C'`, then `C' = commit m'`.

## `VMs/Memory.lean`

The goal of this file is to prove `trace_mem_extract`. Assuming completeness,
position binding, and update binding, a committed trace with valid
committed-memory steps can be reconstructed from a known full initial state
into a full-memory trace. Every reconstructed state corresponds to its
committed state under `CommitInv`, and every reconstructed step satisfies
the corresponding full-memory predicate `FullMemory.step`. The private theorem
`reconstructed_step_full` proves the full-memory semantics of one reconstructed
step. The public theorem `step_reconstruct_exact` retains the same `MemStep` in
its conclusion so that the ISA can check it against `code[pc]`, while
`step_reconstruct` hides that witness for the memory-only interface.

- `FullVMState` represents states containing the complete memory map.
- `CommitInv Ŝ S` means that committed-memory state `Ŝ` represents
  full-memory state `S`: their program counters and registers agree, and
  `Ŝ.mem = commit S.mem`. Equivalently, `Ŝ` is obtained from `S` by replacing
  the full memory map with its commitment and leaving the program counter and
  registers unchanged. Reconstruction proves this relation at every trace
  position, which is why it is called an invariant.
- `MemStep` makes the memory behavior implicit in an instruction explicit:
  - a read contains an address, a value, and an opening proof;
  - a write contains an address, the new value, the old value, and an opening
    proof;
  - other instructions carry no additional memory data.
- `CommittedMemory.read` and `CommittedMemory.write` describe correct reads and
  writes between committed-memory states.
- `FullMemory.read` and `FullMemory.write` describe the corresponding operations
  between full-memory states.
- `CommittedMemory.step` is the committed-memory step predicate, case-split
  over reads, writes, and other instructions.
- `committedStep` says that some `MemStep` passes the memory checks. It lets a
  caller relate two committed states without supplying that value explicitly.
  A concrete VM adds its program checks before exposing the relation through
  `StepInterface`.
- `FullMemory.step` is the corresponding full-memory step predicate, case-split
  over the same witness.
- `step_mem_extract` assumes `CommitInv` for both endpoint states. It proves
  that a `CommittedMemory.step` also satisfies `FullMemory.step`. Because it
  assumes the representation relation for the second state, it cannot itself
  be used to reconstruct a trace.
- `commit_update` shows that a candidate commitment after a write is the
  commitment to the point-updated memory. It uses the old and new accepted
  openings, position binding, and update binding.
- `commitInv_write` proves that a reconstructed correct write preserves
  `CommitInv` from the state before the write to the state after it.
- `stepReconstruct` constructs the next full-memory state from the current
  full-memory state, the next committed-memory state, and a `MemStep` witness.
- `reconstructTrace` applies `stepReconstruct` inductively to reconstruct the
  complete full-memory trace from the committed states and initial full state.
- `commitInv_step` proves that the reconstructed full-memory state is related
  to the corresponding committed-memory state by `CommitInv`.
- `reconstructed_step_full` proves that the reconstructed state satisfies
  the full-memory semantics of the same `MemStep` witness.
- `step_reconstruct_exact` takes a particular `MemStep` and constructs the next
  represented full state while proving `FullMemory.step` for that same value.
  Retaining it is what lets the ISA layer prove that the reconstructed step
  agrees with the operation selected by the program.
- `step_reconstruct` realizes `StepInterface.MemoryBridge`: from
  `CommitInv Ŝ₁ S₁` and `committedStep … Ŝ₁ Ŝ₂`, it constructs a full state
  `S₂` and `MemStep` witness `w` such that both
  `CommitInv Ŝ₂ S₂` and `FullMemory.step S₁ S₂ w` hold.
- `trace_mem_extract` chains the preceding result, by induction, across a
  sequence of committed-memory states. The reconstructed states satisfy both
  `CommitInv` and the full-memory step predicate at every index in the trace.

## `VMs/MemorySanity.lean`

The goal of this file is to show that the memory assumptions are coherent,
non-vacuous, and necessary.

- `exactVC` is a concrete vector-commitment scheme satisfying completeness,
  position binding, and update binding. The file also checks a write that
  changes one value from `false` to `true`, rather than only a no-op step.
- `appendBitVC` is a counterexample scheme satisfying completeness and position
  binding. It also satisfies the earlier away-from-the-updated-address
  condition: if one proof is accepted at the updated address under two
  commitments, accepted openings at any other address reveal the same value.
  Nevertheless, it fails update binding because it accepts a commitment that
  is not the commitment of any full memory.
- `appendBitBreak` is a concrete `UpdateBindingBreak`, and
  `appendBitBreak_wins` proves that it satisfies `IsUpdateBindingBreak`.
- The `MemoryBridge` counterexample shows why the failure matters: an initial
  full-memory state can represent the first committed-memory state and the
  committed-memory write can be accepted, while no full-memory state represents
  the second committed-memory state.

## `VMs/TwoStep/TwoStep.lean`

The goal of this file is to integrate memory reconstruction and the
representative ISA into a minimal two-layer zkVM. Knowledge soundness of the
final and segment argument systems extracts and flattens a valid committed-state
trace, proving `committedTrace_extract`. The memory results reconstruct a
full-memory trace, while the ISA bridge proves that each reconstructed step
executes the operation selected by `code[pc]`. This file proves CTE for the
two-layer toy without bus checks. `VMs/TwoStep/WithBus.lean` reuses this memory
result after `VMs/Bus.lean` has checked each segment bus. The bus theorem does
not choose how segment proofs are combined; the recursive proof layers are
still separate.

- `SegStmt` and `SegWitness` describe a segment's committed boundaries,
  intermediate states, and explicit `MemStep` witnesses.
- `FinalStmt` and `FinalWitness` describe the whole committed execution through
  chained segment boundaries and proofs.
- `FinalStmtFull` carries the corresponding full-memory boundaries, and
  `toCommitted` commits such a boundary state.
- `System` packages the commitment scheme, representative ISA, and verifier
  interfaces for the two-layer toy system.
- `RSeg` requires the segment boundaries to match and every explicit
  `MemStep` witness to satisfy `ISA.System.committedOperation`, which checks
  both the committed memory equations and agreement with `code[pc]` and the
  designated registers.
- `RFinal` requires the outer boundaries to match and every chained segment
  proof to verify.
- `CommittedTraceValid` states validity of a committed-state trace. It is a plain
  predicate, not a second `ZkVM`: the committed layer is an extraction
  intermediate, not a machine we make security claims about.
- `toZkVM` is the file's only instance of the frozen abstract `ZkVM`,
  with `ISA.System.stepPlain` as its full-memory step semantics.
- `memoryStepInterface` fills the frozen step interface for this VM, and
  `memoryBridge` uses `step_reconstruct_exact` to produce the next represented
  state and `committedOperation_stepPlain` to prove its ordinary `ZkVM.step`.
- `traceValid_full` turns a valid committed trace into a valid reconstructed
  full-memory trace with the correct endpoints.
- `committedTrace_extract` is the SNARK half: two-layer straight-line extraction
  yields a valid committed trace for every accepting final proof.
- `cte` composes the two halves into correct-trace extractability for
  the toy zkVM.

## `VMs/TwoStep/TwoStepSanity.lean`

The goal of this file is to show that all hypotheses of `cte` can hold
simultaneously in a concrete system. It constructs a one-segment, one-step
system over `exactVC`, uses relation witnesses as proofs with identity
extractors, exhibits an accepted final proof, and derives full-memory CTE. All
declarations are private, so the file adds no public API.

## Scope

Issue 1 establishes the committed-memory-to-full-memory bridge, and Issue 3
connects that bridge to the representative five-class ISA. Issue 5 reuses this
toy inside a separate segment-bus layer. The `convert`/`combine`/`embed`
recursion tower remains a separate issue, so this result must not be presented
as the complete Vanilla VM security theorem.
