# Step-interface contract

This is the Issue 0 interface shared by the memory, ISA, and bus work. It was
added as a bounded PLAN amendment accepted by Dmitry on **2026-07-29**.

The contract prevents later issues from growing unrelated predicates all called
"step." It fixes the semantic direction of the two bridge arguments while
leaving their concrete operation and witness types to their owning issues.

## Canonical interfaces

The Lean declaration `StepInterface V` has the following fields:

```text
V.step
  : V.State -> V.State -> Prop

represents
  : CommittedState -> V.State -> Prop

stepCommitted
  : CommittedState -> CommittedState -> Prop

```

`V.step` is the single canonical **plain** step predicate. Issue 3's
`ISA.System.stepPlain` is the predicate assigned to that field by a concrete
Vanilla `ZkVM`; it must not become a second, disconnected top-level execution
relation. `TwoStep.System.toZkVM` makes this assignment in the public two-layer
toy, and `VanillaVM.System.toZkVM` reuses it in the assembled recursive VM.

`stepCommitted` relates two committed states. Operation-specific data and
opening proofs may be carried by internal predicates. In the two-layer toy,
`ISA.System.committedOperation` checks the explicit `MemStep` against the
program-selected operation. `ISA.System.committedStep` then says that some such
`MemStep` exists, so callers of the public relation need not pass it explicitly.

Issue 5 separately supplies

```text
stepWithBus
  : CommittedState -> CommittedState -> BusEvidence -> Prop
```

where `BusEvidence` contains one segment's bus and the memory-opening data for
one transition. Before the bridge is used, `Bus.System.segment_extract` proves
that the step, Keccak, Poseidon, and range proofs all refer to that same segment
bus. This theorem is independent of how segment proofs are later combined.
`stepWithBus` then requires both the step check and all three chip checks. The
reusable `stepWithBus_committedOperation` theorem derives the canonical
committed ISA operation for the same recovered `MemStep`; a concrete VM uses
that same value to prove the weaker `BusBridge` statement that a suitable
`MemStep` exists.
Keeping the bus predicate out of `StepInterface` lets Issue 1 instantiate the
memory interface without inventing unused bus data.

## Frozen bridge statements

For `I : StepInterface V`, the memory bridge is

```text
I.MemoryBridge :=
  forall committed states C1 C2 and plain state S1,
    represents C1 S1 ->
    stepCommitted C1 C2 ->
    exists S2,
      represents C2 S2 and V.step S1 S2.
```

The existentially produced `S2` is essential. A lemma that merely assumes
`represents C2 S2` and concludes `V.step S1 S2` does not establish the
representation relation needed to reconstruct a whole trace; this is precisely
the gap exposed by examples where verification accepts `C2` even though no
full state `S2` represents it.

Put differently, the bridge must construct a state `S2` corresponding to `C2`;
it may not ask the caller to provide that state and prove the correspondence in
advance.

The bus bridge is

```text
I.BusBridge stepWithBus :=
  forall C1 C2 and bus evidence b,
    stepWithBus C1 C2 b ->
    stepCommitted C1 C2.
```

For one segment, the step, Keccak, Poseidon, and range-proof extractors each
return a bus. All four buses have the same committed digest, so collision
resistance proves that they are equal. Different segments have separate bus
commitments and may use different buses; the proof neither compares nor
equates them.

## Ownership

| Layer | Designated module | Required realization |
|---|---|---|
| Memory reconstruction | `VanillaZkVM/VMs/Memory.lean` + concrete VM module (Issue 1 / #7) | `VMs/Memory.lean` defines `CommitInv`, the memory-only step predicates, `step_reconstruct_exact`, `step_reconstruct`, and `trace_mem_extract`. The concrete VM packages the appropriate committed relation as a `StepInterface` and proves `MemoryBridge`; `VMs/TwoStep/TwoStep.lean` supplies the current instance. |
| Plain ISA semantics | `VanillaZkVM/VMs/ISA.lean` (Issue 3 / #9) | Define `ISA.System.stepPlain`, connect explicit committed-memory witnesses through `ISA.System.committedOperation`, and assign `stepPlain` directly to both the toy and assembled `ZkVM` instances. |
| Segment bus | `VanillaZkVM/VMs/Bus.lean` + concrete VM connection modules (Issues 5 and 7) | `Bus.System.stepWithBus` combines the segment step check with the three chip checks. `Bus.System.stepWithBus_committedOperation` proves the implication to the Issue 3 committed ISA operation while preserving the recovered `MemStep`, and `Bus.System.segment_extract` proves that the four buses recovered for one segment are equal. Neither theorem chooses how segments are combined. `VMs/TwoStep/WithBus.lean` demonstrates the non-recursive connection; `VMs/VanillaVM/VanillaVM.lean` derives the recursive leaf extractor from the same segment theorem. |

No other module should introduce a different, unrelated public execution
predicate between two states.
Internal helper predicates with additional witness arguments are permitted, but
the module must expose them through this contract.

Issue 0 contains the proposition definitions rather than unproved theorem
stubs: I7 forbids `axiom`/`sorry`, and I5 forbids duplicating `ZkVM.step`.
Concrete theorem bodies remain the owning issues' deliverables.
