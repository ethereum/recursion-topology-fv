# Vanilla zkVM — Lean formalization

A Lean 4 / Mathlib formalization of the **Vanilla zkVM** and its main security result, ported from
the Ethereum Foundation zkVM whitepaper example (`zkvm-whitepaper/sampleVM/`, chapters ch01–ch05).
The goal is to formalize **correct-trace extractability (CTE)** — that an accepting final proof lets
an extractor recover a full, valid execution trace — for a recursive zkVM with committed memory and
a bus, reducing security to explicit cryptographic hardness assumptions.

The exact paper source used for review is pinned in
[`docs/PAPER_REVISION.md`](docs/PAPER_REVISION.md); this matters because the default paper branch and
its corrected `proof` revision currently differ on whether the step count `T` is adversary-chosen.

> **Status: WIP.** The current core is small, clean, and axiom-clean, but idealized (see
> [Idealization](#idealization)). The path from here to the full theorem is [`docs/PLAN.md`](docs/PLAN.md).

---

## Current architecture

```
VanillaZkVM/
├── Preliminaries/                 generic cryptography — definitions only
│   ├── ...
├── Specification/                 what a zkVM is, and what it must prove
│   ├── Zkvm.lean                    abstract ZkVM + TraceValid
│   └── Cte.lean                     R*, CTE, and the keystone cte_iff_knowledgeSound
└── VMs/                           concrete VM machinery and instances, one subdirectory per VM
    ├── ...
    └── VM1/
        ├── ..
```

Dependencies point one way: **`Preliminaries/` → `Specification/` → `VMs/`.**

**`Preliminaries/`** holds everything that does not mention a virtual machine: argument systems and
what it means for one to be knowledge-sound, the memory and bus commitments with their binding
properties, and a couple of generic helpers. Definitions only — the proofs that consume them live
downstream.

**`Specification/`** states what we are trying to prove, once and abstractly. A zkVM is a state type
with a step relation, a step count, and a final verifier; it is *correct-trace extractable* when every
accepting proof can be turned into a valid execution reaching the claimed final state. Crucially this
layer knows nothing about memory commitments or instruction sets, which is what lets one definition
serve every VM.

**`VMs/`** holds the concrete machinery — VM states, the contract linking plain execution to
committed-memory execution, and the reconstruction of full memory from committed memory — plus one
subdirectory per concrete VM. Each such VM is an *instance* of the abstract zkVM above and proves
correct-trace extractability for itself, rather than restating the definition.

The concrete VM variants currently implemented are:

- **TwoStep without a bus** ([`TwoStep.lean`](VanillaZkVM/VMs/TwoStep/TwoStep.lean)):
  a deliberately minimal, non-recursive two-layer VM using the representative
  five-class ISA.
- **TwoStep with a bus** ([`WithBus.lean`](VanillaZkVM/VMs/TwoStep/WithBus.lean)):
  the same two-layer proof structure, with separate step, Keccak, Poseidon, and
  range proofs for each segment. Each segment keeps its own bus.
- **MultiStep without a bus**
  ([`MultiStep.lean`](VanillaZkVM/VMs/MultiStep/MultiStep.lean)): the recursive
  convert/combine/embed proof structure over an abstract segment proof.
- **Assembled Vanilla VM**
  ([`VanillaVM.lean`](VanillaZkVM/VMs/VanillaVM/VanillaVM.lean)): the recursive
  proof structure in which every base segment is checked through the segment
  bus.

Concrete opcode semantics are still to come.

Each `*Sanity.lean` file holds concrete models and countermodels witnessing that the definitions
beside it are satisfiable and the theorems consuming them non-vacuous — kept separate so the
definition files stay definitions-only.

The representative five-class ISA is documented in
[`docs/ISA.md`](docs/ISA.md).
The segment-bus construction is described mathematically in
[`docs/math-companion.md`](docs/math-companion.md).

## Idealization

The crypto layer is **perfect / probability-free**.
Currently, cryptographic building blocks are idealized as *perfect* to simplify everything.
For instance, collision-resistance is just defined as being injective; knowledge
soundness is `∃ extractor, ∀ accepting (x,p), witness valid`. There is no security parameter, no `negl`, no running time yet.
The paper itself flags a deeper caveat (`rem:idealized`): straight-line
extraction composed across recursion layers needs "relativized" SNARKs, which provably don't exist,
so even the paper's bounds validate reduction **structure**, not a concrete security level.

We are of course aware that this is far from being cryptographically accurate, and we may change this in the future.



## Build

```bash
lake exe cache get
lake build
```

Requires the toolchain pinned in `lean-toolchain` and Mathlib `v4.32.0-rc1` (see `lakefile.toml`).
Every PR must keep `lake build` green and satisfy `#print axioms` ⊆ `{propext, Classical.choice,
Quot.sound}`.

## Contributing
TBD
