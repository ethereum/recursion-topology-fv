# recursion-topology-fv

Our goal is an end-to-end claim about the security of zkVMs like *"this zkVM provides 128-bit security."* (we are not there yet)

Why is this hard: A zkVM splits execution into segments and uses recursion to joins the segment proofs into one final proof.  Sound individual
proofs are not enough. The pieces must also agree: segment 2 must start where segment 1 ended, and the memory of the VM
must stay consistent. This project proves in Lean4 that all these pieces fit together.

In our v1 release, we study the [**VanillaVM**](./docs/vanillaVM.pdf), a simplified recursion-based zkVM.

This effort corresponds to the [W3 deliverable](https://zkevm.ethereum.foundation/blog/cryptography-research-update) from our zkVM security sprint.

> **Status (v1):** We prove the security of VanillaVM, but some parts of the proof are idealized.
> See [IDEALIZATION.md](IDEALIZATION.md).
>
> TODO for v2:
> - A better model of recursive proof composition.
> - Adversary success probabilities and running times.

----

## Correct-Trace Extractability

*Correct-Trace Extractability* (CTE) is the keystone security property we prove about a zkVM. It informally says: **if the verifier
accepts a proof, then a real execution exists behind it.**

Let's break it down:

A statement `x` claims "the VM goes from initial state A to final state B". CTE holds if there is an
extractor `E`, such that for every statement `x` and every accepting proof `p`, `E` given `(x,p)`, extracts:
- a valid trace: the list of intermediate VM states, step by step;
- a private input, if the VM uses one.

In Lean ([`Specification/Cte.lean`](recursion-topology-fv/Specification/Cte.lean)):

```lean
def CTE : Prop :=
  ∃ E : V.Stmt → V.Proof → V.PrivInput × (ℕ → V.State),
    ∀ (x : V.Stmt) (p : V.Proof), V.verify x p → V.TraceValid x (E x p).1 (E x p).2
```

This is essentially knowledge soundness for a relation that claims that a VM executed correctly (see `cte_iff_knowledgeSound`).

In v1 our extractor is a plain function, with no probabilities or running times.

## Project layout

**Library.** Generic code, shared by every VM.

- `recursion-topology-fv/Preliminaries/`: Generic cryptography, definitions only (argument systems, commitments, traces)
- `recursion-topology-fv/Specification/`: What a zkVM is and what it must prove (CTE)
- `recursion-topology-fv/VMs/*.lean`: Shared VM building blocks (state, memory, ISA, bus)
- `recursion-topology-fv/VMs/NonDeterministic/`: Generic wrapper that adds private input to any zkVM

**Integrated VMs.**

- `recursion-topology-fv/VMs/TwoStep/`: Minimal two-layer VM, with and without a bus
- `recursion-topology-fv/VMs/MultiStep/`: Recursive multi-step VM resembling the VanillaVM recursion architecture
- `recursion-topology-fv/VMs/VanillaVM/`: The [VanillaVM](./docs/vanillaVM.pdf)

Dependencies should point one way: `Preliminaries/` → `Specification/` → `VMs/`.

## Build

```bash
lake exe cache get
lake build
```

Requires the toolchain pinned in `lean-toolchain` and Mathlib `v4.32.0-rc1` (see `lakefile.toml`).
Every PR must keep `lake build` green and satisfy `#print axioms` ⊆ `{propext, Classical.choice,
Quot.sound}`.

## License

Apache License 2.0. See [LICENSE](LICENSE).
