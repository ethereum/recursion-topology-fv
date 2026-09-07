-- Preliminaries: generic cryptography (defs only) and shared helpers.
import VanillaZkVM.Preliminaries.ArgumentSystem        -- frozen: Relation, ArgumentSystem, Extractor, KnowledgeSound
import VanillaZkVM.Preliminaries.ArgumentSystemSanity  -- non-vacuity model for the kernel (trivialAS)
import VanillaZkVM.Preliminaries.VectorCommitment      -- provisional: memory commitment + binding notions
import VanillaZkVM.Preliminaries.HashCommitment        -- provisional: bus commitment + collision resistance
import VanillaZkVM.Preliminaries.Trace                 -- reusable trace concatenation (concatTrace / chain_flatten)

-- Specification: the abstract target the concrete VMs must meet.
import VanillaZkVM.Specification.Zkvm                  -- abstract zkVM system and trace validity
import VanillaZkVM.Specification.Cte                   -- R*, CTE, and CTE ↔ knowledge soundness

-- VMs: concrete machinery and instances.
import VanillaZkVM.VMs.State                           -- Word/Addr/Byte, VM state, committed VM state
import VanillaZkVM.VMs.Step                            -- canonical plain/committed/bus step-interface contract
import VanillaZkVM.VMs.StepSanity                      -- accepting one-step non-vacuity model (private examples)
import VanillaZkVM.VMs.Memory                          -- committed/full-memory step lift and trace reconstruction
import VanillaZkVM.VMs.MemorySanity                    -- satisfiable binding model and append-bit countermodel
import VanillaZkVM.VMs.ISA                             -- representative five-class plain ISA
import VanillaZkVM.VMs.ISASanity                       -- accepted and rejected ISA examples
import VanillaZkVM.VMs.Bus                             -- reusable one-segment bus and chip-proof extraction
import VanillaZkVM.VMs.TwoStep.TwoStep                 -- minimal two-relation zkVM instantiating the abstract one
import VanillaZkVM.VMs.TwoStep.TwoStepSanity           -- accepting model for the full-memory two-step theorem
import VanillaZkVM.VMs.TwoStep.WithBus                 -- connects the reusable bus to the two-layer VM
import VanillaZkVM.VMs.TwoStep.WithBusSanity           -- consistency model for that connection
import VanillaZkVM.VMs.MultiStep.MultiStep             -- binary-recursion-tree zkVM (convert / combine / embed)
import VanillaZkVM.VMs.MultiStep.MultiStepSanity       -- accepting model for the multi-step theorem
import VanillaZkVM.VMs.VanillaVM.VanillaVM             -- recursive zkVM with bus-checked segments and main CTE theorem
import VanillaZkVM.VMs.VanillaVM.VanillaVMSanity       -- accepting model for the assembled theorem

/-!
# VanillaZkVM — umbrella module

The development is layered `Preliminaries → Specification → VMs`, and the imports
above are grouped accordingly. Every arrow in the module graph points up that
list; there are no back-edges.

* `Preliminaries/` — scheme-independent cryptography, definitions only, plus its
  I6 consistency floor and the generic trace-concatenation helper.
* `Specification/` — what a zkVM is and what it must prove (the frozen kernel:
  `ZkVM`, `TraceValid`, `Rstar`, `CTE`, `cte_iff_knowledgeSound`).
* `VMs/` — concrete VM machinery: state vocabulary, the step-interface contract,
  committed-memory reconstruction, the representative ISA, the per-segment bus,
  the two-step variants, the multi-step recursion tower, and the final
  recursive VM with bus-checked segments that instantiate the specification.
-/
