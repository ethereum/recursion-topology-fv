import «recursion-topology-fv».Preliminaries.VectorCommitment

/-!
# VM state

The state vocabulary shared by every concrete VM: machine words, byte-addressed
memory, and the Lean structure that groups a program counter, registers, and
memory into one VM state.

The commitment-native full state `FullVMState` and the representation relation
`CommitInv` tying the two together live in `Memory.lean`.
-/

namespace VanillaZkVM

/-- A 32-bit machine word (abstracted as `ℕ` for now). -/
abbrev Word : Type := ℕ

/-- A VM state with memory representation `Mem`.

Paper: ch01, section “Program, Execution, and VM State.” -/
structure VMStateWith (Mem : Type) where
  /-- The program counter. -/
  pc : Word
  /-- The register file: register index to word value. -/
  regs : ℕ → Word
  /-- The memory. -/
  mem : Mem

/-- Committed VM state `Ŝ = (pc, regs, mem̂)`: memory replaced by a commitment.

Paper: ch02, section “Execution Segments,” and ch03 `eq:step-bus2`. -/
abbrev CommittedVMState (VC : VectorCommitment) : Type := VMStateWith VC.Com

end VanillaZkVM
