import «recursion-topology-fv».VMs.ISA
import «recursion-topology-fv».Specification.Zkvm

/-!
# Sanity checks for the representative ISA operation classes

These private examples demonstrate both accepted and rejected steps. They cover
an accepted read, an accepted write whose output memory differs from its input,
rejection when the program contains a different operation class, and rejection
when a write produces the wrong memory. A private `ZkVM` instance also checks
that `ISA.System.step` can be used directly as its `step` field.

Nothing in this file adds to the public API or asserts concrete cryptographic
security.
-/

namespace VanillaZkVM
namespace ISASanity

/-- A byte-addressed memory address. -/
private abbrev Addr : Type := ℕ
/-- A byte stored in memory. -/
private abbrev Byte : Type := ℕ

/-- The paper's byte-addressed VM state `S = (pc, regs, mem)`. -/
private abbrev VMState : Type := VMStateWith (Addr → Byte)

private def systemFor (op : ISA.OperationClass) : ISA.System Addr Byte where
  code := fun _ => op
  memFreePred := fun _ _ _ _ _ => True
  indexOfWord := id
  valueOfWord := id

private def zeroState : VMState :=
  ⟨0, fun _ => 0, fun _ => 0⟩

private theorem accepts_read :
    (systemFor .read).step zeroState zeroState := by
  simp [ISA.System.step, ISA.System.operation, systemFor,
    FullMemory.read, zeroState]

private def writeRegisters (i : ℕ) : Word :=
  if i = 1 then 1 else 0

private def writeMemory (i : Addr) : Byte :=
  if i = 0 then 1 else 0

private def beforeWrite : VMState :=
  ⟨0, writeRegisters, fun _ => 0⟩

private def afterWrite : VMState :=
  ⟨0, writeRegisters, writeMemory⟩

private theorem accepts_changed_write :
    (systemFor .write).step beforeWrite afterWrite := by
  simp [ISA.System.step, ISA.System.operation, systemFor,
    FullMemory.write, beforeWrite, afterWrite, writeRegisters, writeMemory]

private theorem rejects_wrong_fetch :
    ¬(systemFor .write).operation .read zeroState zeroState := by
  simp [ISA.System.operation, systemFor]

private theorem rejects_incorrect_write_result :
    ¬(systemFor .write).operation .write beforeWrite beforeWrite := by
  simp [ISA.System.operation, systemFor, FullMemory.write, beforeWrite,
    writeRegisters]

private def readZkVM : ZkVM where
  State := VMState
  step := (systemFor .read).step
  T := 1
  Stmt := VMState × VMState
  PrivInput := Unit
  initial := fun x _ => x.1
  terminal := fun x _ => x.2
  Proof := Unit
  verify := fun x _ => (systemFor .read).step x.1 x.2

private theorem concrete_zkVM_uses_step :
    readZkVM.step zeroState zeroState :=
  accepts_read

end ISASanity
end VanillaZkVM
