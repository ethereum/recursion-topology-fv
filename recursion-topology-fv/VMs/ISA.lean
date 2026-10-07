import «recursion-topology-fv».VMs.Memory

/-!
# An example Instruction Set Architecture (ISA) for a zkVM

An ISA says what one correct step of a zkVM is: run the instruction at the program counter, and change the VM state as
that instruction specifies. This file defines that step as `System.step`. The VMs in this repo use it as `ZkVM.step`, so
the trace that CTE extracts follows the program.

## The ISA of this example VM

A real ISA, such as RISC-V, has many instructions. This example VM groups them into five
*operation classes*. For example, ADD and SUB are both part of the `arith` class.

A step from `S₁ = (pc₁, regs₁, mem₁)` to `S₂ = (pc₂, regs₂, mem₂)` runs the instruction at `pc₁`,
of class `op := code[pc₁]`. The step is valid when the PC/register requirements of `op` and the
memory equation of `op` both hold:

```text
  class   meaning                        memory equation

  read    read from memory               regs₂[1] = mem₁[regs₁[0]]  and  mem₂ = mem₁
  write   write to memory                mem₂ = mem₁, except mem₂[regs₁[0]] = regs₁[1]
  arith   arithmetic, such as ADD        mem₂ = mem₁
  hash    Keccak or Poseidon hash call   mem₂ = mem₁
  bin     binary/bitwise operation       mem₂ = mem₁
```

The PC/register requirements are `memFreePred op`. They are a parameter of `System`, so this
file does not fix them. For example, the requirements of an ADD can say `pc₂ = pc₁ + 1` and
`regs₂[2] = regs₁[0] + regs₁[1]`. They also see `pc₁`, so they can still tell an ADD from a SUB.

## Main definitions
* `OperationClass` — the five classes.
* `System` — the ISA: `code`, the PC/register requirements, and the maps from register words to
  memory addresses and values.
* `System.operation` — the predicate of one class.
* `System.step` — one of the five `operation` predicates holds.
* `System.committedOperation` — like `System.step`, but memory is a commitment. A read or write
  carries its opening proof in a `MemStep`.
* `System.committedStep` — some `MemStep` passes `committedOperation`.

## Main results
* `System.step_iff_operation_at_pc` — `System.step` holds exactly when the predicate of the
  class `code[pc₁]` holds.
* `System.committedOperation_step` — after memory reconstruction, a step that passes
  `committedOperation` passes `System.step`.
-/

namespace VanillaZkVM
namespace ISA


/-! ## Operation classes and fixed ISA parameters -/

/-- The five operation classes modeled by this formalization.

`hash` represents the hash-call precompiles (Keccak and Poseidon), `arith`
represents arithmetic operations, and `bin` represents binary/bitwise
operations. The separate bus layer can use the `hash` class to identify calls
that must be checked by a hash chip. A value of this type identifies a class,
not an exact decoded instruction. This is an intentional simplification, not a
complete RV32IM opcode enumeration.

Paper: operation taxonomy in ch03. -/
inductive OperationClass where
  | read
  | write
  | arith
  | hash
  | bin
  deriving DecidableEq, Repr

/-- The parameters that interpret the five operation classes. Memory maps `Index` to `Value`: for
example, addresses to bytes, or the index and value types of a commitment scheme. -/
structure System (Index Value : Type) where
  /-- The operation class of the instruction at each program counter. -/
  code : Word → OperationClass
  /-- The PC/register requirements for each operation class. It can use the program
  counter to tell instructions in a class apart. For read and write, it must also enforce the
  address bounds. `operation` adds the class check and the memory equation. -/
  memFreePred : OperationClass → MemFreePredicate
  /-- Interpret the address register as an index in this system's memory. The identity when
  `Index` is `ℕ`. -/
  indexOfWord : Word → Index
  /-- Interpret a register word as a value in this system's memory. The identity when `Value` is
  `ℕ`. -/
  valueOfWord : Word → Value

namespace System

variable {Index Value : Type} (isa : System Index Value)

/-! ## Full operation predicates and the step predicate -/

/-- The full predicate for one operation class.

Every case checks that `code S₁.pc = op`. The read and write cases reuse
`FullMemory.read` and `FullMemory.write`. Register 0 of `S₁` holds the address.
Register 1 holds the value of `S₂` for a read, and of `S₁` for a write. The
remaining cases combine their PC/register requirements with `S₂.mem = S₁.mem`.

The read case also includes `S₂.mem = S₁.mem`. -/
def operation (op : OperationClass) (S₁ S₂ : VMStateWith (Index → Value)) : Prop :=
  isa.code S₁.pc = op ∧
    match op with
    | .read =>
        FullMemory.read (isa.memFreePred .read)
          (isa.indexOfWord (S₁.regs 0)) (isa.valueOfWord (S₂.regs 1)) S₁ S₂
    | .write =>
        FullMemory.write (isa.memFreePred .write)
          (isa.indexOfWord (S₁.regs 0)) (isa.valueOfWord (S₁.regs 1)) S₁ S₂
    | .arith =>
        isa.memFreePred .arith S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem
    | .hash =>
        isa.memFreePred .hash S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem
    | .bin =>
        isa.memFreePred .bin S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem

/-- The step predicate used as `ZkVM.step`. It holds when
one of the five operation-class predicates holds. Each clause checks that the
class matches the instruction at the current program counter.

The VMs in this repo must use this predicate as their `ZkVM.step`; it is not an
additional step relation beside `ZkVM.step`. -/
def step (S₁ S₂ : VMStateWith (Index → Value)) : Prop :=
  isa.operation .read S₁ S₂ ∨
  isa.operation .write S₁ S₂ ∨
  isa.operation .arith S₁ S₂ ∨
  isa.operation .hash S₁ S₂ ∨
  isa.operation .bin S₁ S₂

/-- A step executes exactly the operation class stored in the program at
the current program counter. Thus the disjunction in `step` does not let a
proof choose an unrelated operation: the condition `code S₁.pc = op` in
`operation` fixes the only possible branch.

Paper: instruction selection in `eq:op` and `eq:phiop` (ch01), and the
disjunctive step predicate `eq:step` (ch03). -/
theorem step_iff_operation_at_pc (S₁ S₂ : VMStateWith (Index → Value)) :
    isa.step S₁ S₂ ↔ isa.operation (isa.code S₁.pc) S₁ S₂ := by
  cases hcode : isa.code S₁.pc <;> simp [step, operation, hcode]

/-! ## Connection to committed-memory execution -/

/-- Select the PC/register requirements for the instruction at the current
program counter. Both the committed-memory and full-memory checks use this
helper, so they apply the same non-memory requirements. It does not define a
second VM step.

Paper: the fetch condition in `eq:phiop` (ch01). -/
def selectedMemFreePred : MemFreePredicate :=
  fun pc₁ regs₁ pc₂ regs₂ =>
    isa.memFreePred (isa.code pc₁) pc₁ regs₁ pc₂ regs₂

/-- A committed-memory operation selected by the fixed program.

`CommittedMemory.step` checks the opening proof and the change, or lack of
change, to committed memory. The remaining conditions check that the `MemStep`
case matches `code[pc]` and that its address and value come from the designated
registers. In particular, a proof cannot claim a read when the program calls
for a write, or open a different address from the one in the address register.

The explicit `w` argument is necessary here because read and write values carry
the opening proofs later used to reconstruct full memory. `Bus.System.stepBus`
adds the hash-call and range-check conditions without changing this relation.

Paper: `eq:phi-read-decomp`, `eq:phi-write-decomp` (ch01), and the memory
component of `eq:step-bus2` (ch03). -/
def committedOperation {VC : VectorCommitment}
    (isa : System VC.Index VC.Value)
    (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC) : Prop :=
  CommittedMemory.step isa.selectedMemFreePred Ŝ₁ Ŝ₂ w ∧
    match w with
    | .read addr v _ =>
        isa.code Ŝ₁.pc = .read ∧
        addr = isa.indexOfWord (Ŝ₁.regs 0) ∧
        v = isa.valueOfWord (Ŝ₂.regs 1)
    | .write addr v _ _ =>
        isa.code Ŝ₁.pc = .write ∧
        addr = isa.indexOfWord (Ŝ₁.regs 0) ∧
        v = isa.valueOfWord (Ŝ₁.regs 1)
    | .other =>
        isa.code Ŝ₁.pc = .arith ∨
        isa.code Ŝ₁.pc = .hash ∨
        isa.code Ŝ₁.pc = .bin

/-- The relation between two committed states used by a concrete VM. It holds
when there is some `MemStep` satisfying `committedOperation`. Callers of this
relation do not pass the opening proof explicitly, while segment witnesses keep
that proof so memory reconstruction can use it.

Paper: committed step predicate in `eq:step-bus2` (ch03), without the bus
condition deferred to the bus layer. -/
def committedStep {VC : VectorCommitment}
    (isa : System VC.Index VC.Value)
    (Ŝ₁ Ŝ₂ : CommittedVMState VC) : Prop :=
  ∃ w : MemStep VC, isa.committedOperation Ŝ₁ Ŝ₂ w

/-- Suppose a committed operation is accepted and memory reconstruction checks
the same `MemStep` between the corresponding full states. Then those full
states satisfy `step`. `CommitInv` supplies the fact that each committed
state has the same program counter and registers as its full state.

`TwoStep.System.traceValid_full` uses this theorem to keep opening proofs inside
the extraction argument while making `ZkVM.step` the ordinary fixed-program
execution predicate.

Paper: the committed/full operation correspondence used in
`prop:memory-extractability` and Step 6 of `thm:main` (ch05). -/
theorem committedOperation_step {VC : VectorCommitment}
    (isa : System VC.Index VC.Value)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC)
    (hInv₁ : CommitInv Ŝ₁ S₁) (hInv₂ : CommitInv Ŝ₂ S₂)
    (hcommitted : isa.committedOperation Ŝ₁ Ŝ₂ w)
    (hfull : FullMemory.step isa.selectedMemFreePred S₁ S₂ w) :
    isa.step S₁ S₂ := by
  rw [isa.step_iff_operation_at_pc]
  obtain ⟨hpc₁, hregs₁, _⟩ := hInv₁
  obtain ⟨_, hregs₂, _⟩ := hInv₂
  obtain ⟨_, hmatches⟩ := hcommitted
  cases w with
  | read addr value proof =>
      obtain ⟨hcode, haddr, hvalue⟩ := hmatches
      rw [hpc₁] at hcode
      rw [hregs₁] at haddr
      rw [hregs₂] at hvalue
      refine ⟨rfl, ?_⟩
      simpa [FullMemory.step, FullMemory.read, selectedMemFreePred,
        hcode, haddr, hvalue] using hfull
  | write addr value oldValue proof =>
      obtain ⟨hcode, haddr, hvalue⟩ := hmatches
      rw [hpc₁] at hcode
      rw [hregs₁] at haddr hvalue
      refine ⟨rfl, ?_⟩
      simpa [FullMemory.step, FullMemory.write, selectedMemFreePred,
        hcode, haddr, hvalue] using hfull
  | other =>
      rcases hmatches with hcode | hcode | hcode
      · rw [hpc₁] at hcode
        refine ⟨rfl, ?_⟩
        simpa [FullMemory.step, selectedMemFreePred, hcode] using hfull
      · rw [hpc₁] at hcode
        refine ⟨rfl, ?_⟩
        simpa [FullMemory.step, selectedMemFreePred, hcode] using hfull
      · rw [hpc₁] at hcode
        refine ⟨rfl, ?_⟩
        simpa [FullMemory.step, selectedMemFreePred, hcode] using hfull

end System
end ISA
end VanillaZkVM
