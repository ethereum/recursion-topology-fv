# Vanilla zkVM whitepaper — structural digest for Lean formalization

Source: the canonical files `sampleVM/ch00-overview.tex`,
`ch01-execution-model.tex`, `ch02-segmentation.tex`,
`ch03-correct-execution.tex`, `ch04-proof-architecture.tex`,
`ch05-security.tex`, and `macros.tex`, at the revision pinned in
`docs/PAPER_REVISION.md`. Notation follows the paper's macros:
`pc, regs, mem` (state components), `code`
(program), `φ_op` (operation predicates), `B` (bus), `Ŝ` (committed state),
`Com` (commitment), `R*`, `R_{0,*}`, `R_1..R_4` (relations), `Π_i` (SNARKs).

---

## 1. Execution model (ch01)

**Program.** `P` is a fixed RV+ binary (RV32IM + precompiles), compiled from
an Ethereum state-transition function. Inputs `I` from Ethereum state `E`
(initial) + execution witness `W`; outputs `O` = final Ethereum state `E'`.

**VM state** `S := (pc, regs, mem)`: `pc` (32-bit program counter),
`regs[0..k-1]` (`k` 32-bit registers), `mem[]` (byte-addressed, writable
memory). `code` is immutable, read-only, and explicitly **not** part of the
state.

**Step relation.** `S:=(pc1,regs1,mem1) --op:=code[pc1]--> S':=(pc2,regs2,mem2)`
— the opcode is fetched from `code` at the current `pc`. Example (ADD):
`pc2=pc1+1`, `regs2=regs1[2:=regs1[0]+regs1[1]]`, `mem2=mem1`.

**Trace.** `T : S_0 -> S_1 -> ... -> S_T`. A zkVM proof for `(P,E,E')` proves
existence of such a chain with `S_0=(pc_0:=0,regs,mem)` derived from `E` and
`S_T` derived into `E'`.

**Operation predicates.** All ops are RV32IM or precompiles (Keccak,
Poseidon), treated as black boxes via:
```
φ_op(pc1,regs1,mem1,pc2,regs2,mem2) = TRUE  <=>
   (pc1,regs1,mem1) --op--> (pc2,regs2,mem2)  ∧  code[pc1] = op
```
(the `code[pc1]=op` "fetch conjunct" binds every step to the fixed program).
Memory ops (only ones touching `mem`):
```
read:  (regs1:=(addr,*,...),mem) -> (regs2:=(addr,x,...),mem),  mem[addr]=x
write: (regs1:=(addr,x,...),mem) -> (regs2:=(addr,x,...),mem'),
       mem'[i] = x if i=addr else mem[i]
```
decomposed into a memory-free pc/reg part `φ'_op` + explicit memory equation:
```
φ_read(S1,S2)  := φ'_read(pc1,regs1,pc2,regs2) ∧ mem1[regs1[0]] = regs2[1]
φ_write(S1,S2) := φ'_write(pc1,regs1,pc2,regs2) ∧ mem2 = mem1[regs1[0] ↦ regs1[1]]
```
All *other* ops get `φ'_op ∧ mem2=mem1` — non-memory steps provably can't
mutate memory.

**Op taxonomy (ch03):** memory (`read,write`); precompiles (`keccak,
poseidon`); arithmetic w/o range checks (`op_1..op_10`); arithmetic w/ range
checks (`op_11..op_20`, each `φ_op_i := φ'_op_i(S1,S2) ∧ φ_range(S1)`, range
constants in the last two registers). Step predicate:
`φ_step(S1,S2) := ⋁_{op} φ_op(S1,S2)`. No hash/arithmetic internals (e.g.
Keccak's permutation) are ever specified — they stay opaque predicates
`φ_keccak, φ_poseidon, φ_range`, as Lean already treats them.

---

## 2. Segmentation (ch02) and committed memory / bus (ch03)

**Segments.** Trace `T` cut into `m` segments `G_1..G_m` of exactly `N_seg`
instructions each (fixed, hardcoded, verifier-known; no-op padded).
`G_i: S_start_i -> S_end_i`. Global consistency:
`S_end_i = S_start_(i+1)` for `i∈[m-1]`, `S_start_1=S_0`, `S_end_m=S_T`.

**Segment layout.** One *segment trace* (`N_seg` rows; enforces only a
*subset* of instruction semantics inline) + three *chips*: Keccak, Poseidon,
Range-check (each holds all calls/checks of that type in the segment).
Consistency trace↔chips is enforced by a **bus** + lookup arguments (the
concrete lookup mechanism is left as a TODO for teams to fill in).

**Bus `B`:** `B = {(op^(i),S1^(i),S2^(i))}_{i=1..b}, op∈{keccak,poseidon}
∪ {(range,S^(j))}_{j=1..r}`. Filter predicates:
`φ_keccak(B):=⋀_{(keccak,S1,S2)∈B} φ_keccak(S1,S2)` (sim. poseidon, range).

**Bus-deferred step predicate:**
```
φ_step(S1,S2,B) := φ_step,bus(S1,S2,B) ∧ φ_keccak(B) ∧ φ_poseidon(B) ∧ φ_range(B)
```
`φ_step,bus` routes by op-class: memory ops + non-range arithmetic verified
**inline**; range-checked arithmetic verifies the arithmetic inline but
**defers** the check via `(range,S1)∈B`; precompiles are **fully deferred**
(step only checks `(op,S1,S2)∈B ∧ mem2=mem1`). Footnote: this rewritten form
is slightly *stronger* than the original (also asserts correctness of bus
entries the segment doesn't reference) — an efficiency-motivated
over-approximation, not a completeness gap.

**Committed memory.** `mem` replaced by a Merkle vector commitment
`Com=(Commit,Open,Verify)`: `Commit(mem)`→root; `Open(mem,i)`→auth path;
`Verify(C,i,v,π)=1` iff `π` certifies position `i` under `C` holds `v`.
Committed state `Ŝ:=(pc,regs,mem̂)`, `mem̂:=Commit(mem)`. Opening proofs are
**explicit witness fields** (not existentially quantified) — essential to the
proof: binding only applies to proofs a PPT prover actually produced, so the
extractor must read them out of the witness.
```
φ̂_read(Ŝ1,Ŝ2,π) := φ'_read(Ŝ1.pc,Ŝ1.regs,Ŝ2.pc,Ŝ2.regs) ∧ Ŝ1.mem=Ŝ2.mem
                    ∧ Verify(Ŝ1.mem, Ŝ1.regs[0], Ŝ2.regs[1], π)=1
φ̂_write(Ŝ1,Ŝ2,π^mem) := φ'_write(Ŝ1.pc,Ŝ1.regs,Ŝ2.pc,Ŝ2.regs)
   ∧ Verify(Ŝ1.mem, Ŝ1.regs[0], π^mem.v_old, π^mem.π_writ)=1
   ∧ Verify(Ŝ2.mem, Ŝ1.regs[0], Ŝ1.regs[1], π^mem.π_writ)=1
```
(`π^mem=(π_writ,v_old)`: one shared path opening old value under `Ŝ1.mem` and
new value under `Ŝ2.mem`.) Full committed step relation:
`φ̂_step(Ŝ1,Ŝ2,B̂,π^mem) := φ̂_step,bus(...) ∧ φ̂_keccak(B̂) ∧ φ̂_poseidon(B̂) ∧ φ̂_range(B̂)`
(the three chip predicates are syntactically unchanged, memory-free).

**Warning (important for Lean).** Satisfying `φ̂_step` does **not** imply
`φ_step`, even computationally — opening a commitment to the *full* memory
vector may be infeasible. The gap is bounded (not eliminated) by
position/update-binding of `Com_mem` — Proposition `memory-extractability`,
§5 below.

---

## 3. Correct-execution relation R* (ch03, formalized in ch05 `rem:cte-ks`)

Plain (uncommitted, bus-free) target relation of the whole proof:
```
R* = { ((S_0,S_T); (S_1,...,S_(T-1))) | ∀ i∈[T]: φ_step(S_(i-1),S_i) = TRUE }
```
Associated *verification algorithm* (turns "correct-trace extractability"
into ordinary knowledge soundness):
1. `Ŝ_0 := (pc_0,regs_0,Commit(mem_0))`, `Ŝ_T := (pc_T,regs_T,Commit(mem_T))`.
2. Output `Π_4.Verify((Ŝ_0,Ŝ_T), π^4)`.

The verifier only ever sees committed boundary states + the final proof
`π^4`; correctness of the entire intermediate trace (memory ops, precompiles,
range checks, bus consistency, all recursion layers) is exactly what the R*
witness must certify. This matches Lean's `ZkVM.Rstar`/`TraceValid`
(statement=boundary pair, witness=full `ℕ`-indexed trace, membership=per-step
predicate), except: the paper threads the *specific* `φ_step` disjunction of
§1/§2, and additionally derives `Ŝ_0,Ŝ_T` from `S_0,S_T` via `Commit` — a step
the abstract Lean `ZkVM.Stmt/initial/terminal` (bare projections, no
commitment structure) does not model.

---

## 4. Proof architecture (ch04)

**Topology — leaf layer of 4 circuits + 4 recursion layers:**

| Circuit | Purpose | Relation |
|---|---|---|
| `inner-step` | segment trace (leaf) | `R_{0,step}` |
| `inner-keccak` | Keccak precompile (leaf) | `R_{0,keccak}` |
| `inner-poseidon` | Poseidon precompile (leaf) | `R_{0,poseidon}` |
| `inner-range` | range checks (leaf) | `R_{0,range}` |
| `segment` | verifies the 4 inner proofs | `R_1` |
| `convert` | 1-to-1 normalization | `R_2` |
| `combine` | 2-to-1 recursive merge | `R_3` |
| `embed` | final proof | `R_4` |

**Recursion tree** (Fig. `fig:topo`): binary tree of `convert` leaves merged
pairwise by `combine` nodes to a root, capped by one `embed`. Example shown:
8 segments → 8 `convert` (each atop a `segment` atop 4 `inner-*`) → 3 levels
of `combine` → 1 `embed`. Not required to be balanced — `combine`'s relation
only needs `N_L+N_R=N` with each divisible by `N_seg` and `≥N_seg`; any binary
decomposition works, and `combine` is applied exactly `m-1` times total
across the tree for `m=T/N_seg` segments (Lemma "Combine tree unrolling").

**Relations:**
- `R_{0,step}` — chains `N_seg` committed steps `Ŝ_in→Ŝ_out`, bus committed
  in the public input; `code` is hard-wired into the circuit (so the
  verification key binds the proof to the fixed program):
  ```
  R_{0,step} = { ((Ŝ_in,Ŝ_out,C_B̂); (B̂,{Ŝ_i}_{i=1..N_seg+1},{π^mem_i}_{i=1..N_seg})) |
      Ŝ_1=Ŝ_in ∧ Ŝ_{N_seg+1}=Ŝ_out
      ∧ ⋀_{i=1}^{N_seg} φ̂_step,bus(Ŝ_i,Ŝ_{i+1},B̂,π^mem_i) = TRUE
      ∧ C_B̂ = Com_bus(B̂) }
  ```
- `R_{0,keccak}`, `R_{0,poseidon}`, `R_{0,range}`:
  `{ (C_B̂; B̂) | φ̂_j(B̂)=TRUE ∧ C_B̂=Com_bus(B̂) }`, `j∈{keccak,poseidon,range}`.
- `R_1` (`segment`) — verifies the 4 inner proofs under shared `C_B̂`:
  `Π_{0,step}.Verify((Ŝ_in,Ŝ_out,C_B̂),π_step)=1 ∧ Π_{0,keccak}.Verify(C_B̂,π_keccak)=1
  ∧ Π_{0,poseidon}.Verify(C_B̂,π_poseidon)=1 ∧ Π_{0,range}.Verify(C_B̂,π_range)=1`.
- `R_2` (`convert`, 1-to-1) — carries `N_seg` as public input (rejects any
  other value): `{ ((Ŝ_0,Ŝ_N,N_seg); π_1) | Π_1.Verify((Ŝ_0,Ŝ_N),π_1)=1 }`.
- `R_3` (`combine`, 2-to-1) — two children, each either `convert` (`Π_2`) or
  `combine` (`Π_3`), chained through witness state `Ŝ_N^L`:
  ```
  R_3 = { ((Ŝ_0^L,Ŝ_N^R,N); (π^L,π^R,Ŝ_N^L,N_L,N_R)) |
      (Vfy_2((Ŝ_0^L,Ŝ_N^L,N_L),π^L)=1 ∨ Vfy_3((Ŝ_0^L,Ŝ_N^L,N_L),π^L)=1)
      ∧ (Vfy_2((Ŝ_N^L,Ŝ_N^R,N_R),π^R)=1 ∨ Vfy_3((Ŝ_N^L,Ŝ_N^R,N_R),π^R)=1)
      ∧ N_L+N_R=N ∧ N_seg|N_L ∧ N_seg|N_R ∧ N_L≥N_seg ∧ N_R≥N_seg }
  ```
  (divisibility + `≥N_seg` side conditions make each child's step count
  strictly smaller than the parent's ⇒ well-founded recursion, Remark
  `rem:wellfounded`).
- `R_4` (`embed`, final) — `T` is a *fixed system parameter* (not
  adversary-chosen), `N_seg|T`, `T≥2N_seg` (so every execution has ≥2
  segments; `R_3` forces `N≥2N_seg`, so a single-segment execution has no
  valid tree), `T≤poly(λ)`:
  `R_4 = { ((Ŝ_0,Ŝ_T); π_3) | Π_3.Verify((Ŝ_0,Ŝ_T,T),π_3)=1 }`.

**Composition.** `zkVM = ({φ_op}, Com_bus, Com_mem, Π_0,Π_1,Π_2,Π_3,Π_4)`
(Definition "zkVM system", ch05). Each `Π_i.Verify` calls the next relation's
`Verify` inside its own relation's definition (`R_1↦Π_{0,j}`, `R_2↦Π_1`,
`R_3↦Π_2/Π_3`, `R_4↦Π_3`) — this is proof-carrying data (PCD), not a flat
SNARK.

---

## 5. Security (ch05)

### 5.1 Main theorem — exact statement

**`def:cte` (Correct-trace extractability).** Experiment
`Exp^cte_{zkVM,E_zkVM,A}(λ)`: `A` picks `S_0,S_T,π^4` (`code`,`T` fixed, not
adversary-chosen); verifier commits `Ŝ_0,Ŝ_T`, checks `Π_4.Verify`; if it
verifies, run `E_zkVM(S_0,S_T,π^4)` to get full-memory states `S_0..S_T`;
`A` **wins** iff the extracted trace disagrees with the claimed boundary
(`pc/regs/mem` at `0` or `T`) or `φ_step(S_i,S_{i+1})≠TRUE` for some `i`.
`zkVM` is CTE iff `Adv^cte_zkVM(A)≤negl(λ)` ∀ PPT `A`, for a fixed PPT `E_zkVM`.

**`rem:cte-ks`.** CTE is *exactly* knowledge soundness (`def:extractable`) of
the R*-verification algorithm of §3 — the paper's analogue of Lean's
`cte_iff_knowledgeSound`, except the R*-verifier here additionally performs
the `Commit(mem_0),Commit(mem_T)` step, which Lean's `ZkVM.Stmt/initial/
terminal` abstracts away entirely.

**`thm:main` (Correct-trace extractability) — exact bound.** Let
`m:=T/N_seg`. For every PPT `A` with `ε:=Adv^cte_zkVM(A)`, ∃ PPT reductions
`D_4,D_3,D_2,D_1,{D_{0,j}}_j,D_bus,{D^pos_k}_{k=1}^T,{D^upd_k}_{k=1}^T`:
```
ε ≤ Adv^ks_{Π_4}(D_4)
  + (m-1)·Adv^ks_{Π_3}(D_3)
  + m·Adv^ks_{Π_2}(D_2)
  + m·( Adv^ks_{Π_1}(D_1) + Σ_{j∈{step,keccak,poseidon,range}} Adv^ks_{Π_{0,j}}(D_{0,j})
        + Adv^cr_{Com_bus}(D_bus) )
  + Σ_{k=1}^{T} ( Adv^pos_{Com_mem}(D^pos_k) + Adv^upd_{Com_mem}(D^upd_k) )
```
All reductions run in `Time(A)+poly(λ)`; overall
`Time(E_zkVM) ≤ c·Time(A)+poly(λ)`, `c=3m+T` (`A` invoked once per
Embed/Convert/Combine call = `2m` total, plus `m` Segment calls, plus `T`
per-step memory-reconstruction calls). Negligible RHS ⇒ CTE.

### 5.2 Reduction structure — one lemma per layer, outermost→innermost, plus
a per-step memory argument

1. **Embed** (`lem:embed`): assumes `Π_4` KS; `D_4` just forwards `A`'s
   `(x,π^4)` to the `Π_4` challenger ⇒ `Adv^embed_{E_4}(A) ≤ Adv^ks_{Π_4}(D_4)`.
   Base case, coefficient 1.

2. **Combine** (`lem:combine`, "tree unrolling"): assumes `Π_3` KS. `E_3`
   recursively unrolls the tree (well-founded, `rem:wellfounded`: child step
   counts strictly `<N`). Bad event `B_t` at internal node `t`: node's proof
   verifies but `E_{Π_3}` fails to return an `R_3` witness. Exactly `m-1`
   internal nodes ⇒ `Adv^comb_{N,E_3}(A) ≤ (m-1)·Adv^ks_{Π_3}(D_3)`. Base case
   `N=N_seg` (`m=1`) is vacuous by *arithmetic contradiction*
   (`N_L+N_R=N_seg` with both `≥N_seg` is impossible).

3. **Convert** (`lem:convert`): assumes `Π_2` KS; single reduction,
   `Adv^conv_{E_2}(A) ≤ Adv^ks_{Π_2}(D_2)`, applied once per segment (`m`
   times total).

4. **Segment** (`lem:segment`): assumes `Π_1` KS + all four `Π_{0,j}` KS +
   `Com_bus` collision-resistant. *Six* bad events: `B_1` (`Π_1` extraction
   fails), `B_{0,step}`, `B_{0,j}` (`j∈{keccak,poseidon,range}`, inner
   extraction fails), `B_bus` (the four extracted buses `B̂_step, B̂_keccak,
   B̂_poseidon, B̂_range` aren't all equal despite committing to the same
   `C_B̂` — a `Com_bus` collision). Off all six, unify buses as `B̂:=B̂_step`
   and combine the four predicates via Eq. `eq:step-bus2` to get full
   `φ̂_step`. Bound: `Adv^seg_{E_1}(A) ≤ Adv^ks_{Π_1} + Adv^ks_{Π_{0,step}}
   + Adv^ks_{Π_{0,keccak}} + Adv^ks_{Π_{0,poseidon}} + Adv^ks_{Π_{0,range}}
   + Adv^cr_{Com_bus}`. The active Lean tree does not yet formalize this
   segment/bus reduction; it is assigned to Issues 2 and 5.

5. **Inner-circuit** (`lem:inner`): each `Π_{0,j}` KS directly gives its
   extractor; `Adv^inner_{j,E_{0,j}}(A) = Adv^ks_{Π_{0,j}}(A)` — no reduction
   loss (this game *is* the KS game).

6. **Memory extractability** (`prop:memory-extractability`) — not a
   recursion layer but a crypto-to-crypto bridge from committed-memory to
   plain full-memory correctness, applied once **per step** `k=0..T-1`:
   - Assumptions on `Com_mem` (`def:binding`): **position-binding**
     (`Adv^pos_{Com}(A):=Pr[Verify(C,i,v,π)=1 ∧ Verify(C,i,v',π')=1 ∧ v≠v']`
     negl.) and **update-binding**
     (`Adv^upd_{Com}(A):=Pr[Verify(C,addr,m[addr],π)=1 ∧ Verify(C',addr,x,π)=1
     ∧ C'≠Commit(m[addr↦x])]` negl.). Remark: Merkle trees get both from
     hash collision-resistance.
   - Statement: given `A` outputting `(Ŝ1,Ŝ2,mem1,mem2,B̂,π^mem)` with matching
     program counters/registers and `Ŝ_j.mem=Commit(mem_j)`, with `φ̂_step`
     holding but `φ_step(S1,S2)` (for
     `S_j:=(Ŝ_j.pc,Ŝ_j.regs,mem_j)`) failing with prob. `ε`, then
     `ε ≤ Adv^pos_{Com_mem}(D^pos) + Adv^upd_{Com_mem}(D^upd)`.
   - Proof: two bad events `E_pos,E_upd` (position/update collisions), one
     reduction each; then a case-split over every op kind (arithmetic w/wo
     range, read, write, precompile) showing off both bad events
     `φ̂_step ⇒ φ_step(...,B) ⇒ φ_step(...)` — the second implication ("Step
     B: bus elimination") needs no crypto, purely predicate unfolding.
   - Used in `thm:main` Step 6 to inductively rebuild `mem_0..mem_T` from the
     committed-state chain + per-step memory-opening witnesses `{π^mem_k}`
     extracted at the Segment layer, contributing the
     `Σ_{k=1}^T(Adv^pos_k+Adv^upd_k)` tail. Issue 1 formalizes the
     perfect, probability-free reconstruction statement; the explicit
     reductions and advantage sum remain absent (§6).

### 5.3 Composition and running time

`E_zkVM` composes the five layer-extractors `E_4,E_3,E_2,E_1,{E_{0,j}}`
sequentially (Steps 1-4), then the per-step memory-reconstruction argument
(Steps 5-6). Every reduction is a single run of `A` + `poly(λ)`
(`Time(D)=Time(A)+poly(λ)`); the aggregate `c=3m+T` blow-up in
`Time(E_zkVM)` comes purely from *invocation count* (once per
Embed/Convert/Combine, `m` for Segment, `T` for memory reconstruction), not
from expensive individual reductions.

### 5.4 Idealization caveats (flagged by the paper itself, `rem:idealized`)

(i) `def:extractable` postulates a **straight-line** extractor in
`Time(A)+poly(λ)` — impossible for *succinct* proofs in the plain model,
only exists in the ROM. (ii) Composing straight-line extraction *across
recursion layers* (PCD) needs each SNARK knowledge-sound *relative to the
same random oracle* ("relativized"), and relativized SNARKs provably don't
exist in general (`EPRINT:relativized`) — the paper explicitly idealizes over
this. So `thm:main`'s bounds validate the **reduction structure/topology**,
not a concrete security level.

---

## 6. Gap list for Lean formalization

The current implementation (`VanillaZkVM/**/*.lean`): `Specification/Zkvm.lean` has the
abstract `ZkVM` structure and `Specification/Cte.lean` has `R*=ZkVM.Rstar`, `CTE=ZkVM.CTE`, keystone
`cte_iff_knowledgeSound`; `Preliminaries/Trace.lean` has `concatTrace`/`chain_flatten`.
`Preliminaries/ArgumentSystem.lean`
has `Relation`, `ArgumentSystem` (verifier-only), `Extractor`,
`KnowledgeSound` (**perfect**: `∃E,∀ x p, verify → rel`, no `λ`/`negl`/
running time); `Preliminaries/VectorCommitment.lean` has `VectorCommitment` with `Complete`,
`PositionBinding`, and `UpdateBinding` (perfect); and `Preliminaries/HashCommitment.lean` has
`HashCommitment` with `CollisionResistant`
(perfect: injective `hash`). `VMs/Memory.lean` reconstructs full memory from a
known initial memory and per-step `MemStep` witnesses, realizes the frozen
`MemoryBridge` by constructing each next full-memory state, and `VMs/TwoStep/TwoStep.lean`
composes that reconstruction into
`TwoStep.System.cte`. `VMs/ISA.lean` supplies the representative five-class
plain predicate, connects its selected operation to each explicit `MemStep`,
and `TwoStep.System.toZkVM` now uses that predicate as its actual `step`.
`VMs/Bus.lean` supplies the replacement segment bus: the four inner relations
and the proof that the four buses recovered for one segment agree.
`VMs/TwoStep/WithBus.lean` separately demonstrates per-segment extraction followed
by `chain_flatten` and memory reconstruction. Concrete opcode and chip
implementations remain absent. `VMs/MultiStep/MultiStep.lean` formalizes the
recursive convert/combine/embed proof tower over an abstract segment proof. Its
recursive extractor constructs and joins the committed traces recovered from the
tree, and its CTE theorem then applies the existing memory reconstruction. The
final `VMs/VanillaVM/VanillaVM.lean` assembly uses the bus-checked segment
verifier for that base case and proves the probability-free main CTE theorem.
The former playground `Bus.lean` is still only git-history reference material;
the current file is a new Issue 5 implementation against the frozen interfaces.

**(a) Committed memory / memory-commitment properties — memory core connected
to the representative ISA.** `VMs/Memory.lean` now formalizes the perfect
position/update-binding memory slice: committed/full read and write equations,
the `CommitInv` relation, conditional `step_mem_extract`,
`step_reconstruct`/`TwoStep.System.memoryBridge` (which produce each next
represented state), and
`trace_mem_extract`; `TwoStep.System.cte` composes it with the
two-layer toy. `VMs/TwoStep/TwoStepSanity.lean` gives a permanent accepting joint model for
the theorem's hypotheses. The append-bit countermodel demonstrates that
agreement of accepted openings away from the updated address does not provide
update binding. `ISA.System.committedOperation` now ties each `MemStep`
constructor and its address/value to program fetch and the designated
registers, and the two-step CTE concludes `stepPlain`. `Bus.System.stepBus` now
adds the bus/chip evidence, while
`Bus.System.stepWithBus_committedOperation` returns the same recovered
`MemStep` to that committed ISA relation. `Bus.TwoStepSystem.busBridge`
uses the same recovered `MemStep` to prove that the demonstration VM has a
suitable memory witness.
Explicit advantage/reduction accounting remains the Issue 8 study and Issues
10 and 6 in `PLAN.md` (the former Issue 2 was withdrawn).

**(b) Multi-layer recursion — abstract recursion and concrete segment
connection implemented.**
`VMs/MultiStep/MultiStep.lean` formalizes the leaf, convert, combine, and embed
relations. Its explicit, terminating `buildTrace` extractor follows the binary
proof tree, and `combine_tree` proves that it joins the recovered child traces
correctly. The recursive proof type permits both balanced and unbalanced trees;
the combine relation's size conditions guarantee that each recursive child is
strictly smaller. `committedTrace_extract` obtains the committed execution, and
the MultiStep CTE theorem reconstructs its full-memory execution.
`VMs/MultiStep/MultiStepSanity.lean` supplies a small accepted example showing
that these assumptions can hold together. `VMs/VanillaVM/VanillaVM.lean` uses
the bus-checked segment verifier for the recursion's base proofs and derives
the required extraction guarantee from `Bus.System.segment_extract`; it does
not assume a separate bus-free segment theorem. The quantitative `(m-1)`
accounting remains deferred to Issue 6.

**(c) Representative ISA operations — structure implemented, exact opcodes
still abstract.** `VMs/ISA.lean` uses the five Issue 3 classes `read`, `write`,
`arith`, `hash`, and `bin`. It defines the disjunction `stepPlain`, checks
`code[pc]`, makes the read/write memory equations explicit, and assigns
`stepPlain` to the concrete two-step VM. `VMs/Bus.lean` further divides `bin`
into its ordinary register check and its range check, and places hash and range
entries on a segment bus. This represents the paper's division of work, but it
does not define or verify the paper's individual `op_1..op_20`, Keccak, or
Poseidon implementations.

**(d) One bus per segment — reusable segment theorem plus a two-step connection.**
`VMs/Bus.lean` defines the step, Keccak, Poseidon, and range relations and proves
the perfect-security form of `lem:segment`: knowledge soundness recovers four
buses under one digest, and collision resistance proves that those four buses
are equal. This module has no dependency on a complete VM and does not choose
how segment proofs are combined. `VMs/TwoStep/WithBus.lean` is the separate
demonstration module:
`execution_extract` applies the segment theorem once per segment, retains a
separate bus `B̂_i` and `MemStep` sequence, and reuses
`concatTrace`/`chain_flatten` to obtain one committed-state trace. It then uses
the existing memory reconstruction theorem to prove CTE for the non-recursive
two-step VM. The sanity model accepts two segments with provably different
buses. The Issue 7 assembly reuses the segment theorem for the base proofs of
the recursive VM; concrete chip implementations remain outside the current
model.

**(e) Explicit reductions to hardness assumptions — systematically absent.**
`Preliminaries/` is deliberately **perfect/probability-free** (`KnowledgeSound`
is `∃E,∀ x p, verify→rel`, no adversary/`λ`/`negl`/`Adv(·)`/running time).
Consequences: no notion of advantage (`Adv^ks_Π`, `Adv^pos_Com`,
`Adv^upd_Com`, `Adv^cr_Com`) anywhere, so `thm:main`'s weighted sum of
advantage terms (each with an explicit reduction adversary and running time
`Time(A)+poly(λ)`) has no Lean counterpart. The probability-free proof chain
now culminates in `VanillaVM.System.cte_main`, but it has no failure
probabilities to add together. Unlike the paper's real bound, it therefore has
no factors depending on `m` or `T`. There is no PPT-adversary type, no
security-parameter families, no
negligibility predicate, no explicit reduction-adversary construction (the
paper spells these out per-lemma, e.g. `D_3^(t)`: "run `A` once, unroll the
tree to node `t`, forward to the `Π_3` challenger" — no challenger/experiment
formalism exists in Lean at all), no running-time bookkeeping. Issues 10 and 6
are scoped more narrowly than the paper's full asymptotic claim: they will add
randomized experiments and explicit advantages at fixed parameters, then prove
the concrete coefficient bound (`(m-1)·`, `m·`, and `Σ_{k=1}^T` terms).
Security-parameter families, PPT predicates, negligibility, and formal running
times remain outside that scope.

The final verifier now derives `Ŝ_0,Ŝ_T` from plain `S_0,S_T` with `Com_mem`, so
the boundary-commitment step is present in the assembled instance even though
the reusable `ZkVM` specification remains abstract. Remaining semantic gaps
include concrete opcode and chip implementations. The paper's own
`rem:idealized` caveat also remains: perfect knowledge soundness records the
straight-line extraction assumption but does not make a relativized SNARK
exist or establish a concrete security level.

**Implementation ordering:** [`PLAN.md`](PLAN.md) is authoritative. Issues 1,
3, 4, and 5 provide the memory, ISA, recursion, and bus layers; Issue 7 composes
them into the probability-free main theorem. The quantitative re-foundation in
Issues 10 and 6 follows the separate Issue-8 study and is not a prerequisite
for the perfect model.
