import Mathlib

/-!
# A collision-resistant commitment

A hash-based commitment, kept separate from the vector commitment in `VectorCommitment.lean`
because the two layers are independent. For example, memory reconstruction consumes only the
vector-commitment binding notions, while the bus consumes only collision-resistance.

The notion is idealized as plain injectivity. See `IDEALIZATION.md`.

`VMs/Bus.lean` consumes these declarations to identify the four buses extracted
inside one segment. No theorem compares buses from different segments.
-/

namespace VanillaZkVM

/-- A hash-style commitment `hash : Domain → Digest`.

Paper: `def:bus-cr`. -/
structure HashCommitment where
  /-- The type of hashed values. -/
  Domain : Type
  /-- The digest type. -/
  Digest : Type
  /-- The hash function. -/
  hash : Domain → Digest

/-- **Collision-resistance**: the commitment map is injective.

Paper: `def:bus-cr`. Idealized: see `IDEALIZATION.md`. -/
def CollisionResistant (H : HashCommitment) : Prop :=
  ∀ b b' : H.Domain, H.hash b = H.hash b' → b = b'

end VanillaZkVM
