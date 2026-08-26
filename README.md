# Formalization of Lagrange's Theorem in Lean

This project formalizes **Lagrange's theorem** in group theory using [Lean](https://lean-lang.org/) and [Mathlib](https://github.com/leanprover-community/mathlib4).

The is stated as follows: for $G$ a finite group and $H$ a subgroup of $G$, one has:

$|G| = |G/H| \times |H|.$

In lean, it takes the form:

```lean
theorem lagrange_theorem [Fintype G] (H : Subgroup G)
    [Fintype H] [Fintype (LeftCosets H)] :
    Fintype.card G =
      Fintype.card (LeftCosets H) * Fintype.card H
```

The central idea of the proof is to construct an explicit bijection

$$
G \simeq G/H \times H,
$$

where $`G/H`$ is represented by a quotient of $`G`$ under the relation of belonging to the same left coset. The cardinality statement then follows immediately.

## Mathematical Structure

Assume $H \leq G$ and define

$$
a \sim b \iff a^{-1}b \in H.
$$

This relation identifies exactly the elements belonging to the same left coset.

The formalization of the proof proceeds in three stages:

1. Define and prove that `leftRel H` is an equivalence relation.
2. Construct a bijection

   ```lean
   G ≃ LeftCosets H × H
   ```
3. Apply `Fintype.card_congr` and `Fintype.card_prod` to obtain Lagrange's theorem:

   ```lean
   Fintype.card G = Fintype.card (LeftCosets H) * Fintype.card H
   ```

## Architecture

The code is organized as a hierarchy of **definitions → lemmas/proofs → theorem**:

```text
G : Type* [Group G]
│
└── H : Subgroup G
    │
    ├── Definition: leftRel H
    │   │
    │   └── Equivalence relation
    │       ├── refl
    │       ├── symm
    │       └── trans
    │
    ├── Definition: LeftCosets H
    │   │
    │   └── Quotient (leftRel H)
    │
    ├── Definition: groupEquivCosetProd H
    │   │
    │   ├── toFun
    │   │   └── invFun
    │   │
    │   ├── left_inv
    │   └── right_inv
    │
    └── Theorem: lagrange_theorem
        │
        ├── Fintype.card_congr
        └── Fintype.card_prod
```

### Proof Dependencies

```text
leftRel
   │
   │
   ▼
LeftCosets
   │
   ▼
groupEquivCosetProd
   │
   │
   ▼
lagrange_theorem
```

The difficult mathematical work is isolated in the construction of the equivalence; once

```lean
G ≃ LeftCosets H × H
```

has been established, the cardinality argument is essentially automatic.

## Main Definitions

### `leftRel`

```lean
def leftRel (H : Subgroup G) : Setoid G
```

Defines the relation

```lean
a⁻¹ * b ∈ H
```

and proves reflexivity, symmetry, and transitivity.

### `LeftCosets`

```lean
def LeftCosets (H : Subgroup G) := Quotient (leftRel H)
```

Represents the set of left cosets as a quotient type.

### `groupEquivCosetProd`

```lean
def groupEquivCosetProd (H : Subgroup G) :
  G ≃ LeftCosets H × H
```

Constructs the explicit bijection. An element $g\in G$ is represented by a pair consisting of its left coset $gH$ and the unique element $h\in H$ that, together with the chosen representative of $gH$, reconstructs $g$.

## Proof of Lagrange's Theorem

The proof then reduces to:

```lean
rw [Fintype.card_congr (groupEquivCosetProd H)]
simp only [Fintype.card_prod]
```

In fact, the formal proof mirrors the mathematical argument: $|G| = |G/H \times H| = |G/H| \times |H|.$

## Installation

```bash
lake init Lagrange math
lake update
lake exe cache get
lake build
```
