import Mathlib

open Function MulOpposite Set
open scoped Pointwise

variable {G : Type*} [Group G]
variable (H : Subgroup G)

-- Theorem 1: Characterization of membership in a left coset
-- An element x belongs to the left coset g • H if and only if
-- x can be written as g * h for some element h in H.
@[to_additive add_mem_vadd_set_add_subgroup]
theorem mem_smul_set_subgroup
    {G : Type*}              -- G is the type representing our group
    [Group G]                -- G has a group structure (multiplication, inverses, identity)
    (subgroupH : Subgroup G) -- H is a subgroup of G
    (cosetRep elementX : G)  -- g (coset representative) and x (element being tested)
    :
    elementX ∈ cosetRep • (subgroupH : Set G) ↔ ∃ h : G, h ∈ subgroupH ∧ cosetRep * h = elementX := by

  -- Because this is an if-and-only-if (↔) statement, we split it into two directions (goals)
  constructor
  · rintro ⟨groupElement, isMember, rfl⟩
    -- rintro unpacks the existential statement hidden inside the set definition:
    -- • groupElement: the element 'h' from the subgroup
    -- • isMember: the proof that 'h ∈ H'
    -- • rfl: substitutes elementX with (cosetRep * groupElement) automatically via reflexivity

    -- We provide the exact same witness back to satisfy the right-hand side existential
    exact ⟨groupElement, isMember, rfl⟩

  -- Direction 2 (Backward ←): If elementX = g * h for some h ∈ H, it belongs to the coset
  · rintro ⟨groupElement, isMember, rfl⟩
    -- Similarly, rintro unpacks the assumption that such a 'h' exists and sets elementX = cosetRep * h

    -- Conversely, if elementX = cosetRep * h with h ∈ H, it clearly belongs to cosetRep • H
    exact ⟨groupElement, isMember, rfl⟩

/-
· rintro ⟨h, hh, h_eq⟩   -- 1. Unpack and name the equality `h_eq`
  rw [h_eq]            -- 2. Manually rewrite/substitute it
  exact ⟨h, hh, rfl⟩   -- 3. Finish the proof
-/

-- Step 1: Define the equivalence relation
-- We say 'a' and 'b' are related if they belong to the same left coset.
-- Algebraically, this means a⁻¹ * b ∈ H.
def leftRel (H : Subgroup G) : Setoid G where
  r a b := a⁻¹ * b ∈ H
  iseqv := {
    -- 1a. Reflexivity: a ~ a (a⁻¹ * a ∈ H)
    refl := by
      intro a
      rw [inv_mul_cancel]
      exact H.one_mem

    -- 1b. Symmetry: a ~ b → b ~ a (a⁻¹ * b ∈ H → b⁻¹ * a ∈ H)
    symm := by
      intro a b hab
      have h_inv := H.inv_mem hab
      rw [mul_inv_rev, inv_inv] at h_inv
      exact h_inv

    -- 1c. Transitivity: a ~ b → b ~ c → a ~ c
    trans := by
      intro a b c hab hbc
      -- Hint: (a⁻¹ * b) * (b⁻¹ * c) = a⁻¹ * c.
      -- The product of two elements in H is in H.
      have hac := H.mul_mem hab hbc
      rw [<- mul_assoc] at hac
      rw [mul_assoc  a⁻¹ b b⁻¹] at hac
      rw [mul_inv_cancel] at hac
      rw [mul_one] at hac
      exact hac
  }

-- Step 2: Define the set of all left cosets (The Quotient Type)
-- This creates a new type where each "element" is an entire coset.
def LeftCosets (H : Subgroup G) := Quotient (leftRel H)

-- We open a noncomputable section because choosing a representative
-- from a quotient space uses the Axiom of Choice.
noncomputable section

-- Step 3a: The Bijection between G and (LeftCosets H × H)
def groupEquivCosetProd (H : Subgroup G) : G ≃ LeftCosets H × H where
  -- FORWARD: Take g in G. Return its coset, and the "remainder" inside H.
  toFun g :=
    let q := Quotient.mk (leftRel H) g
    let rep := Quotient.out q

    have h_in_H : rep⁻¹ * g ∈ H := by
      -- 1. Prove that the coset of rep is the same as the coset of g
      have same_coset : Quotient.mk (leftRel H) rep = Quotient.mk (leftRel H) g :=
        Quotient.out_eq q

      -- 2. Use Quotient.exact directly on the custom relation
      have are_related : (leftRel H).r rep g :=
        Quotient.exact same_coset

      -- 3. Being related means rep⁻¹ * g ∈ H by definition of leftRel
      exact are_related

    (q, ⟨rep⁻¹ * g, h_in_H⟩)

  -- BACKWARD: Take a coset q and an element h in H. Return an element in G.
  invFun p :=
    let q := p.1
    let h := p.2
    let rep := Quotient.out q
    rep * h.val

  -- PROOF 1: toFun (invFun p) = p
  left_inv := by
    intro g
    -- Hint: You'll need to show rep * (rep⁻¹ * g) = g
    dsimp
    rw [<- mul_assoc]
    rw [mul_inv_cancel]
    rw [one_mul]

-- PROOF 2: The right inverse mapping (invFun (toFun p) = p)
  right_inv := by
    -- 'coset_pair' represents the input pair (C, h)
    intro coset_pair

    -- Unpack the pair into 'target_coset' (C) and 'subgroup_elem' (h)
    rcases coset_pair with ⟨target_coset, subgroup_elem⟩

    -- Pre-compute the core mathematical fact: (g * h)H = gH
    have coset_unchanged : Quotient.mk (leftRel H) (Quotient.out target_coset * ↑subgroup_elem) = target_coset := by
      -- Step 1: Prove (g * h)H = gH by applying Quotient.sound
      have h_sound : Quotient.mk (leftRel H) (Quotient.out target_coset * ↑subgroup_elem) = Quotient.mk (leftRel H) (Quotient.out target_coset) := by
        apply Quotient.sound
        -- Show algebraically what the equivalence relation means
        show (Quotient.out target_coset * ↑subgroup_elem)⁻¹ * Quotient.out target_coset ∈ H
        rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        exact H.inv_mem subgroup_elem.property

      -- Step 2: Use the standard fact that ⟦target_coset.out⟧ = target_coset
      rw [h_sound]
      exact Quotient.out_eq target_coset

    -- Split the goal to prove equality for both parts of the pair
    ext
    · -- Case 1: Prove the coset component maps back to itself
      dsimp
      exact coset_unchanged

    · -- Case 2: Prove the subgroup element component maps back to itself
      dsimp
      -- Rewrite using our pre-computed fact to simplify the expression
      rw [coset_unchanged]
      -- Standard algebraic cancellation
      rw [← mul_assoc, inv_mul_cancel, one_mul]

-- Step 3b: The Final Theorem
-- Because you did the hard work of building the bijection above,
-- the cardinality proof is now just two lines of Fintype lemmas!
theorem lagrange_theorem [Fintype G] [Fintype H] [Fintype (LeftCosets H)] :
  Fintype.card G = Fintype.card (LeftCosets H) * Fintype.card H := by

  -- 1. Since G and (LeftCosets H × H) are bijective, they have the same size.
  rw [Fintype.card_congr (groupEquivCosetProd H)]

  -- 2. The size of a Cartesian product (A × B) is Size(A) * Size(B).
  -- (simp can usually solve this directly, or use Fintype.card_prod)
  simp only [Fintype.card_prod]

end -- ends the noncomputable section
