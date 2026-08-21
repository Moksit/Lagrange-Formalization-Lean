import Mathlib

open Function MulOpposite Set
open scoped Pointwise

variable {G : Type*} [Group G]
variable (H : Subgroup G)

open Function MulOpposite Set
open scoped Pointwise

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

-- Theorem 2: Coset intersection property / membership condition
-- If an element x belongs to both left cosets g • H and k • H,
-- then the element k⁻¹ * g must belong to the subgroup H.
@[to_additive add_coset_intersection_mem]
theorem coset_intersection_mem {G : Type*} [Group G] (H : Subgroup G) (g k x : G)
  (hxg : x ∈ g • (H : Set G))
  (hxk : x ∈ k • (H : Set G)) :
  k⁻¹ * g ∈ H := by
  -- Unpack the membership of x in g • H to get h₁ ∈ H such that g * h₁ = x
  have hg := (mem_smul_set_subgroup H g x).mp hxg
  rcases hg with ⟨h₁, hh₁, hxeq₁⟩

  -- Unpack the membership of x in k • H to get h₂ ∈ H such that k * h₂ = x
  have hk := (mem_smul_set_subgroup H k x).mp hxk
  rcases hk with ⟨h₂, hh₂, hxeq₂⟩

  -- Since both equal x, we have g * h₁ = k * h₂
  have h_eq : g * h₁ = k * h₂ := by
    calc
      g * h₁ = x := hxeq₁
      _ = k * h₂ := hxeq₂.symm

  -- Multiply both sides on the left by k⁻¹
  have h_eq' : k⁻¹ * (g * h₁) = k⁻¹ * (k * h₂) := by
    exact congrArg (fun y => k⁻¹ * y) h_eq

  -- Simplify the right side: k⁻¹ * k * h₂ becomes h₂
  rw [← mul_assoc] at h_eq'
  rw [← mul_assoc] at h_eq'
  rw [inv_mul_cancel, one_mul] at h_eq'

  -- Multiply both sides on the right by h₁⁻¹ to isolate k⁻¹ * g
  have h_eq'' := congrArg (fun y => y * h₁⁻¹) h_eq'
  rw [mul_assoc] at h_eq''
  rw [mul_inv_cancel, mul_one] at h_eq''
  rw [h_eq'']

  -- Since h₂ ∈ H and h₁⁻¹ ∈ H (by subgroup properties), their product is in H
  exact H.mul_mem hh₂ (H.inv_mem hh₁)

-- Theorem 3: Equality of left cosets
-- Two left cosets g • H and k • H are equal if and only if k⁻¹ * g ∈ H.
theorem coset_eq_of_mem
  {G : Type*} [Group G]
  (H : Subgroup G) (g k : G)
  (hkg : k⁻¹ * g ∈ H) :
  g • (H : Set G) = k • (H : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      -- Direction 1: Show g • H ⊆ k • H
      have hg := (mem_smul_set_subgroup H g x).mp hx
      rcases hg with ⟨h, hh, hxeq⟩

      have hmem : (k⁻¹ * g) * h ∈ H := by
        exact H.mul_mem hkg hh

      apply (mem_smul_set_subgroup H k x).mpr
      refine ⟨(k⁻¹ * g) * h, hmem, ?_⟩
      rw [← mul_assoc]
      rw [mul_inv_cancel_left]
      exact hxeq

    · intro x hx
      -- Direction 2: Show k • H ⊆ g • H
      have hk := (mem_smul_set_subgroup H k x).mp hx
      rcases hk with ⟨h, hh, hxeq⟩

      have hgk : g⁻¹ * k ∈ H := by
        have h_inv : (k⁻¹ * g)⁻¹ ∈ H := by
          exact H.inv_mem hkg
        rw [mul_inv_rev, inv_inv] at h_inv
        exact h_inv

      have hmem : (g⁻¹ * k) * h ∈ H := by
        exact H.mul_mem hgk hh

      apply (mem_smul_set_subgroup H g x).mpr
      refine ⟨(g⁻¹ * k) * h, hmem, ?_⟩
      rw [← mul_assoc]
      rw [mul_inv_cancel_left]
      exact hxeq

-------------------

-- 1. Define what a specific coset is as a Lean Type.
-- (This creates a type containing only the elements x where x ∈ gH)
def LocalCoset (g : G) := {x : G // x ∈ g • (H : Set G)}

-- 2. Build the local bijection between the subgroup H and the LocalCoset gH.
-- We will use `mem_smul_set_subgroup` to prove this works!

/--
This equivalence proves that any single left coset `gH` has exactly
the same number of elements as the subgroup `H`.
Mathematically, it establishes the one-to-one mapping f(h) = g * h.
-/
def local_coset_equiv (g : G) : H ≃ LocalCoset H g where
  -- 1. THE FORWARD FUNCTION (H → gH)
  -- If you hand me an element `h` from the subgroup H,
  -- I will multiply it by `g` to give you an element in the coset gH.
  toFun := by
      -- 1. Introduce the input element (h ∈ H)
      intro h

      -- 2. Define the exact group element we want to output (g * h)
      let target_val := g * h.val

      -- 3. Prove step-by-step that this element actually belongs to the coset gH
      have proof_in_coset : target_val ∈ g • (H : Set G) := by
        -- We use your colleague's theorem in reverse (mpr)
        apply (mem_smul_set_subgroup H g target_val).mpr

        -- The theorem requires us to provide an element in H. We provide h.val.
        use h.val

        -- Now we must prove two things: (1) h.val is in H, and (2) g * h.val = target_val
        constructor
        · exact h.property -- Lean already knows h is in H, this is the proof.
        · rfl              -- g * h.val equals target_val by definition.

      -- 4. Package the value and the proof together to finish
      exact ⟨target_val, proof_in_coset⟩

  -- 2. THE BACKWARD FUNCTION (gH → H)
  -- If you hand me an element `x` from the coset gH,
  -- I will multiply it by the inverse `g⁻¹` to strip away the `g`
  -- and hand you back the original element in H.
  invFun := by
    intro x

    let h_val := g⁻¹ * x.val

    have h_in_subgroup : h_val ∈ H := by
      -- Step 1: Extract the proof that x.val is in the coset
      -- `x` is a Subtype, so `x.property` is the literal proof of membership.
      have x_in_coset : x.val ∈ g • (H : Set G) := x.property

      -- Step 2: Instatiate Theorem 1 for our specific elements
      -- This gives us the exact ↔ (if-and-only-if) statement we need.
      have membership_iff := mem_smul_set_subgroup H g x.val

      -- Step 3: Apply the forward direction (.mp) of the theorem
      -- We feed our proof (Step 1) into the left side of the ↔ (Step 2)
      -- to get the existential statement on the right side.
      have h_exists : ∃ h : G, h ∈ H ∧ g * h = x.val :=
        membership_iff.mp x_in_coset

      -- Step 4: Unpack the existential statement
      -- Now we crack open `h_exists` into its three underlying parts.
      rcases h_exists with ⟨h, hh, h_eq⟩
      unfold h_val
      rw [← h_eq]
      rw [<- mul_assoc]
      rw [inv_mul_cancel]
      rw [one_mul]
      exact hh

    exact ⟨h_val, h_in_subgroup⟩


      --- first replace x by g h
      -- say that g-1 g is identity
      -- show that h is in H


  -- 3. LEFT INVERSE (Proof that invFun(toFun(h)) = h)
  -- We must prove to Lean that if we start with `h`, multiply by `g`,
  -- and then multiply by `g⁻¹`, we get exactly `h` back.
  -- (Algebraically: g⁻¹ * (g * h) = h)
  left_inv := by
    intro h
    ext
    dsimp
    rw [← mul_assoc, inv_mul_cancel, one_mul]


  -- 4. RIGHT INVERSE (Proof that toFun(invFun(x)) = x)
  -- We must prove that if we start with `x`, multiply by `g⁻¹`,
  -- and then multiply by `g`, we get exactly `x` back.
  -- (Algebraically: g * (g⁻¹ * x) = x)
  right_inv := by
    intro x
    -- 1. Unfold the subtype abbreviation so Lean sees it as {val // property}
    dsimp [LocalCoset]

    -- 2. Use ext to prove equality of the subtype components
    ext

    -- 3. Evaluate the functions
    dsimp
    rw [<- mul_assoc]
    rw [mul_inv_cancel]
    rw [one_mul]


---

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

  -- PROOF 2: invFun (toFun g) = g
  right_inv := by
    intro p
    ext
    · dsimp

      sorry

    -- Hint: Similar algebraic cancellation
    -- dsimp
    sorry

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
