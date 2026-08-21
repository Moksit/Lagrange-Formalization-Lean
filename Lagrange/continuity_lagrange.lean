import Mathlib

open Function MulOpposite Set
open scoped Pointwise

variable {G : Type*} [Group G][Finite G] (H : Subgroup G) (g : G)

theorem mem_smul_set_subgroup {G : Type*} [Group G] (H : Subgroup G) (g x : G) :
x ∈ g • (H : Set G) ↔ ∃ h : G, h ∈ H ∧ g *h = x := by
  constructor
  · intro hx
    rcases hx with ⟨ h, hh, rfl⟩
    exact ⟨ h, hh, rfl ⟩
  · rintro ⟨ h, hh, rfl⟩
    exact ⟨ h,hh,rfl ⟩

--lemma smul_set_subgroup_eq {G : Type*} [Group G] (H : Subgroup G) (g : G) := by sorry


--Nat.card(g • (H : Set G))
def fintype_card_smul_subgroup_eq :  H ≃ (g • (H : Set G) : Set G) where
  toFun h := ⟨g • (h : G), ⟨h, h.property, rfl⟩⟩
  invFun x := ⟨g⁻¹ • x.val, by

/-

#check toFun

#check Nat.card
theorem fintype_card_smul_subgroup_eq {G : Type*} [Group G] (H : Subgroup G) (g : G)
    [Fintype H] [Fintype (g • (H : Set G))] :
    Fintype.card (g • (H : Set G)) = Fintype.card H := by sorry

-/

/-
theorem nat_card_smul_subgroup_eq {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (g • (H : Set G)) = Nat.card (H : Set G) := by sorry

#check Nat.card
-/
