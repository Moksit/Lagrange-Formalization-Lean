import Mathlib

open Function MulOpposite Set
open scoped Pointwise

theorem mem_smul_set_subgroup {G : Type*} [Group G] (H : Subgroup G) (g x : G) :
x ∈ g • (H : Set G) ↔ ∃ h : G, h ∈ H ∧ g *h = x := by
  constructor
  · intro hx
    rcases hx with ⟨ h, hh, rfl⟩
    exact ⟨ h, hh, rfl ⟩
  · rintro ⟨ h, hh, rfl⟩
    exact ⟨ h,hh,rfl ⟩

theorem coset_intersection_mem {G : Type*} [Group G] (H : Subgroup G) (g k x : G)
  (hxg : x ∈ g • (H : Set G))
  (hxk : x ∈ k • (H : Set G)) :
  k⁻¹ * g ∈ H := by
  have hg := (mem_smul_set_subgroup H g x).mp hxg
  rcases hg with ⟨ h₁, hh₁, hxeq₁⟩

  have hk := (mem_smul_set_subgroup H k x).mp hxk
  rcases hk with ⟨ h₂,hh₂, hxeq₂⟩
  have h_eq : g * h₁ = k * h₂ :=by
   calc
   g* h₁ = x := hxeq₁
   _ = k *h₂ := hxeq₂.symm

  have h_eq' : k⁻¹ * (g * h₁) = k⁻¹ * (k * h₂) := by
    exact congrArg (fun y => k⁻¹*y) h_eq

  rw [← mul_assoc] at h_eq'
  rw [← mul_assoc] at h_eq'
  rw [inv_mul_cancel, one_mul] at h_eq'
  have h_eq'' := congrArg ( fun y => y* h₁⁻¹) h_eq'
  rw [mul_assoc] at h_eq''
  rw [mul_inv_cancel, mul_one] at h_eq''
  rw[h_eq'']
  exact H.mul_mem hh₂ (H.inv_mem hh₁)


  theorem coset_eq_of_mem
  {G : Type*} [ Group G]
  (H : Subgroup G) (g k : G)
  (hkg : k⁻¹*g ∈ H) :
  g • (H : Set G) = k • (H : Set G) := by
    apply Set.Subset.antisymm
    intro x
    intro hx
    have hg := (mem_smul_set_subgroup H g x).mp hx
    rcases hg with ⟨h, hh, hxeq ⟩

    have hmem : (k⁻¹ * g) * h ∈ H := by
     exact H.mul_mem hkg hh
    apply (mem_smul_set_subgroup H k x).mpr
    refine ⟨ (k⁻¹ * g) * h, hmem, ?_⟩
    rw [← mul_assoc]
    rw[mul_inv_cancel_left]
    exact hxeq

    intro x hx
    have hk := (mem_smul_set_subgroup H k x).mp hx
    rcases hk with ⟨ h,hh, hxeq ⟩
    have hgk : g⁻¹ * k ∈ H := by
      have h_inv : (k⁻¹ * g)⁻¹ ∈ H := by
        exact H.inv_mem hkg
      rw [mul_inv_rev, inv_inv] at h_inv
      exact h_inv
    have hmem : (g⁻¹ *k) *h ∈ H := by
     exact H.mul_mem hgk hh
    apply (mem_smul_set_subgroup H g x).mpr
    refine ⟨ (g⁻¹*k) *h, hmem, ?_⟩
    rw [ ← mul_assoc]
    rw[mul_inv_cancel_left]
    exact hxeq
