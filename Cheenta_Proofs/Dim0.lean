import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Cheenta_Proofs.BasicLemmasforCD

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

public section
open Set
universe u v
variable {X : Type u} [TopologicalSpace X]


theorem dim0_iff_disjoint_clopen_refinement
    {ι : Type*} [Fintype ι] (u : ι → Set X) (hu : IsOpenCover u) :
    (∃ (κ : Type) (_ : Fintype κ) (v : κ → Set X), IsOpenCover v ∧ Refines v u ∧ HasOrderLE v 0) ↔
    (∃ (κ : Type) (_ : Fintype κ) (v : κ → Set X), IsOpenCover v ∧ Refines v u ∧ ∀ k₁ k₂, k₁ ≠ k₂ → v k₁ ∩ v k₂ = ∅) := by
  constructor
  · rintro ⟨κ, hκ, v, hvc, hv_ref, hv_ord⟩
    refine ⟨κ, hκ, v, hvc, hv_ref, ?_⟩
    intro k₁ k₂ hne
    ext x
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    intro ⟨hk₁, hk₂⟩
    have hm := hv_ord x
    unfold multiplicity at *
    classical
    have hs := Fintype.card_le_one_iff_subsingleton.mp hm
    have h_eq : (⟨k₁, hk₁⟩ : {i : κ // x ∈ v i}) = ⟨k₂, hk₂⟩ := by
     exact hs.elim ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩
    injection h_eq with h_k_eq
    exact hne h_k_eq

  · rintro ⟨κ, hκ, v, hvcov, hv_ref, hv_disj⟩
    refine ⟨κ, hκ, v, hvcov, hv_ref, ?_⟩
    intro x
    unfold multiplicity
    classical
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor
    rintro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩
    by_cases hne : k₁ = k₂
    · ext
      exact hne
    · have h_disj := hv_disj k₁ k₂ hne
      have h_mem : x ∈ v k₁ ∩ v k₂ := ⟨hk₁, hk₂⟩
      rw [h_disj] at h_mem
      exact False.elim h_mem
