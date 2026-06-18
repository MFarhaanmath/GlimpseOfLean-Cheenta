import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Covering_Dimension

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

public section
open Set
universe u v
variable {X : Type u} [TopologicalSpace X]

theorem subspaceOfDimension
    {Y : Set X}
    (hY : IsClosed Y)
    {n : ℕ}
    (hdim : Covering_Dimension_General (X := X) n) :
    Covering_Dimension_General (X := ↥Y) n := by
  unfold Covering_Dimension_General at hdim ⊢
  intro ι u hu
  unfold IsOpenCoverGeneral at hu
  have h_open := hu.1
  simp_rw [isOpen_induced_iff] at h_open
  choose U hU_open hU_eq using h_open
  let U_ext : Option ι → Set X := fun
    | none => Yᶜ
    | some i => U i
  have hU_ext_open : ∀ (j : Option ι), IsOpen (U_ext j) := by
    intro j
    cases j with
    | none => exact isOpen_compl_iff.mpr hY
    | some i => exact hU_open i
  have hU_ext_univ : ⋃ (j : Option ι), U_ext j = univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases h : x ∈ Y
    · have hx : (⟨x, h⟩ : Y) ∈ ⋃ i, u i := hu.2.symm ▸ Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨some i, by rw [← hU_eq i] at hi; exact hi⟩
    · exact ⟨none, h⟩

  let cover : IsOpenCoverGeneral U_ext := ⟨hU_ext_open, hU_ext_univ⟩

  by_cases hι : Nonempty ι
  · obtain ⟨κ, v, hv_cov, hv_ref, hv_ord⟩
    refine ⟨κ, inferInstance, fun k => Subtype.val ⁻¹' v k,
      ⟨fun k => (hv_cov.1 k).preimage continuous_subtype_val,
       by rw [← Set.preimage_iUnion, hv_cov.2, Set.preimage_univ]⟩,
       fun k => ?_, fun y => hv_ord y.val⟩
    match hv_ref k with
    | ⟨none, hj⟩ => exact ⟨Classical.choice hι, fun y hy => False.elim (hj hy y.prop)⟩
    | ⟨some i, hj⟩ => exact ⟨i, fun y hy => by rw [← hU_eq i]; exact hj hy⟩
  · have hYa : IsEmpty Y := ⟨fun y => let ⟨i, _⟩ := Set.mem_iUnion.mp (hu.2.symm ▸ Set.mem_univ y); hι ⟨i⟩⟩
    exact ⟨PEmpty, PEmpty.elim,
      ⟨fun k => k.elim, by ext y; exact (hY.false y).elim⟩,
      fun k => k.elim, fun y => (hY.false y).elim⟩
