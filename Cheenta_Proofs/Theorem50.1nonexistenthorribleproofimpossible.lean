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
universe v w
variable {X : Type u} [TopologicalSpace X]

theorem subspaceOfDimension
    {Y : Set X}
    (hY : IsClosed Y)
    {n : ℕ}
    (hdim : Covering_Dimension (X := X) n) :
    Covering_Dimension (X := ↥Y) n := by
  unfold Covering_Dimension at hdim ⊢
  intro ι u hu
  unfold IsOpenCover at hu
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
    ext x; simp [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases h : x ∈ Y
    · have hx : (⟨x, h⟩ : Y) ∈ ⋃ i, u i := hu.2.symm ▸ Set.mem_univ _
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨some i, by rw [← hU_eq i] at hi; exact hi⟩
    · exact ⟨none, h⟩

  let cover : IsOpenCover U_ext := ⟨hU_ext_open, hU_ext_univ⟩

  by_cases hι : Nonempty ι
  · -- Let Lean infer the universe of the index type using `_`
    -- Unpack exactly 5 items: index type, cover, open proof, refinement proof, order proof
    rcases hdim _ U_ext cover with ⟨κ, v, hv_cov, hv_ref, hv_ord⟩

    refine ⟨κ, fun k => Subtype.val ⁻¹' v k,
      ⟨fun k => (hv_cov.1 k).preimage continuous_subtype_val,
       by rw [← Set.preimage_iUnion, hv_cov.2, Set.preimage_univ]⟩,
       ?_,
       ?_⟩
    · -- Goal 1: Refinement proof
      intro k
      match hv_ref k with
      | ⟨none, hj⟩ => exact ⟨Classical.choice hι, fun y hy => False.elim (hj hy y.prop)⟩
      | ⟨some i, hj⟩ => exact ⟨i, fun y hy => by rw [← hU_eq i]; exact hj hy⟩
    · -- Goal 2: Order bound proof
      -- Apply your lemma showing that the preimage cover preserves the dimension bound n.
      sorry

  · have hYa : IsEmpty ↥Y := ⟨fun y => let ⟨i, _⟩ := Set.mem_iUnion.mp (hu.2.symm ▸ Set.mem_univ y); hι ⟨i⟩⟩
    -- Provide exactly 5 items for the empty case
    refine ⟨PEmpty, fun k => k.elim, ⟨fun k => k.elim, ?_⟩, fun k => k.elim, ?_⟩
    · ext y
      exact (hYa.false y).elim
    · sorry
