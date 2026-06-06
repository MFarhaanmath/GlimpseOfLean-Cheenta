import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Regular
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Dim0
import Cheenta_Proofs.Covering_Dimension
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

#check (inferInstance : TopologicalSpace ℝ)

public section
open Set Filter Function

open Filter Topology

universe u v w

variable {X : Type u} [TopologicalSpace X]

open Set Topology

lemma real_not_dim0 : ¬ Covering_Dimension (X := ℝ) 0 := by
  intro h
  let u : Bool → Set ℝ := fun b => if b then Set.Ioi 0 else Set.Iio 1
  have hu : IsOpenCover u := by
    constructor
    · intro b
      cases b <;> simp [u, isOpen_Ioi, isOpen_Iio]
    · ext x
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      by_cases hx : x < 1
      · exact ⟨false, by simp [u, hx]⟩
      · exact ⟨true, by simp [u]; linarith⟩
  obtain ⟨κ, hκ, v, hvcov, hvref, hvord⟩ := h Bool inferInstance u hu
  have hdisj : ∀ k₁ k₂ : κ, k₁ ≠ k₂ → v k₁ ∩ v k₂ = ∅ := by
    intro k₁ k₂ hne
    by_contra hne'
    rw [← Set.ne_empty_iff_nonempty] at hne'
    push_neg at hne'
    obtain ⟨x, hx1, hx2⟩ := Set.nonempty_iff_ne_empty.mpr hne'
    have hm := hvord x
    unfold HasOrderLE multiplicity at hm
    have : 2 ≤ Fintype.card { k : κ // x ∈ v k } := by
      apply Fintype.card_le_of_injective (fun b => if b then ⟨k₁, hx1⟩ else ⟨k₂, hx2⟩)
      intro a b hab
      cases a <;> cases b <;> simp_all
    simp at hm
    omega
  have hconn : IsConnected (Set.univ : Set ℝ) := isConnected_univ
  rw [isConnected_iff_sUnion_eq_univ_of_disjoint] at hconn
  have hfinset := (isConnected_iff (s := Set.univ)).mp hconn
  haveI : Fintype κ := hκ
  let U : Finset (Set ℝ) := Finset.univ.image v
  have hUopen : ∀ s ∈ U, IsOpen s := by
    intro s hs
    simp [U] at hs
    obtain ⟨k, rfl⟩ := hs
    exact hvcov.1 k
  have hUsub : Set.univ ⊆ ⋃₀ ↑U := by
    intro x _
    have := hvcov.2
    rw [← this]
    simp [U, Set.mem_sUnion]
    have : x ∈ ⋃ k, v k := by rw [hvcov.2]; trivial
    rw [Set.mem_iUnion] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨v k, ⟨k, rfl⟩, hk⟩
  have hUpairwise : ∀ a ∈ U, ∀ b ∈ U,
      (Set.univ ∩ (a ∩ b)).Nonempty → a = b := by
    intro a ha b hb hab
    simp [U] at ha hb
    obtain ⟨k₁, rfl⟩ := ha
    obtain ⟨k₂, rfl⟩ := hb
    by_contra hne
    have hk : k₁ ≠ k₂ := fun h => hne (congrArg v h)
    have := hdisj k₁ k₂ hk
    rw [Set.inter_comm] at hab
    simp [Set.univ_inter] at hab
    rw [this] at hab
    exact Set.not_nonempty_empty hab
  obtain ⟨s, hsU, hsuniv⟩ := hfinset U hUpairwise hUopen hUsub
  simp [U] at hsU
  obtain ⟨k, rfl⟩ := HSub.hSub
  obtain ⟨b, hb⟩ := hvref k
  have hfull : v k = Set.univ := by
    exact Set.eq_univ_of_univ_subset hsuniv
  have hproper : u b ≠ Set.univ := by
    cases b <;> simp [u] <;> [exact Set.Iio_ne_univ 1; exact Set.Ioi_ne_univ 0]
  exact hproper (Set.eq_univ_of_univ_subset (hfull ▸ hb))
