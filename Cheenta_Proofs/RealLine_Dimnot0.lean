import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Regular
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Dim0


#check (inferInstance : TopologicalSpace ℝ)


public section
open Set Filter Function

open Filter Topology

universe u v w

variable {X : Type u} [TopologicalSpace X]

def Covering_Dimension (n : ℕ) : Prop :=
  ∀ (ι : Type v) [Fintype ι] (u : ι → Set X),
    IsOpenCover u →
    ∃ (κ : Type*) (_ : Fintype κ) (v : κ → Set X),
      IsOpenCover v ∧
      Refines v u ∧
      HasOrderLE v n


open Set Topology

lemma real_not_dim0 : ¬ Covering_Dimension (X := ℝ)  0 := by
  intro h
  -- From your lemma: dimension 0 ↔ existence of disjoint clopen refinement
  have hclopen := dim0_iff_disjoint_clopen_refinement h
  -- Apply to the trivial cover {ℝ}
  let U := {univ : Set ℝ}
  have hU : IsOpenCover U := by
    constructor
    · intro i hi; simp [hi]  -- openness of univ
    · simp                    -- union of {univ} is univ
  obtain ⟨V, hVcover, hVclopen, hVdisjoint⟩ := hclopen U hU
  -- Now V is a refinement into disjoint clopen sets
  -- But ℝ is connected, so only trivial clopen sets exist
  have hconn : IsConnected (univ : Set ℝ) := isConnected_univ
  -- Connectedness contradicts existence of nontrivial disjoint clopen refinement
  exact hconn.not_disjoint_clopen_refinement V hVcover hVclopen hVdisjoint
