import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Data.Fintype.Card

open Set

universe u v

variable {X : Type u} [TopologicalSpace X]

def IsOpenCover
    {ι : Type v}
    (u : ι → Set X) : Prop := -- Family of sets definition
-- using index i to U_i function.
  (∀ i, IsOpen (u i)) ∧ -- Every U_i is open.
  (⋃ i, u i) = Set.univ -- Union of all equals whole X


def Refines
    {ι : Type v}
    {κ : Type*}
    (v : κ → Set X)
    (u : ι → Set X) : Prop :=
  ∀ k, ∃ i, v k ⊆ u i
-- This has to be explained properly. It does cover entire set.
-- But in this case every refinement is automatically an open cover.


noncomputable def multiplicity
  {ι : Type v}
  [Fintype ι]
  (u : ι → Set X)
  (x : X) : ℕ :=
by
  classical
  exact Fintype.card { i : ι // x ∈ u i }

def HasOrderLE
    {ι : Type v}
    [Fintype ι]
    (u : ι → Set X)
    (n : ℕ) : Prop :=
  ∀ x : X, multiplicity u x ≤ n + 1


def CoveringDimensionLE
    (n : ℕ) : Prop :=

  ∀ (ι : Type v)
    (_ : Fintype ι)
    (u : ι → Set X),

    IsOpenCover u →

    ∃ (κ : Type*)
      (_ : Fintype κ)
      (v : κ → Set X),

      IsOpenCover v ∧
      Refines v u ∧
      HasOrderLE v n


def trivialCover : Unit → Set X :=
  fun _ => Set.univ

lemma trivialCover_open :
    IsOpenCover (trivialCover : Unit → Set X) := by
  refine ⟨?_, ?_⟩

  · intro i
    simp [trivialCover]

  · ext x
    simp [trivialCover]

omit [TopologicalSpace X]
lemma refines_refl
  {ι : Type v}
  (u : ι → Set X) :
  Refines u u := by
  intro i
  exact ⟨i, subset_rfl⟩

omit [TopologicalSpace X]
lemma refines_trans
    {ι : Type v}
    {κ : Type*}
    {σ : Type*}
    {u : ι → Set X}
    {v : κ → Set X}
    {w : σ → Set X}
    (h₁ : Refines w v)
    (h₂ : Refines v u) :
    Refines w u := by

  intro s

  rcases h₁ s with ⟨k, hkv⟩
  rcases h₂ k with ⟨i, hui⟩

  refine ⟨i, ?_⟩

  exact Set.Subset.trans hkv hui

omit [TopologicalSpace X]
lemma trivialCover_order :
  HasOrderLE
    (trivialCover : Unit → Set X)
    0 := by

  intro x
  unfold multiplicity

  classical

  simp [trivialCover]
