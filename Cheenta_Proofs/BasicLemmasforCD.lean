import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Basic

open Set

universe u v

variable {X : Type u} [TopologicalSpace X]

def multiplicity
   {ι : Type*}
   (u : ι → Set X) (x : X) (_ : ℕ) : Prop :=
  ∀ (s : Set ι), (∀ i ∈ s, x ∈ u i) →
    (∀ (f : ℕ → ι), (∀ n, f n ∈ s) → ¬ Function.Injective f)

def HasOrderLE
   {κ : Type*}
   (v : κ → Set X) (n : ℕ) : Prop :=
 ∀ (s : Set κ),
   (∀ (f : ℕ → κ), Function.Injective f → (∀ i < n + 2, f i ∈ s)) →
   (⋂ k ∈ s, v k) = ∅

def HasOrderEq
    {κ : Type*} (v : κ → Set X) (n : ℕ) : Prop :=
  HasOrderLE v n ∧
  ∃ (g : Fin (n + 1) → κ),
    Function.Injective g ∧
    (⋂ i, v (g i)) ≠ ∅

def IsOpenCover {ι : Type*}
 (u : ι → Set X) : Prop :=
 (∀ i, IsOpen (u i)) ∧
 (⋃ i, u i) = univ

def Refines {ι : Type*}
 {κ : Type*} (v : κ → Set X)
 (u : ι → Set X) : Prop :=
 ∀ k : κ, ∃ i : ι, v k ⊆ u i

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
 {ι : Type*}
 (u : ι → Set X) :
 Refines u u := by
 intro i
 exact ⟨i, subset_rfl⟩

omit [TopologicalSpace X]
lemma refines_trans
   {ι : Type*}
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
  sorry

lemma restrict_cover_union
   {ι : Type*}
   (u : ι → Set X)
   (hu : (⋃ i, u i) = Set.univ)
   (Y : Set X) :
   (⋃ i, (Y ∩ u i)) = Y := by
   calc
   ⋃ i, (Y ∩ u i)
       = Y ∩ (⋃ i, u i) := by
           rw [Set.inter_iUnion]
   _ = Y ∩ Set.univ := by
           rw [hu]
   _ = Y := by
           simp
