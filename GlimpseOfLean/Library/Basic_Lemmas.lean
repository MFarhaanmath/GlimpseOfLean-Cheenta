import Mathlib.Topology.Basic
import Mathlib.Topology.Closure

variable {X : Type*} [TopologicalSpace X]
variable (A : Set X)

example : IsOpen (interior A) := by
  unfold interior
  apply isOpen_sUnion
  intro g hg
  apply hg.1

lemma setinsideclosure (A : Set X): A ⊆ closure A := by
  intro x hx
  unfold closure
  intro t ht
  exact ht.2 hx

  variable {X : Type*} [TopologicalSpace X]
  variable (A : Set X)
  variable (B : Set X)

example: A ∩ B ⊆ A := by
intro x hx
exact hx.1



example : IsOpen ( interior A ) := by
  unfold interior
  apply isOpen_sUnion
  intro g hg
  apply hg.1


variable {X : Type*} [TopologicalSpace X]

lemma intersection_closed {ι : Type*} {A : ι → Set X}
  (hA : ∀ i, IsClosed (A i)) : IsClosed (⋂ i, A i) := by
  constructor 
  rw [Set.compl_iInter] 
  apply isOpen_iUnion 
  intro i 
  exact (hA i).isOpen_compl 

set_option linter.unusedSectionVars false
lemma null_intersection_complement : A ∩ Aᶜ = ∅ := by
  ext x --CHnages statement to equivalent statement. See the Lean_Infoview
  constructor
  · intro hx
    have hA := hx.1
    have hAc := hx.2
    contradiction
  · intro hp
    cases hp 



lemma Shravas_lemma {α : Type*} (t : Set α) : (tᶜ)ᶜ = t := by
  ext y
  constructor
  · 
    intro h
    by_contra hn
    exact h hn
  · 
    intro h hn
    exact hn h



lemma difference_of_sets_closure :
  closure A \ closure B ⊆ closure (A \ B) := by
  intro x hx  
  rcases hx with ⟨hxA, hxB⟩
  rw [mem_closure_iff] at hxA 
  rw [mem_closure_iff] at hxB 
  push_neg at hxB 
  obtain ⟨V, hV, hxV, hVB⟩ := hxB 
  rw [mem_closure_iff]  
  intro U hU hxU  
                 
  have hUV : IsOpen (U ∩ V) := hU.inter hV 
  have hxUV : x ∈ U ∩ V := ⟨hxU, hxV⟩ 
  obtain ⟨y, ⟨hyU, hyV⟩, hyA⟩ := hxA (U ∩ V) hUV hxUV
  have hynotB : y ∉ B := by  
    intro hyB 
    have : y ∈ V ∩ B := ⟨hyV, hyB⟩  
    simp [hVB] at this  
  exact ⟨y, hyU, hyA, hynotB⟩   