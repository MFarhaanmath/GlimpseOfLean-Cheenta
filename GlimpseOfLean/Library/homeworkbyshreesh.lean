import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : Set X}
variable {B : Set Y}

set_option linter.style.whitespace false
example {α : Type} {A B : Set α} : A ∩ B ⊆ A := by
  intro a ha
  exact ha.1

example {S : Set (Set X)} (h : ∀ s ∈ S, IsClosed s) :
  IsClosed (⋂₀ S) := by
  rw [← isOpen_compl_iff] ---Complement is open
  rw [Set.compl_sInter] ---de morgans laws
  apply isOpen_sUnion ---union of open sets
  intro t ht
  rcases ht with ⟨s, hs, rfl⟩
  rw [isOpen_compl_iff]
  exact h s hs

example : closure (A ×ˢ B) = closure A ×ˢ closure B := by
  exact closure_prod_eq

example (f : X → Y) (ha : Continuous f) (x : X) (xn : ℕ → X) (hb : ∀ V, IsOpen V → x ∈ V → ∃ N, ∀ n ≥ N, xn n ∈ V) :
  ∀ U, IsOpen U → f x ∈ U → ∃ N, ∀ n ≥ N, f (xn n) ∈ U := by
  intro U hbU hax
  exact hb (f ⁻¹' U) (ha.isOpen_preimage U hbU) hax
