import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Basic
-- File created and edited by Niranjan S Rao. (As of now)
-- Lemma 1: Every closed subspace of a compact space is also compact

variable {X : Type*} [TopologicalSpace X]
variable [CompactSpace X]

variable (A : Set X)

lemma closed_compact
    (hA : IsClosed A) :
    IsCompact A := by
  rw [isCompact_iff_finite_subcover]
  intro 𝒜 hopen hcover
  intro hAcover
  have hAc_open : IsOpen Aᶜ := hA.isOpen_compl
  let U : Option 𝒜 → Set X :=
  fun j =>
    match j with
    | none => Aᶜ
    | some i => hopen i
  have hU_open : ∀ j, IsOpen (U j) := by
    intro j
    cases j with
    |  none =>
        simpa [U] using hAc_open
    | some i =>
        simpa [U] using hcover i
  have hU_cover : ∀ x : X, x ∈ ⋃ j, U j := by
    intro x
    by_cases hx : x ∈ A
    · have hxcover : x ∈ U i, hopen i := by
        exact hAcover hx
      rcases mem_iUnion.mp hxcover with ⟨i, hi⟩
      have : x ∈ U (some i) := by
        simpa [U] using hi
    -- THIS LEAN LEMMA IS UNDER CONSTRUCTION. HELP IF YOU CAN,
    -- BUT PLEASE DO NOT DELETE OR BACKSPACE ANYTHING.
