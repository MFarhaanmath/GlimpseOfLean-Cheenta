import Mathlib
-- File created and edited by Niranjan S Rao. (As of now)
-- Lemma 1: Every closed subspace of a compact space is also compact

variable {X : Type*} [TopologicalSpace X]
variable [CompactSpace X]
variable (A : Set X)

-- Once I am completed with this proof, make sure to go through it. I will add
-- helpful comments so that anyone can understand it.

lemma closed_compact
    (hA : IsClosed A) :
    IsCompact A := by
  rw [isCompact_iff_finite_subcover]
  intro 𝒜 hopen hcover
  intro hAcover
  have hAc_open : IsOpen Aᶜ := hA.isOpen_compl
  -- Extend the cover of A to a cover of X by throwing in Aᶜ
  let U : Option 𝒜 → Set X :=
  fun j =>
    match j with
    | none => Aᶜ
    | some i => hopen i
  have hU_open : ∀ j, IsOpen (U j) := by
    intro j
    cases j with
    | none =>
        simpa [U] using hAc_open
    | some i =>
        simpa [U] using hcover i
  have hU_cover : ∀ x : X, ∃ j, x ∈ U j := by
    intro x
    by_cases hx : x ∈ A
    · have hxcover := hAcover hx
      -- Pure logic extraction from the definition of a union
      obtain ⟨i, hi⟩ := hxcover
      exact ⟨some i, hi⟩
    · exact ⟨none, hx⟩

  -- 2. Use the CompactSpace definition of X directly.
  -- In Lean 4, a CompactSpace is defined by its `isCompact_univ` property.
  obtain ⟨s, hs⟩ := CompactSpace.isCompact_univ U hU_open hU_cover

  -- 3. Construct the finite subcover for A using basic logic
  refine ⟨Finset.filterMap id s, ?_⟩
  intro x hx

  -- Look up x in the total space cover guaranteed by `hs`
  have hx_univ : x ∈ Set.univ := Set.mem_univ x
  have hx_s := hs hx_univ
  obtain ⟨j, hjs, hjx⟩ := hx_s

  -- Case split on the index j to eliminate the `none` case by contradiction
  cases j with
  | none =>
      exact False.elim (hjx hx)
  | some i =>
      refine ⟨i, ?_, hjx⟩
      rw [Finset.mem_filterMap]
      exact ⟨some i, hjs, rfl⟩
