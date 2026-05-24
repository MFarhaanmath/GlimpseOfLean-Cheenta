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
  have hU_cover : ∀ x : X, x ∈ ⋃ j, U j := by
    intro x
    by_cases hx : x ∈ A
    · have hxcover := hAcover hx
      rcases mem_iUnion.mp hxcover with ⟨i, hi⟩
      have hmem : x ∈ U (some i) := by
        simpa [U] using hi
      exact mem_iUnion.mpr ⟨some i, hmem⟩
    · have hmem : x ∈ U none := by
        simpa [U] using hx
      exact mem_iUnion.mpr ⟨none, hmem⟩
  -- Apply compactness of X to get a finite subcover s : Finset (Option 𝒜)
  have hcompact := isCompact_univ (α := X)
  rw [isCompact_iff_finite_subcover] at hcompact
  obtain ⟨s, hs⟩ := hcompact U hU_open (by simp [hU_cover])
  -- Strip the `none` option out; only the `some` indices cover A
  refine ⟨s.filterMap id, ?_⟩
  intro x hx
  -- x ∈ A, so x ∉ Aᶜ, so the `none` set didn't cover x
  -- therefore x must be in some U (some i) for i ∈ s
  have hxU := hs (Set.mem_univ x)
  simp only [Set.mem_iUnion, Finset.mem_coe] at hxU
  obtain ⟨j, hjs, hjx⟩ := hxU
  -- j can't be none because x ∈ A
  cases j with
  | none =>
      -- U none = Aᶜ, but x ∈ A — contradiction
      simp [U] at hjx
      exact hjx hx
  | some i =>
      -- j = some i, so i ∈ s.filterMap id and x ∈ ↑i
      simp only [Set.mem_iUnion, Finset.mem_coe]
      refine ⟨i, ?_, ?_⟩
      · simp only [Finset.mem_filterMap, Function.comp]
        exact ⟨some i, hjs, rfl⟩
      · simpa [U] using hjx
