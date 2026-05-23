import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.MetricSpace.Basic

theorem lebesgue_number_lemma_lean {X : Type*} [MetricSpace X](hX : CompactSpace X)
 (𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U) (hcover : ⋃₀ 𝒰 = Set.univ) : ∃ δ > 0,
  ∀ x : X, ∃ U ∈ 𝒰, Metric.ball x δ ⊆ U := by
  have h_univ : ∀ x : X, ∃ U ∈ 𝒰, x ∈ U := by
      simpa [Set.ext_iff] using hcover
  choose U hU hxU using h_univ
  have h_radius : ∀ x : X, ∃ r > 0, Metric.ball x r ⊆ U x := by
    intro x
    exact Metric.isOpen_iff.mp (hopen (U x) (hU x)) x (hxU x)
  -- Step 3: Define a cover by these balls
  let 𝒱 := {V | ∃ x, ∃ r > 0, V = ball x r ∧ ball x r ⊆ U x}
  have hVcover : ⋃₀ 𝒱 = univ := by
    ext y; constructor
    · intro _; trivial
    · intro hy
      obtain ⟨r, hr, hball⟩ := h_radius y
      refine ⟨ball y r, ⟨y, r, hr, rfl, hball⟩, mem_ball_self hr⟩

  -- Step 4: Compactness ⇒ finite subcover
  obtain ⟨𝒲, hWfin, hWsub, hWcover⟩ := CompactSpace.elim_finite_subcover hX 𝒱 hVcover

  -- Step 5: Extract radii from finite subcover
  let radii := {r | ∃ x, ball x r ∈ 𝒲}
  have hpos : ∀ r ∈ radii, 0 < r := by
    intro r hr; rcases hr with ⟨x, hx⟩
    obtain ⟨_, _, hrpos, _, _⟩ := hx; exact hrpos

  -- Step 6: Take minimum radius δ
  obtain ⟨δ, hδpos, hδmin⟩ := Finset.exists_minimal radii.toFinset hpos

  -- Step 7: Verification
  use δ; constructor
  · exact hδpos
  · intro x
    have hx := mem_univ x
    rw [← hWcover] at hx
    rcases hx with ⟨V, hV, hxV⟩
    rcases hVsub hV with ⟨x₀, r₀, hr₀, hVdef, hVsubU⟩
    use U x₀; constructor
    · exact hU x₀
    · calc
        ball x δ ⊆ ball x₀ r₀ := by
          apply ball_subset_ball; apply hδmin; use x₀; rw [hVdef]; exact hV
        ... ⊆ U x₀ := hVsubU




open Metric Set

theorem lebesgue_number_lemma_lean_1 {X : Type*} [MetricSpace X] [CompactSpace X]
  (𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U) (hcover : ⋃₀ 𝒰 = univ) :
  ∃ δ > 0, ∀ x : X, ∃ U ∈ 𝒰, ball x δ ⊆ U := by
  -- Step 1: Every point lies in some U
  have h_univ : ∀ x : X, ∃ U ∈ 𝒰, x ∈ U := by
    simpa [ext_iff] using hcover
  choose U hU hxU using h_univ

  -- Step 2: For each x, get a radius with ball inside U x
  have h_radius : ∀ x : X, ∃ r > 0, ball x r ⊆ U x := by
    intro x
    exact isOpen_iff.mp (hopen (U x) (hU x)) x (hxU x)

  -- Step 3: Define a cover by these balls
  let 𝒱 := {V | ∃ x r, 0 < r ∧ V = ball x r ∧ ball x r ⊆ U x}
  have hVcover : ⋃₀ 𝒱 = univ := by
    ext y
    constructor
    · intro _; trivial
    · intro hy
      obtain ⟨r, hr, hball⟩ := h_radius y
      refine ⟨ball y r, ⟨y, r, hr, rfl, hball⟩, mem_ball_self hr⟩

  -- Step 4: Compactness ⇒ finite subcover
  obtain ⟨𝒲, hWfin, hWsub, hWcover⟩ := CompactSpace.elim_finite_subcover 𝒱 hVcover

  -- Step 5: Extract radii from finite subcover
  let radii := {r | ∃ x, ball x r ∈ 𝒲}
  have hpos : ∀ r ∈ radii, 0 < r := by
    intro r hr
    rcases hr with ⟨x, hx⟩
    obtain ⟨_, _, hrpos, _, _⟩ := hx
    exact hrpos
