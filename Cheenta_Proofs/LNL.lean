import Mathlib

open Set
-- This first proof is a proof with no errors fixed by Adhiraj. This is just the same as the
-- second proof, but it uses a different variation of tactics that fixes the original errors
-- of the proof that we had originally made.
theorem lebesgue_number_lemma_lean {X : Type*} [MetricSpace X] [CompactSpace X]
    (u : Set (Set X)) (hopen : ∀ U ∈ u, IsOpen U)
    (hcover : ⋃₀ u = Set.univ) :
    ∃ δ > 0, ∀ x : X, ∃ U ∈ u, Metric.ball x δ ⊆ U := by
  classical

  by_cases hnon : Nonempty X

  · haveI : Nonempty X := hnon

    have hxcover : ∀ x : X, ∃ U ∈ u, x ∈ U := by
      intro x
      have hx : x ∈ ⋃₀ u := by
        rw [hcover]
        exact Set.mem_univ x
      rcases Set.mem_sUnion.mp hx with ⟨U, hUu, hxU⟩
      exact ⟨U, hUu, hxU⟩

    choose U hUu hxU using hxcover

    have hopenU : ∀ x : X, IsOpen (U x) := by
      intro x
      exact hopen (U x) (hUu x)

    have hball : ∀ x : X, ∃ r > 0, Metric.ball x r ⊆ U x := by
      intro x
      exact Metric.isOpen_iff.mp (hopenU x) x (hxU x)

    choose r hrpos hrsub using hball

    have h_half_cover :
        (Set.univ : Set X) ⊆ ⋃ x : X, Metric.ball x (r x / 2) := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨x, by
        rw [Metric.mem_ball]
        simpa using half_pos (hrpos x)⟩

    rcases isCompact_univ.elim_finite_subcover
        (fun x : X => Metric.ball x (r x / 2))
        (fun x => Metric.isOpen_ball)
        h_half_cover
      with ⟨s, hs_cover⟩

    have hs_nonempty : s.Nonempty := by
      by_contra hs
      have hs_eq : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have hx : (Classical.choice hnon) ∈ ⋃ i ∈ s, Metric.ball i (r i / 2) :=
        hs_cover (Set.mem_univ _)
      simp [hs_eq] at hx

    let radii : Finset ℝ := s.image fun i => r i / 2

    have hradii_nonempty : radii.Nonempty := by
      rcases hs_nonempty with ⟨i, hi⟩
      exact ⟨r i / 2, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩

    let δ : ℝ := radii.min' hradii_nonempty

    have hδ_pos : 0 < δ := by
      have hδmem : δ ∈ radii := by
        dsimp [δ]
        exact Finset.min'_mem radii hradii_nonempty
      rcases Finset.mem_image.mp hδmem with ⟨i, hi, h_eq⟩
      rw [← h_eq]
      exact half_pos (hrpos i)

    refine ⟨δ, hδ_pos, ?_⟩
    intro x

    have hx_cover : x ∈ ⋃ i ∈ s, Metric.ball i (r i / 2) :=
      hs_cover (Set.mem_univ x)

    rcases Set.mem_iUnion.mp hx_cover with ⟨i, hi_rest⟩
    rcases Set.mem_iUnion.mp hi_rest with ⟨hi_s, hx_half⟩

    refine ⟨U i, hUu i, ?_⟩
    intro y hy
    apply hrsub i

    rw [Metric.mem_ball] at hx_half hy ⊢

    have hδle : δ ≤ r i / 2 := by
      dsimp [δ, radii]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi_s, rfl⟩)

    calc
      dist y i ≤ dist y x + dist x i := dist_triangle y x i
      _ < δ + r i / 2 := add_lt_add hy hx_half
      _ ≤ r i / 2 + r i / 2 := by nlinarith
      _ = r i := by ring

  · refine ⟨1, by norm_num, ?_⟩
    intro x
    exact False.elim (hnon ⟨x⟩)

-- Here is the unedited original proof that we all together made, with some errors.

theorem lebesgue_number_lemmaog {X : Type*} [MetricSpace X] (hX : CompactSpace X)
    (𝒰 : Set (Set X)) (hopen : ∀ U ∈ 𝒰, IsOpen U) (hcover : ⋃₀ 𝒰 = Set.univ) :
    ∃ δ > 0, ∀ x : X, ∃ U ∈ 𝒰, Metric.ball x δ ⊆ U := by
  have h_univ : ∀ x : X, ∃ U ∈ 𝒰, x ∈ U := by
    simpa [Set.ext_iff] using hcover
  choose U hU hxU using h_univ
  have h_radius : ∀ x : X, ∃ r > 0, Metric.ball x r ⊆ U x := by
    intro x
    exact Metric.isOpen_iff.mp (hopen (U x) (hU x)) x (hxU x)
  choose r hr_pos hr_ball using h_radius
  obtain ⟨s, hs_cover⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => Metric.ball x (r x / 2))
    (fun _ : X => Metric.isOpen_ball)
    (by intro x _; exact Metric.mem_ball_self (half_pos (hr_pos x)))
  rcases s.eq_empty_or_nonempty with rfl | hs_nonempty
  · have hX_empty : IsEmpty X := by
      rw [isEmpty_iff]
      intro x
      have := hs_cover (Set.mem_univ x)
      simp at this
    exact ⟨1, one_pos, fun x => hX_empty.elim x⟩
  obtain ⟨x_min, hx_min_s, hx_min_le⟩ :=
    s.exists_min_image (fun x => r x / 2) hs_nonempty
  refine ⟨r x_min / 2, half_pos (hr_pos x_min), fun y => ?_⟩
  have hy : y ∈ ⋃ x ∈ s, Metric.ball x (r x / 2) := hs_cover (Set.mem_univ y)
  simp only [Set.mem_iUnion, Metric.mem_ball] at hy
  obtain ⟨xi, hxi_s, hxi_dist⟩ := hy
  refine ⟨U xi, hU xi, fun z hz => ?_⟩
  apply hr_ball xi
  simp only [Metric.mem_ball] at hz ⊢
  have hδ_le : r x_min / 2 ≤ r xi / 2 := hx_min_le xi hxi_s
  calc dist z xi
      ≤ dist z y + dist y xi    := dist_triangle z y xi
    _ < r x_min / 2 + r xi / 2 := by linarith [hz, hxi_dist]
    _ ≤ r xi / 2 + r xi / 2    := by linarith
    _ = r xi                    := by ring
