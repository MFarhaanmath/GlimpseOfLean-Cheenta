import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.MetricSpace.Basic

open Filter

variable {X Y : Type*} [TopologicalSpace X][MetricSpace Y]
variable {A : Set X}
variable {B : Set Y}

theorem continuity_iff_epsilon_delta_ball {f : X → Y} :
  Continuous f ↔ ∀ x : X, ∀ ε > 0, ∃ U ∈ nhds x, f '' U ⊆ Metric.ball (f x) ε := by
  constructor
  · -- Forward direction (→): Continuous f → ∀ x ε > 0, ∃ U ∈ nhds x, f '' U ⊆ Metric.ball (f x) ε
    intro hf x ε hε
    have : Metric.ball (f x) ε ∈ nhds (f x) := Metric.ball_mem_nhds (f x) hε
    have preimage_nhd : f ⁻¹' Metric.ball (f x) ε ∈ nhds x := hf.continuousAt.preimage_mem_nhds this
    use f ⁻¹' Metric.ball (f x) ε, preimage_nhd
    intro y hy
    simp [Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hz

  · -- Backward direction
    intro h
    rw [continuous_def]
    intro s hs
    rw [isOpen_iff_mem_nhds] at hs ⊢
    exact fun x hx => by
      specialize hs (f x) hx
      obtain ⟨ε, hε, hsub⟩ := hs
      obtain ⟨U, U_in, hU⟩ := h x ε hε
      use U, U_in
      exact Set.Subset.trans (Set.image_subset f hU) hsub
      exact Set.Subset.trans (Set.image_subset f hU) hsub

variable {X Y : Type*} [TopologicalSpace X][MetricSpace Y]
variable {A : Set X}
variable {B : Set Y}

def converges_uniformly (f_n : ℕ → X → Y) (f : X → Y) : Prop :=
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : X, dist (f_n n x) (f x) < ε

namespace UniformLimitProof

def ConvergesUniformly {X Y : Type*} [Dist Y]
    (f_n : ℕ → X → Y) (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : X, dist (f_n n x) (f x) < ε

private theorem three_step_triangle {Y : Type*} [MetricSpace Y]
    (a b c d : Y) :
    dist a d ≤ dist a b + dist b c + dist c d := by
  have step₁ : dist a d ≤ dist a c + dist c d := dist_triangle a c d
  have step₂ : dist a c ≤ dist a b + dist b c := dist_triangle a b c
  linarith

theorem uniform_limit_is_continuous
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    (f_n : ℕ → X → Y)
    (f  :  X → Y)
    (hf    : ∀ n, Continuous (f_n n))
    (hconv : ConvergesUniformly f_n f) :
    Continuous f := by
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_preimage] at hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU (f x) hx
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨N, hN⟩ := hconv (ε / 3) hε3
  have hV := (hf N).continuousAt.preimage_mem_nhds
    (Metric.ball_mem_nhds (f_n N x) hε3)
  apply Filter.mem_of_superset hV
  intro y hy
  apply hball
  simp only [Set.mem_preimage, Metric.mem_ball] at hy
  simp only [Metric.mem_ball]
  have e₁ := hN N le_rfl x
  have e₂ := hN N le_rfl y
  have chain := three_step_triangle (f y) (f_n N y) (f_n N x) (f x)
  linarith [dist_comm (f y) (f_n N y) ▸ e₂]

end UniformLimitProof

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
variable {A : Set X}
variable {B : Set Y}
-- Definitons

def converges_uniformly_1 (f_n : ℕ → X → Y) (f : X → Y) : Prop :=
∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : X, dist (f_n n x) (f x) < ε
-- Above is the definition of uniform convergence in LEAN

theorem uniform_limit_theorem_ (f_n : ℕ → X → Y)
(f : X → Y) (hf : ∀ n , Continuous (f_n n)) :
converges_uniformly f_n f → Continuous f := by
  intro proposition
  rw [Metric.continuous_iff] -- Main hurdle right now.
  intro x ε hε
  obtain ⟨N, hN⟩ := proposition (ε / 3) (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuous_iff.mp (hf N) x (ε / 3) (by linarith)
  refine ⟨δ, hδpos, fun y hy => ?_⟩
  have h1 : dist (f_n N y) (f y)      < ε / 3 := hN N le_rfl y -- ε/3 here
  have h2 : dist (f_n N y) (f_n N x)  < ε / 3 := hδ y hy
  have h3 : dist (f_n N x) (f x)      < ε / 3 := hN N le_rfl x
  calc dist (f y) (f x)
      ≤ dist (f y) (f_n N y) + dist (f_n N y) (f x) :=
          dist_triangle _ _ _
    _ ≤ dist (f y) (f_n N y) + dist (f_n N y) (f_n N x) + dist (f_n N x) (f x) := by
          linarith [dist_triangle (f_n N y) (f_n N x) (f x)]
    _ < ε / 3 + ε / 3 + ε / 3 := by
          linarith [dist_comm (f_n N y) (f y)]
    _ = ε := by ring