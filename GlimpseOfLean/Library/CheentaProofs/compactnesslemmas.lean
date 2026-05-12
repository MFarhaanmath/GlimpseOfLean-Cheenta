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
