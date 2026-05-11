import Mathlib
-- File created and edited by Niranjan S Rao. (As of now)
-- Lemma 1: Every closed subspace of a compact space is also compact

variable {X : Type*} [TopologicalSpace X]
variable (A: Set X)

lemma subspaceclosedcompact (hX: IsConnected X) (hA: IsClosed A)
