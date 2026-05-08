import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.MetricSpace.Basic
variable {X Y : Type*} [TopologicalSpace X]
variable {A B : Set X}


lemma product_of_connected (hA : IsConnected A) (hB : IsConnected B) (x : A) (y : B): 
IsConnected (A ×ˢ B) := by
  unfold IsConnected at *
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  ·