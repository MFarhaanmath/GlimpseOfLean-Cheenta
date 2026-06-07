import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Regular
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Cheenta_Proofs.BasicLemmasforCD
import Cheenta_Proofs.Dim0_iff_Clopen
import Cheenta_Proofs.Covering_Dimension
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

public section
open Set Filter Function

open Filter Topology

universe u v w

variable {X : Type u} [TopologicalSpace X]

open Set Topology

lemma real_not_dim0 : ¬ Covering_Dimension (X := ℝ) 0 := by
 sorry
