/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/
module
import Cheenta_Proofs.BasicLemmasforCD
public import Mathlib.Data.Option.Basic
public import Mathlib.Topology.Separation.Regular

public section
open Set Filter Function

open Filter Topology

universe u v w

structure OpenCover(X : Type v) [TopologicalSpace X] where
  α : Type*
  sets : α → Set X
  isOpen_sets : ∀ a, IsOpen (sets a)
  covers_univ : (⋃ a, sets a = Set.univ)
