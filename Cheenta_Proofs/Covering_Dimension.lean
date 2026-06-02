/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Cheenta_Proofs.BasicLemmasforCD

public section
open Set Filter Function

open Filter Topology

universe u v w

structure OpenCover(X : Type v) [TopologicalSpace X] where
  α : Type*
  sets : α → Set X
  isOpen_sets : ∀ a, IsOpen (sets a)
  covers_univ : (⋃ a, sets a = Set.univ)
