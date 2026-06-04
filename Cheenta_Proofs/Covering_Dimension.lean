import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Cheenta_Proofs.BasicLemmasforCD

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

module Cheenta_Proofs.Covering_Dimension

public section
open Set Filter Function

open Filter Topology

universe u v w

variable {X : Type u} [TopologicalSpace X]

def Covering_Dimension (n : ℕ) : Prop :=
  ∀ {ι : Type v} [Fintype ι] {u : ι → Set X},
    IsOpenCover u →
    ∃ (k : Type*) (_ : Fintype k) (v : k → Set X),
      TsOpenCover v ∧ ...
