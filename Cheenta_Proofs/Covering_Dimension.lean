import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Cheenta_Proofs.BasicLemmasforCD

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

open Set Filter Function
open Filter Topology

universe u w

variable {X : Type u} [TopologicalSpace X]

def Covering_Dimension (n : ℕ) : Prop :=
  ∀ (ι : Type*) [Fintype ι] (u : ι → Set X),
    IsOpenCoverGeneral u →
    ∃ (κ : Type*) (_ : Fintype κ) (v : κ → Set X),
      IsOpenCoverGeneral v ∧
      RefinesGeneral v u ∧
      HasOrderLEGeneral v n

def Covering_Dimension_General {X : Type u} [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (ι : Type w) (u : ι → Set X),
    IsOpenCoverGeneral u →
    ∃ (κ : Type w) (v : κ → Set X),
      IsOpenCoverGeneral v ∧
      RefinesGeneral v u ∧
      HasOrderLEGeneral v n
