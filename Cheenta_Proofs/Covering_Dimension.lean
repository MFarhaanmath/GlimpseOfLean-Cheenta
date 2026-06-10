import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Cheenta_Proofs.BasicLemmasforCD

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

public section
open Set Filter Function

open Filter Topology

universe u v

variable {X : Type u} [TopologicalSpace X]

def Covering_Dimension (n : ℕ) : Prop :=
  ∀ (ι : Type*) [Fintype ι] (u : ι → Set X),
    IsOpenCover u →
    ∃ (κ : Type*) (_ : Fintype κ) (v : κ → Set X),
      IsOpenCover v ∧
      Refines v u ∧
      HasOrderLE v n

def Covering_Dimension_General (n : ℕ) : Prop :=
  ∀ (ι : Type v) (u : ι → Set X),
    IsOpenCoverGeneral u →
    ∃ (κ : Type*) (v : κ → Set X),
      IsOpenCoverGeneral v ∧
      RefinesGeneral v u ∧
      HasOrderLEGeneral_2 v n
