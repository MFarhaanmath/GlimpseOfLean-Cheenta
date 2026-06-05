import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular
import Cheenta_Proofs.BasicLemmasforCD

/-
Copyright (c) 2026 Cheenta Lean Project. All rights reserved.
Authors : Adhiraj Anand, Niranjan Rao, Parum Sarda, Shravas Matta, Shreesh Nayak, Shreya Iyer
-/

public section
open Set Filter Function

open Filter Topology

universe u v w

variable {X : Type u} [TopologicalSpace X]

def Covering_Dimension (n : ℕ) : Prop :=
  ∀ (ι : Type v) [Fintype ι] (u : ι → Set X),
    IsOpenCover u →
    ∃ (κ : Type*) (_ : Fintype κ) (v : κ → Set X),
      IsOpenCover v ∧
      Refines v u ∧
      HasOrderLE v n


theorem subspaceOfDimension
    {Y : Set X}
    (hY : IsClosed Y)
    {n : ℕ}
    (hdim : Covering_Dimension (X := X) n) :
    Covering_Dimension (X := ↥Y) n := by
  unfold Covering_Dimension
  intro ι hι u hu
  -- nobody is contributing why
