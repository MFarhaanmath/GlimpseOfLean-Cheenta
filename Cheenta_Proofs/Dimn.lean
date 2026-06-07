import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Topology.Separation.Regular

variable {X : Type}

axiom DimLe : Set X → ℕ → Prop

axiom dimLe_succ_split {S : Set X} {n : ℕ} :
  DimLe S (n + 1) ↔ ∃ A B : Set X, S = A ∪ B ∧ DimLe A 0 ∧ DimLe B n

set_option linter.style.whitespace false
theorem dimension_decomposition (S : Set X) (n : ℕ) :
  DimLe S n ↔ ∃ Xs : Fin (n + 1) → Set X, S = (⋃ i, Xs i) ∧ ∀ i, DimLe (Xs i) 0 := by
  induction n generalizing S with
  | zero =>
    constructor
    · intro h
      refine ⟨fun _ => S, ?_, fun _ => h⟩
      ext x
      simp only [Set.mem_iUnion]
      exact ⟨fun hx => ⟨0, hx⟩, fun ⟨_, hx⟩ => hx⟩
    · rintro ⟨Xs, rfl, hDim⟩
      have H : (⋃ i, Xs i) = Xs 0 := by
        ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨i, hx⟩
          have : i = 0 := by
            rcases i with ⟨val, hval⟩
            ext
            omega
          rwa [this] at hx
        · intro hx
          exact ⟨0, hx⟩
      exact H.symm ▸ hDim 0
  | succ n ih =>
    constructor
    · rintro h
      rcases dimLe_succ_split.mp h with ⟨A, B, rfl, hA, hB⟩
      rcases (ih B).mp hB with ⟨Ys, rfl, hYs⟩
      refine ⟨Fin.cases A Ys, ?_, fun i => Fin.cases hA hYs i⟩
      ext x
      simp only [Set.mem_union, Set.mem_iUnion]
      constructor
      · rintro (hx | ⟨i, hx⟩)
        · exact ⟨0, hx⟩
        · exact ⟨Fin.succ i, hx⟩
      · rintro ⟨i, hx⟩
        exact Fin.cases (fun h => Or.inl h) (fun (j : Fin (n + 1)) h => Or.inr ⟨j, h⟩) i hx
    · rintro ⟨Xs, rfl, hDim⟩
      apply dimLe_succ_split.mpr
      use Xs 0
      use ⋃ j : Fin (n + 1), Xs (Fin.succ j)
      refine ⟨?_, hDim 0, (ih _).mpr ⟨fun j : Fin (n + 1) => Xs (Fin.succ j), rfl, fun j : Fin (n + 1) => hDim (Fin.succ j)⟩⟩
      ext x
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨i, hx⟩
        exact Fin.cases (fun h => Or.inl h) (fun (j : Fin (n + 1)) h => Or.inr ⟨j, h⟩) i hx
      · rintro (hx | ⟨j, hx⟩)
        · exact ⟨0, hx⟩
        · exact ⟨Fin.succ j, hx⟩
