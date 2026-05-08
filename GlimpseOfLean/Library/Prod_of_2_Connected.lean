import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions

open Set

variable {X : Type*} [TopologicalSpace X]
variable {A B : Set X}

lemma product_of_connected
    (hA : IsConnected A) (hB : IsConnected B) (x : A) (y : B) :
    IsConnected (A ×ˢ B) := by
  unfold IsConnected at *
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  constructor
  · exact ⟨(x, y), x.property, y.property⟩
  · exact hA2.prod hB2


lemma product_of_connected (hA : IsConnected A) (hB : IsConnected B) :
  IsConnected (A ×ˢ B) := by
  rcases hA with ⟨hA_pre, hA_nonempty⟩
  rcases hB with ⟨hB_pre, hB_nonempty⟩

  constructor

  · -- prove preconnected
    intro U V hU hV hUV hVU hcover
    by_cases hAU : (A ×ˢ B) ∩ U = ∅
    · left
      ext z
      constructor
      · intro hz
        have : z ∈ (A ×ˢ B) ∩ U := ⟨hz, hU hz⟩
        exact False.elim (hAU this)
      · intro hz
        exact False.elim hz

    · right
      intro hVempty

      have hUnion :
          (A ×ˢ B) ⊆ U := by
        intro z hz
        have hzUV := hcover hz
        rcases hzUV with hzU | hzV
        · exact hzU
        · exfalso
          exact hVempty ⟨hz, hzV⟩

      have hEmpty : (A ×ˢ B) ∩ U = ∅ := by
        ext z
        constructor
        · intro hz
          exact hVU hz.1 hz.2
        · intro hz
          exact False.elim hz

      exact hAU hEmpty

  · -- prove nonempty
    rcases hA_nonempty with ⟨a, ha⟩
    rcases hB_nonempty with ⟨b, hb⟩
    exact ⟨(a, b), ⟨ha, hb⟩⟩