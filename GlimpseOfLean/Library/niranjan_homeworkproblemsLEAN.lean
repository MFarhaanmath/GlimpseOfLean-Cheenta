-- IMPORTS, VARIABLES AND DEFINITIONS --
import Mathlib.Topology.Basic
import Mathlib.Topology.Closure
import Mathlib.Topology.Constructions
import Mathlib.Data.Set.Prod

variable {X Y: Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (A B : Set X)

def MyIsClosed (s : Set X) : Prop :=
  IsOpen (sᶜ)

-- FIRST LEMMA --
omit [TopologicalSpace X] in
lemma intersectioninoriginalset : A ∩ B ⊆ A := by
    intro x hx
    rcases hx with ⟨hxA, hxB⟩
    exact hxA

-- SECOND LEMMA --
lemma arbitraryintersectionclosed {I : Type*} {f : I → Set X}
  (hf : ∀ i, MyIsClosed (f i)) : MyIsClosed (⋂ i, f i) := by

  -- Unfolding the predefined definition: We need to show IsOpen (⋂ i, f i)ᶜ
  unfold MyIsClosed at *

  -- Sir, I decided to use this simple identity to prove this lemma.
  -- Using the Set Theory identity (De Morgan): (⋂ f_i)ᶜ = ⋃ (f_iᶜ).
  rw [Set.compl_iInter]

  -- Using the fact that the union of open sets is open
  apply isOpen_iUnion

  -- Showing that each piece of the union (f i)ᶜ is open.
  intro i
  exact hf i

-- THIRD LEMMA --
lemma closureofprodequalprodofclosure : closure (A ×ˢ B) = closure A ×ˢ closure B := by
  -- We prove equality by showing each side is a subset of the other
  apply Set.Subset.antisymm -- (ChatGPT command)

  -- Direction 1: closure (A × B) ⊆ closure A × closure B
  · apply closure_minimal
    · -- Show A × B ⊆ closure A × closure B
      apply Set.prod_mono
      · exact subset_closure
      · exact subset_closure
    · -- Show that the product of two closed sets is closed
      apply IsClosed.prod
      · exact isClosed_closure
      · exact isClosed_closure

  -- Direction 2: closure A × closure B ⊆ closure (A × B)
  · intro ⟨x, y⟩ hx
    -- hx is (x ∈ closure A) and (y ∈ closure B)
    rw [mem_closure_iff_nhds]
    intro U hU
    -- In the product topology, a neighborhood U of (x, y)
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hU
    rcases hU with ⟨V, hV, W, hW, hsub⟩

    -- Since x is in closure A, every neighborhood V intersects A
    have hA := mem_closure_iff_nhds.mp hx.1 V hV
    -- Since y is in closure B, every neighborhood W intersects B
    have hB := mem_closure_iff_nhds.mp hx.2 W hW

    -- Extract points a ∈ V ∩ A and b ∈ W ∩ B
    rcases hA with ⟨a, haV, haA⟩
    rcases hB with ⟨b, hbW, hbB⟩

    -- Show that the point (a, b) is in (U ∩ A × B)
    use (a, b)
    constructor
    · -- (a, b) is in U because it's in V × W, which is a subset of U
      apply hsub
      exact ⟨haV, hbW⟩
    · -- (a, b) is in A × B
      exact ⟨haA, hbB⟩

-- Sir, I found this lemma harder to prove with just tactics, so, consulting the use
-- of ChatGPT I found inbuilt lemmas in LEAN that helped me prove this lemma.
-- You can simply hover over each lemma to find its statement which made it clear for
-- me as well. Thank you!

-- LAST LEMMA --
theorem continuous_seq_basic {f : X → Y} {x : X} {xn : ℕ → X}
  (hf : Continuous f)
  (hx : ∀ V, IsOpen V → x ∈ V → ∃ N, ∀ n ≥ N, xn n ∈ V) :
  ∀ W, IsOpen W → f x ∈ W → ∃ N, ∀ n ≥ N, f (xn n) ∈ W := by

  -- 1. Let W be an open neighborhood of f(x)
  intro W hW_open hfx_in_W

  -- 2. Because f is continuous, then the preimage  open in X
  let V := f ⁻¹' W
  have hV_open : IsOpen V := hf.isOpen_preimage W hW_open

  -- 3. Since f(x) ∈ W, we know x ∈ f⁻¹(W) (which is V)
  have hx_in_V : x ∈ V := hfx_in_W -- This is true by definition of preimage

  -- 4. Use our hypothesis hx: since V is an open neighborhood of x,
  -- the sequence xn is eventually in V.
  rcases hx V hV_open hx_in_V with ⟨N, hN⟩

  -- 5. Got the number N and hN. Now we are showing that for n ≥ N, f(xn) is in W.
  use N
  intro n hngreaterequaltoN

  -- 6. From hN, we know xn n is in V
  have hxn_inV := hN n hngreaterequaltoN

  -- 7. By definition of V (preimage), if xn n ∈ f⁻¹(W), then f(xn n) ∈ W
  exact hxn_inV

-- I apologise for any mistakes in the code or any naming confusion(s) (if any)
