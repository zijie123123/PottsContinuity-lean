module

public import PottsContinuity.Thm3.Push.ClosedPathTransfer
public import PottsContinuity.Thm3.Push.RectangleTopFrontier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance replacementPropDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance replacementEdgeDecidableEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Open cut bonds replace the portions of a reference crossing in the upper
region. The conclusion is an ACTUAL crossing of the same target rectangle;
no claim that the lower random domain contains that rectangle is required.
The two structural premises are literal bond-state retention conditions. -/
theorem rectangle_crossing_of_cut_restoration (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleDualVertex a w h → Bool)
    (hbottom : ∀ b ∈ rectangleDualBottomPorts a w h, σ b = false)
    (A B : Configuration (rectangleGraph a w h))
    (hcut : auxiliaryLabelCut (DualityExt.rectangleDualEdgeEquiv a w h) σ ⊆ A)
    (hout : ∀ f : (rectangleGraph a w h).edgeSet,
      (∀ z ∈ (DualityExt.rectangleDualEdgeEquiv a w h f).val, σ z = false) →
      f ∈ B → f ∈ A)
    (hB : B ∈ rectangleHorizontalCrossingEvent a w h) :
    A ∈ rectangleHorizontalCrossingEvent a w h := by
  by_contra hno
  obtain ⟨b, hb, t, ht, hconn⟩ :=
    rectangleDualBottomTop_of_no_primal_horizontal_crossing a w h A hno
  rw [← auxiliaryClosedConfiguration_rectangle_eq] at hconn
  have htransfer := (auxiliaryClosed_path_transfer_below_cut
    (DualityExt.rectangleDualEdgeEquiv a w h) σ A B hcut hout (hbottom b hb) hconn).2
  rw [auxiliaryClosedConfiguration_rectangle_eq] at htransfer
  have hby : b.val.2 = a.2-1 := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
    rfl
  have hty : t.val.2 = a.2+(h : ℤ) := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    rfl
  exact rectanglePrimalDualCrossings_exclusive a w h B hB ⟨b,t,hby,hty,htransfer⟩

end
end PottsContinuity.Push
