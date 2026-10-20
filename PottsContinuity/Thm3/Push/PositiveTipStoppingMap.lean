module

public import PottsContinuity.Thm3.Push.PositiveTipOneSidedLocality
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

@[expose] public section

namespace PottsContinuity.Push
open PD.FK Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance positiveTipStoppingEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Classical.decEq _
local instance positiveTipStoppingEdgeFintype (n : ℕ) :
    Fintype (rectangleGraph (0,0) (2*n) (2*n)).edgeSet := Fintype.ofFinite _

/-- The original source bonds observed for a successful positive tip. -/
def caseTwoTipRightReveal (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (tip : SideCollarFirstHitRecord (5*s) (2*n))
    (v : RectangleVertex (0,0) (2*n) (2*n)) :
    Configuration (rectangleGraph (0,0) (2*n) (2*n)) :=
  rectangleSlitBonds (2*n) (2*n) (4*(s:ℤ)) v.val.2 ∪
    internalBonds (rectangleGraph (0,0) (2*n) (2*n))
      (pocketAugmentedSourceRightExterior (2*n) (2*n) (4*(s:ℤ)) v.val.2
        (sourceCoordinateTrace (2*n) (2*n)
          (Subtype.val '' {z | z ∈ caseTwoTipOriginalTrace n s hfit tip})))

end
end PottsContinuity.Push
