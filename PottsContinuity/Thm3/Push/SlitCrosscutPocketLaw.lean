module

public import PottsContinuity.Thm3.Push.SlitCrosscutPocketGeometry

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit PlanarMixed.Square
noncomputable section
local instance slitPocketEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Remove exactly the unseeded pockets of either actual slit crosscut. -/
def slitCrosscutPocketCarrier {M : ℕ} {x y : ℤ} (D : CrosscutData M x y) : Set (Vertex M x) :=
  closedCutExterior (graph M x y) {w | w ∈ D.first.support} (alpha M x ∪ beta M x y) ∩
  closedCutExterior (graph M x y) {w | w ∈ D.second.support} (alpha M x ∪ beta M x y)

end
end PottsContinuity.Push
