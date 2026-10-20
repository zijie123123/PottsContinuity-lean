module

public import PottsContinuity.PlanarMixed.CrosscutOrderedPair
public import PottsContinuity.PlanarMixed.OrderedCutActive
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-! The induced band between actual ordered square-crossing walks.
All ordered-cut geometry is now proved; no walk-separation or exterior
partition interface is assumed by these consumers.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

section
variable (N : ℕ) {a b t u : RectangleVertex (0,0) N N}
variable (p : (rectangleGraph (0,0) N N).Walk a t)
variable (q : (rectangleGraph (0,0) N N).Walk b u)
variable (ha : a.val.2 = 0) (hb : b.val.2 = 0)
variable (ht : t.val.2 = (N : ℤ)) (hu : u.val.2 = (N : ℤ))
variable (hab : a.val.1 < b.val.1) (hdis : ∀ z ∈ p.support, z ∉ q.support)

/-- Accessible-component labels of the domain between the actual two cuts. -/
def squareCrosscutRank : RectangleVertex (0,0) N N → ℤ :=
  orderedCutRank (rectangleGraph (0,0) N N)
    (Square.squareLeftArc (0,0) N) (Square.squareRightArc (0,0) N)
    {z | z ∈ p.support} {z | z ∈ q.support}
    (orderedCutPair_of_square_crosscuts N p q ha hb ht hu hab hdis)

local notation "rank" => squareCrosscutRank N p q ha hb ht hu hab hdis

end
end
end PottsContinuity.PlanarMixed
