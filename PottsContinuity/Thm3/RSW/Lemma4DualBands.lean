module

public import PottsContinuity.Thm3.RSW.FiniteClosedDualRectangle
public import PottsContinuity.Thm3.RSW.Lemma4MiddleReveal

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK

/-- The two exact source dual bands on integer face bases. Their physical
coordinates are the printed half-integer rectangles R-star-plus/minus. -/
def lemma4DualBandEvent (n : ℕ) : Fin 2 → Set (Configuration (lemma4AmbientGraph n)) :=
  Fin.cases
    (finiteClosedDualHorizontalRectangle (box (56*n))
      (-56*(n:ℤ)-1) (56*(n:ℤ)) (2*(n:ℤ)) (3*(n:ℤ)-1))
    (fun _ => finiteClosedDualHorizontalRectangle (box (56*n))
      (-56*(n:ℤ)-1) (56*(n:ℤ)) (-3*(n:ℤ)) (-2*(n:ℤ)-1))

/-- The actual source event B-n: both original annulus circuits and the two
confined original closed-dual band crossings. -/
def lemma4BandConstructionEvent (n : ℕ) : Set (Configuration (lemma4AmbientGraph n)) :=
  lemma4AnnulusPairEvent n ∩ (lemma4DualBandEvent n 0 ∩ lemma4DualBandEvent n 1)

/-- Both source dual band events are decreasing in the sampled original bonds. -/
theorem lemma4DualBandEvent_isLowerSet (n : ℕ) (i : Fin 2) :
    IsLowerSet (lemma4DualBandEvent n i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact finiteClosedDualHorizontalRectangle_isLowerSet _ _ _ _ _
  · exact finiteClosedDualHorizontalRectangle_isLowerSet _ _ _ _ _

end PottsContinuity.RSW
