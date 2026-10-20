module

public import PottsContinuity.PlanarMixed.OrderedCutConsumers
public import PottsContinuity.BD12.WiredArcRemoval
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Ordered-cut estimates after removing exposed path bonds

Removed bonds have endpoints in a single separately wired arc. Their sampled
states do not affect the event that the two entire arcs have an actual open
connection. Thus the estimate lives on the remaining carrier, without
resampling bonds fixed by an exploration record.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12 MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

/-- The actual arc observable is unchanged by forgetting prewired arc bonds,
even if the FK boundary includes additional wiring. -/
theorem arcsConnection_remainingLaw_eq {V : Type*} [Finite V]
    (G : SimpleGraph V) (θ : Parameters) (A C : Set V) (hAC : Disjoint A C)
    (hA : A.Nonempty) (hC : C.Nonempty)
    (η : BoundaryCondition V) (hη : (twoBlockBoundary A C hAC).partition ≤ η.partition)
    (R : Configuration G)
    (hR : ∀ (u v : V) (huv : G.Adj u v),
      (⟨s(u,v), G.mem_edgeSet.mpr huv⟩ : G.edgeSet) ∈ R →
        (twoBlockBoundary A C hAC).partition.r u v) :
    (remainingLaw G θ η R).toMeasure {ω | ω.val ∈ arcsConnectionEvent G A C} =
      measure G θ η (arcsConnectionEvent G A C) := by
  let : DecidableEq G.edgeSet := Classical.decEq _
  let split := fun ω : Configuration G => (configurationSplitEquiv G R ω).1
  have hsplit := law_map_remove G θ η R (fun u v huv he => hη (hR u v huv he))
  change (law G θ η).map split = _ at hsplit
  rw [← hsplit, PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top]
  congr 1
  ext ω
  let ζ := (configurationSplitEquiv G R ω).2
  have hrestore : (split ω).val ∪ ζ.val = ω :=
    (configurationSplitEquiv G R).symm_apply_apply ω
  have hevent := arcsConnectionEvent_union_removed A C hAC hA hC R hR (split ω).val ζ
  rw [hrestore] at hevent
  exact hevent.symm

section
variable (q : Set.Ici (1 : ℝ)) (a : LatticeVertex) (N : ℕ) (hN : 1 ≤ N)
variable (A C : Set (RectangleVertex a N N))
variable (hcuts : OrderedCutPair (rectangleGraph a N N)
  (Square.squareLeftArc a N) (Square.squareRightArc a N) A C)
include hN
local notation "rank" => orderedCutRank (rectangleGraph a N N)
  (Square.squareLeftArc a N) (Square.squareRightArc a N) A C hcuts
local notation "GΩ" => rankedBandGraph (rectangleGraph a N N) rank

end
end
end PottsContinuity.PlanarMixed
