-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/StripSmallestScale.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteEnergy
public import PottsContinuity.FKC.Rectangle
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory

namespace PottsContinuity.FKC.FiniteFK
noncomputable section

def stripSmallGraph : SimpleGraph (RectangleVertex (-1, 0) 2 1) :=
  rectangleGraph (-1, 0) 2 1

def stripSmallBottomVertex : RectangleVertex (-1, 0) 2 1 :=
  ⟨(0, 0), by rw [mem_latticeRectangle]; norm_num⟩

def stripSmallTopVertex : RectangleVertex (-1, 0) 2 1 :=
  ⟨(0, 1), by rw [mem_latticeRectangle]; norm_num⟩

 theorem stripSmallVerticalAdj :
    stripSmallGraph.Adj stripSmallBottomVertex stripSmallTopVertex := by
  apply (rectangleGraph_adj_iff (-1, 0) 2 1 _ _).2
  rw [squareLattice_adj_iff]
  simp [stripSmallBottomVertex, stripSmallTopVertex]

def stripSmallVerticalEdge : stripSmallGraph.edgeSet :=
  ⟨s(stripSmallBottomVertex, stripSmallTopVertex),
    stripSmallGraph.mem_edgeSet.mpr stripSmallVerticalAdj⟩

/-- The literal actual-open connection between the origin and the top point of
the width-two, height-one rectangle used for the smallest-scale base case. -/
def stripSmallOriginTopConnectionEvent : Set (Configuration stripSmallGraph) :=
  {A | ActualConnected stripSmallGraph A stripSmallBottomVertex stripSmallTopVertex}

/-- In the smallest rectangle, the actual vertical edge gives a connection
probability at least the uniform FK one-edge lower bound, for every boundary
condition. -/
theorem stripSmallOriginTopConnection_probability_ge_lambda
    (q : ClusterWeight) (ξ : BoundaryCondition (RectangleVertex (-1, 0) 2 1)) :
    1 / (1 + loopWeight q) ≤
      (measure stripSmallGraph q ξ stripSmallOriginTopConnectionEvent).toReal := by
  have hfinite := configurationProbability_edge_finite_energy q ξ Set.univ
    stripSmallVerticalAdj (by intro A; simp)
  have hopen :
      1 / (1 + loopWeight q) ≤
        (measure stripSmallGraph q ξ {A | stripSmallVerticalEdge ∈ A}).toReal := by
    simpa [stripSmallVerticalEdge] using hfinite.1
  have hsubset :
      {A | stripSmallVerticalEdge ∈ A} ⊆ stripSmallOriginTopConnectionEvent := by
    intro A hA
    apply actualConnected_of_adj
    apply (openGraph_adj stripSmallGraph A _ _).2
    exact ⟨stripSmallVerticalEdge, hA, rfl⟩
  let μ := measure stripSmallGraph q ξ
  have hmeasure : μ {A | stripSmallVerticalEdge ∈ A} ≤
      μ stripSmallOriginTopConnectionEvent := MeasureTheory.measure_mono (μ := μ) hsubset
  have hreal := ENNReal.toReal_mono
    (measure_ne_top μ stripSmallOriginTopConnectionEvent) hmeasure
  exact hopen.trans hreal

/-- The smallest-scale actual connection has probability strictly above both
`1/3` and the weaker `1/5` bound, uniformly over all boundary conditions. -/
theorem stripSmallOriginTopConnection_probability_gt_constants
    (q : ClusterWeight) (ξ : BoundaryCondition (RectangleVertex (-1, 0) 2 1)) :
    (1 / 3 : ℝ) <
        (measure stripSmallGraph q ξ stripSmallOriginTopConnectionEvent).toReal ∧
      (1 / 5 : ℝ) <
        (measure stripSmallGraph q ξ stripSmallOriginTopConnectionEvent).toReal := by
  have hLower := stripSmallOriginTopConnection_probability_ge_lambda q ξ
  have hLowerThird : (1 / 3 : ℝ) < 1 / (1 + loopWeight q) := by
    rw [div_lt_div_iff₀ (by norm_num) (one_add_loopWeight_pos q)]
    norm_num
    linarith [loopWeight_lt_two q]
  constructor <;> linarith [hLower, hLowerThird]

end
end PottsContinuity.FKC.FiniteFK
