module

public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction

/-! Concrete open square-crosscut data, shared by finite-host consumers.
The bundle records actual walks and their coordinates, not a separation,
boundary-law or probability conclusion. Its rank is constructed from the
proved ordered-cut geometry.
-/

@[expose] public section

namespace PottsContinuity.PlanarMixed
open PD.FK BD12
noncomputable section

/-- Actual open crossing walks with their coordinate data on a given graph. -/
structure OpenCrosscutPair {V : Type*} (G : SimpleGraph V)
    (coord : V → LatticeVertex) (height : ℤ) where
  state : Configuration G
  firstStart : V
  secondStart : V
  firstEnd : V
  secondEnd : V
  first : (openGraph G state).Walk firstStart firstEnd
  second : (openGraph G state).Walk secondStart secondEnd
  first_bottom : (coord firstStart).2 = 0
  second_bottom : (coord secondStart).2 = 0
  first_top : (coord firstEnd).2 = height
  second_top : (coord secondEnd).2 = height
  ordered : (coord firstStart).1 < (coord secondStart).1
  disjoint : ∀ z ∈ first.support, z ∉ second.support

/-- The same actual crossing data on the literal source square. -/
abbrev SquareCrosscutData (N : ℕ) :=
  OpenCrosscutPair (rectangleGraph (0,0) N N) Subtype.val (N : ℤ)

namespace SquareCrosscutData
variable {N : ℕ} (D : SquareCrosscutData N)

/-- All walk-separation facts are derived, not fields of the data. -/
theorem orderedCuts : OrderedCutPair (rectangleGraph (0,0) N N)
    (Square.squareLeftArc (0,0) N) (Square.squareRightArc (0,0) N)
    {v | v ∈ D.first.support} {v | v ∈ D.second.support} := by
  simpa only [openWalkUnderlying_support] using orderedCutPair_of_square_crosscuts N
    (openWalkUnderlying _ D.state D.first) (openWalkUnderlying _ D.state D.second)
    D.first_bottom D.second_bottom D.first_top D.second_top D.ordered
    (openWalkUnderlying_disjoint _ D.state D.first D.second D.disjoint)

/-- The exact accessible-component labels of this concrete pair. -/
def rank : RectangleVertex (0,0) N N → ℤ :=
  orderedCutRank (rectangleGraph (0,0) N N)
    (Square.squareLeftArc (0,0) N) (Square.squareRightArc (0,0) N)
    {v | v ∈ D.first.support} {v | v ∈ D.second.support} D.orderedCuts

theorem rank_first_iff (v : RectangleVertex (0,0) N N) :
    D.rank v = 1 ↔ v ∈ D.first.support := orderedCutRank_eq_one_iff D.orderedCuts v

theorem rank_second_iff (v : RectangleVertex (0,0) N N) :
    D.rank v = 3 ↔ v ∈ D.second.support := orderedCutRank_eq_three_iff D.orderedCuts v

theorem arcs_nonempty :
    (rankedBandFirstArc D.rank).Nonempty ∧ (rankedBandSecondArc D.rank).Nonempty := by
  have ha : D.rank D.firstStart = 1 := (D.rank_first_iff _).mpr D.first.start_mem_support
  have hb : D.rank D.secondStart = 3 := (D.rank_second_iff _).mpr D.second.start_mem_support
  constructor
  · refine ⟨⟨D.firstStart, ?_⟩, ha⟩
    change 1 ≤ D.rank D.firstStart ∧ D.rank D.firstStart ≤ 3
    omega
  · refine ⟨⟨D.secondStart, ?_⟩, hb⟩
    change 1 ≤ D.rank D.secondStart ∧ D.rank D.secondStart ≤ 3
    omega

end SquareCrosscutData
end
end PottsContinuity.PlanarMixed
