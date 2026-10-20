module

public import PottsContinuity.Thm3.RSW.FiniteClosedDualMonotone

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.RCInfinite

/-- An actual horizontal closed-dual crossing on original face bases, with
its complete path confined to the specified closed integer rectangle. -/
def finiteClosedDualHorizontalRectangle (V : Finset LatticeVertex) (l r b t : ℤ) :
    Set (Configuration (squareLattice.induce (V : Set LatticeVertex))) :=
  {A | ∃ u v : LatticeVertex,
    ∃ p : (wholePlaneClosedDualGraph (finiteSubgraphConfiguration V 0 A)).Walk u v,
      u.1 = l ∧ v.1 = r ∧
      ∀ x ∈ p.support, l ≤ x.1 ∧ x.1 ≤ r ∧ b ≤ x.2 ∧ x.2 ≤ t}

/-- The original sampled closed-dual crossing is a decreasing event. -/
theorem finiteClosedDualHorizontalRectangle_isLowerSet
    (V : Finset LatticeVertex) (l r b t : ℤ) :
    IsLowerSet (finiteClosedDualHorizontalRectangle V l r b t) := by
  intro A B hAB hB
  obtain ⟨u,v,p,hu,hv,hp⟩ := hB
  refine ⟨u,v,p.mapLe (finite_closedDualGraph_antitone V hAB),hu,hv,?_⟩
  simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hp

end PottsContinuity.RSW
