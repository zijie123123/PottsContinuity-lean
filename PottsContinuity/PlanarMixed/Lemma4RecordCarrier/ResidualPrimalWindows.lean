module

public import PottsContinuity.PlanarMixed.Lemma4Connectors.PrimalWindow
public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.ActualNativeDualLaw

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK RSW
noncomputable section
local instance routeSevenResidualEdgeEq {U : Type*} (G : SimpleGraph U) : DecidableEq G.edgeSet := Classical.decEq _

/-- Delete every queried bond before testing a literal primal crossing. -/
def residualPrimalWindowNoncrossing (V : Finset (ℤ × ℤ))
    (R : Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) (l r b t : ℤ) :
    Set (Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :=
  (fun A => A \ R) ⁻¹' primalWindowNoncrossing V Set.univ l r b t

/-- A connector on the native sample includes only its sampled original bonds. -/
def nativePrimalWindowNoncrossing (V : Finset (ℤ × ℤ))
    (R : Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) (l r b t : ℤ) :
    Set (Configuration (edgeRestriction (squareLattice.induce (V : Set (ℤ × ℤ))) R)) :=
  (fun C => (edgeRestrictionConfigurationEquiv _ R C).val) ⁻¹'
    primalWindowNoncrossing V Set.univ l r b t

theorem nativePrimalWindowNoncrossing_isLowerSet (V : Finset (ℤ × ℤ))
    (R : Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) (l r b t : ℤ) :
    IsLowerSet (nativePrimalWindowNoncrossing V R l r b t) := by
  intro A B hAB hB
  exact (primalWindowNoncrossing_isLowerSet V Set.univ l r b t)
    ((edgeRestrictionConfigurationEquiv_le_iff _ R B A).mpr hAB) hB

/-- The three source windows on the actual joint stopping record. -/
def lemma4ActualResidualConnectors (n : ℕ) (record : Configuration (lemma4AmbientGraph n)) :
    Set (Configuration (lemma4AmbientGraph n)) :=
  {A | ∀ j : Fin 3, A ∈ residualPrimalWindowNoncrossing (box (56*n))
    (lemma4JointSourceReveal n record) ((10*(j:ℤ)-13)*(n:ℤ))
      ((10*(j:ℤ)-7)*(n:ℤ)) (-3*(n:ℤ)) (3*(n:ℤ))}

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
