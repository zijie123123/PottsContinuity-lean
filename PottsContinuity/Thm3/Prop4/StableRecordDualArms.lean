module

public import PottsContinuity.Thm3.Prop4.FrozenFiberDualArms
public import PottsContinuity.Thm3.Prop4.TranslatedWindowIso
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

/-!
# Actual dual-arm correlation under a stable exploration record

The law is obtained by conditioning the original finite FK PMF on the
complete attained record, then retaining the remaining sampled edges.
The exact DMP identifies it with the normalized fixed-state fiber.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace

local instance stableRecordDualArmsEdgeDecidableEq (V : Finset LatticeVertex) :
    DecidableEq (squareLattice.induce (V : Set LatticeVertex)).edgeSet := Classical.decEq _

/-- The genuine conditional remaining-edge PMF on a complete attained stable record. -/
def stableRecordRemainingLaw (V : Finset LatticeVertex) (θ : Parameters)
    (ξ : BoundaryCondition (V : Set LatticeVertex))
    (reveal : Configuration (squareLattice.induce (V : Set LatticeVertex)) →
      Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration (squareLattice.induce (V : Set LatticeVertex))) :
    PMF (RemainingConfiguration (squareLattice.induce (V : Set LatticeVertex)) (reveal C₀)) :=
  ((law _ θ ξ).filter (Exploration.revealRecordEvent reveal C₀) (by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
    exact frozenStateEvent_support θ ξ (reveal C₀) (Exploration.revealRecordConfiguration reveal C₀))).map
    (fun C => (configurationSplitEquiv _ (reveal C₀) C).1)

/-- The record law is exactly the proved fixed frozen fiber, including its true partition. -/
theorem stableRecordRemainingLaw_eq_frozenFiberLaw (V : Finset LatticeVertex) (θ : Parameters)
    (ξ : BoundaryCondition (V : Set LatticeVertex))
    (reveal : Configuration (squareLattice.induce (V : Set LatticeVertex)) →
      Configuration (squareLattice.induce (V : Set LatticeVertex)))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration (squareLattice.induce (V : Set LatticeVertex))) :
    stableRecordRemainingLaw V θ ξ reveal hstable C₀ =
      frozenFiberLaw θ ξ (reveal C₀) (Exploration.revealRecordConfiguration reveal C₀) := by
  unfold stableRecordRemainingLaw
  rw [Exploration.law_filter_revealRecord_map_remaining θ ξ reveal hstable C₀]
  exact (frozenFiberLaw_eq_remainingLaw θ ξ (reveal C₀)
    (Exploration.revealRecordConfiguration reveal C₀)).symm

end
end PottsContinuity.Thm3.Prop4
