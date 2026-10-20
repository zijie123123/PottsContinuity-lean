module

public import PottsContinuity.PlanarMixed.FiniteSlit.ReferenceBound
public import PottsContinuity.PlanarMixed.FiniteSlit.OmegaComparison
public import PottsContinuity.Thm3.RSW.StoppedConnection

/-! Finite Case 2 consumers with the reference estimate fully discharged.
Only actual source geometry and exploration identification remain explicit. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK BD12 Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance finiteSlitReferenceConsumersEdgeDecidableEq {U : Type*} (G : SimpleGraph U) :
    DecidableEq G.edgeSet := Classical.decEq _

section Geometry
variable (q : Set.Ici (1 : ℝ))
  (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
  {W : Type*} [Finite W] (H : SimpleGraph W)
  (i : W ↪ Vertex M x) (hH : H.map i ≤ graph M x y)
  (G1 G2 : Set W) (hdis : Disjoint G1 G2) (η : BoundaryCondition W)
  (hη : (twoBlockBoundary G1 G2 hdis).partition ≤ η.partition)
  (hpaths : ∀ C ∈ connectionEvent M x y,
    embeddedConfigurationRestriction H (graph M x y) i hH C ∈
      arcsConnectionEvent H G1 G2)
  (hpart : ∀ K : RemovedConfiguration (graph M x y)
      (subgraphRemovedEdges (H.map i) (graph M x y)),
    (isolatedExtensionPullbackBoundary i
      (frozenBoundary (boundary M x y hM hy hyM) K.val)).partition ≤
        (twoBlockBoundary G1 G2 hdis).partition)

include i hH hdis hη hpaths hpart in
/-- Case 2 Omega estimate with only its actual source geometric inputs.
The finite reference probability estimate is proved, not a premise. -/
theorem omega_lower_bound_of_geometry :
    1/(1+(q : ℝ)^2) ≤
      (measure H (criticalParameters q) η (arcsConnectionEvent H G1 G2)).toReal := by
  exact omega_connection_lower_bound_of_referenceBound_and_geometry M x y hM hy hyM
    H i hH G1 G2 hdis q η hη
    (wired_arcs_lower_bound q M x y hM hy hyM)
    hpaths hpart

include i hH hdis hη hpaths hpart in
/-- The finite Case 2 estimate evaluated on an actual remaining-edge law. -/
theorem remaining_connection_lower_bound_of_geometry
    {U : Type*} [Finite U] (G : SimpleGraph U) (ζ : BoundaryCondition U)
    (R : Configuration G) (r : RemainingConfiguration G R → Configuration H)
    (hmap : (remainingLaw G (criticalParameters q) ζ R).map r =
      law H (criticalParameters q) η) :
    1/(1+(q : ℝ)^2) ≤
      ((remainingLaw G (criticalParameters q) ζ R).toMeasure
        (r ⁻¹' arcsConnectionEvent H G1 G2)).toReal := by
  have h := congrArg (fun ρ : PMF (Configuration H) =>
    ρ.toMeasure (arcsConnectionEvent H G1 G2)) hmap
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
    MeasurableSpace.measurableSet_top] at h
  rw [h]
  exact omega_lower_bound_of_geometry q M x y hM hy hyM
    H i hH G1 G2 hdis η hη hpaths hpart

include i hH hdis hη hpaths hpart in
/-- The stable-reveal DMP of `Exploration.FiniteStoppingSetDMP` and the proved
finite reference estimate give the conditional source bound from actual Omega geometry
and target surgery. -/
theorem stopped_connection_lower_bound_of_geometry
    {U : Type*} [Finite U] (G : SimpleGraph U) (ζ : BoundaryCondition U)
    (reveal : RevealMap (G := G))
    (hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C)
    (C₀ : Configuration G)
    (r : RemainingConfiguration G (reveal C₀) → Configuration H)
    (hmap : (remainingLaw G (criticalParameters q)
      (frozenBoundary ζ (revealRecordConfiguration reveal C₀).val) (reveal C₀)).map r =
        law H (criticalParameters q) η)
    (S : Set (Configuration G))
    (hsurgery : ∀ C ∈ revealRecordEvent reveal C₀,
      r ((configurationSplitEquiv G (reveal C₀) C).1) ∈ arcsConnectionEvent H G1 G2 → C ∈ S) :
    1/(1+(q : ℝ)^2) ≤
      (((law G (criticalParameters q) ζ).filter (revealRecordEvent reveal C₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C₀]
          exact frozenStateEvent_support (criticalParameters q) ζ (reveal C₀)
            (revealRecordConfiguration reveal C₀))).toMeasure S).toReal := by
  exact RSW.stopped_connection_lower_of_remaining_bound (criticalParameters q) ζ reveal
    hstable C₀ (r ⁻¹' arcsConnectionEvent H G1 G2) S _
    (remaining_connection_lower_bound_of_geometry q M x y hM hy hyM
      H i hH G1 G2 hdis η hη hpaths hpart G
      (frozenBoundary ζ (revealRecordConfiguration reveal C₀).val) (reveal C₀) r hmap)
    hsurgery

end Geometry
end
end PottsContinuity.PlanarMixed.FiniteSlit
