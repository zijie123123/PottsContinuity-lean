module

public import PottsContinuity.PlanarMixed.Square.Consumers
public import PottsContinuity.PlanarMixed.Square.RectangleDualHorizontalCoreLaw
public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.PlanarMixed.Square.Extras
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.Duality BD12 Square MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Exact transposed primal/dual exclusion, on the true rectangle dual graph. -/
theorem squareVerticalCrossing_excludes_dualHorizontal (z : ℤ) (N : ℕ)
    (A : Configuration (rectangleGraph (z,z) N N))
    (hV : A ∈ rectangleVerticalCrossingEvent (z,z) N N) :
    rectanglePrimalDualConfigurationEquiv (z,z) N N A ∉ squareDualHorizontalCrossingEvent z N := by
  intro hD
  let P := squarePrimalGraphSwapIso z N
  let D := squareDualGraphSwapIso z N
  have hH : configurationIso P A ∈ rectangleHorizontalCrossingEvent (z,z) N N := by
    apply (rectangleHorizontalCrossingEvent_coordinateSwap_iff (z,z) N N (configurationIso P A)).mpr
    change configurationIso P (configurationIso P A) ∈ rectangleVerticalCrossingEvent (z,z) N N
    rwa [squarePrimalConfigurationSwap_twice]
  obtain ⟨u,v,hu,hv,hconn⟩ := hD
  apply rectanglePrimalDualCrossings_exclusive (z,z) N N (configurationIso P A) hH
  refine ⟨D u,D v,?_,?_,?_⟩
  · exact hu
  · exact hv
  · have hmap := (actualConnected_configurationIso D
      (rectanglePrimalDualConfigurationEquiv (z,z) N N A) u v).mpr hconn
    rw [squarePrimalDualConfiguration_swap_commute] at hmap
    convert! hmap using 1

/-- A literal horizontal crossing on the true dual horizontal core. -/
def referenceDualCoreHorizontalCrossing (z : ℤ) (N : ℕ) :
    Set (Configuration (rectangleDualHorizontalCoreGraph (z,z) N N)) :=
  {C | ∃ u v : rectangleDualHorizontalCoreVertex (z,z) N N,
    u.val.val.1=z-1 ∧ v.val.val.1=z+(N:ℤ) ∧ ActualConnected _ C u v}

/-- The reference native horizontal core has the square noncrossing lower
bound. The core removes only true top/bottom dual leaves. -/
theorem referenceDualCore_noncrossing_lower
    (q : Set.Ici (1:ℝ)) (z : ℤ) (N : ℕ) (hN : 1 ≤ N) :
    1/(1+(q:ℝ)^2) ≤
      (measure (rectangleDualHorizontalCoreGraph (z,z) N N) (criticalParameters q)
        (BoundaryCondition.wired {u : rectangleDualHorizontalCoreVertex (z,z) N N |
          rectangleDualHorizontalCoreInclusion (z,z) N N u ∈
            rectangleDoubleCollarDualInnerVerticalSides (z,z) N N})
        (referenceDualCoreHorizontalCrossing z N)ᶜ).toReal := by
  let G := rectangleGraph (z,z) N N
  let H := rectangleDualHorizontalCoreGraph (z,z) N N
  let ξ := twoBlockBoundary (rectangleDoubleCollarInnerBottom (z,z) N N)
    (rectangleDoubleCollarInnerTop (z,z) N N)
    (rectangleDoubleCollarInnerBottom_disjoint_top (z,z) N N hN)
  let η := BoundaryCondition.wired {u : rectangleDualHorizontalCoreVertex (z,z) N N |
    rectangleDualHorizontalCoreInclusion (z,z) N N u ∈ rectangleDoubleCollarDualInnerVerticalSides (z,z) N N}
  let read := fun A : Configuration G => embeddedConfigurationRestriction H (rectangleDualGraph (z,z) N N)
    (rectangleDualHorizontalCoreInclusion (z,z) N N) (rectangleDualHorizontalCoreGraph_map_le (z,z) N N)
    (rectanglePrimalDualConfigurationEquiv (z,z) N N A)
  have hlaw : (law G (criticalParameters q) ξ).map read=law H (criticalParameters q) η := by
    rw [show read = (embeddedConfigurationRestriction H _ _ (rectangleDualHorizontalCoreGraph_map_le (z,z) N N)) ∘
      rectanglePrimalDualConfigurationEquiv (z,z) N N from rfl,← PMF.map_comp]
    rw [rectangleDoubleCollar_mixedDuality_law_map (z,z) N N hN q]
    exact rectangleDualHorizontalCoreGraph_law_map (z,z) N N hN (criticalParameters q)
  have hsub : rectangleVerticalCrossingEvent (z,z) N N ⊆ read ⁻¹' (referenceDualCoreHorizontalCrossing z N)ᶜ := by
    intro A hA hC
    obtain ⟨u,v,hu,hv,hconn⟩ := hC
    apply squareVerticalCrossing_excludes_dualHorizontal z N A hA
    refine ⟨u.val,v.val,hu,hv,?_⟩
    let i := rectangleDualHorizontalCoreInclusion (z,z) N N
    let f : openGraph H (read A) →g openGraph (rectangleDualGraph (z,z) N N)
        (rectanglePrimalDualConfigurationEquiv (z,z) N N A) :=
      { toFun := i, map_rel' := by
          intro x y hxy
          obtain ⟨e,he,heq⟩ := (openGraph_adj H (read A) x y).mp hxy
          have hem := (mem_embeddedConfigurationRestriction H _ i
            (rectangleDualHorizontalCoreGraph_map_le (z,z) N N) _ e).mp he
          apply (openGraph_adj _ _ (i x) (i y)).mpr
          refine ⟨_,hem,?_⟩
          rw [embeddedEdgeEmbedding_coe,heq]
          rfl }
    exact hconn.map f
  have hmass := congrArg (fun ρ : PMF (Configuration H) => ρ.toMeasure (referenceDualCoreHorizontalCrossing z N)ᶜ) hlaw
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hmass
  apply (square_separateVertical_ge_inv_one_add_q_sq q z N hN).trans
  change (measure G (criticalParameters q) ξ _).toReal ≤ _
  rw [show measure H (criticalParameters q) η (referenceDualCoreHorizontalCrossing z N)ᶜ =
    (law G (criticalParameters q) ξ).toMeasure (read ⁻¹' (referenceDualCoreHorizontalCrossing z N)ᶜ) from hmass.symm]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
