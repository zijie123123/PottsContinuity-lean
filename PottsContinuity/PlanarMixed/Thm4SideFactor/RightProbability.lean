module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightReducedEmbedding
public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushReduced
public import PottsContinuity.PlanarMixed.Thm4SideFactor.DirectSideAverage
public import PottsContinuity.Thm4SideEuler.HostDualDomination

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open MeasureTheory PD.FK PD.Duality DualityExt Thm4Side Thm4SideEuler
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance rightProbabilitySourceEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

abbrev rightNativeHostGraph (m : ℕ)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  rectangleSubgraphDualGraph (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))

abbrev rightNativeHostBoundary (m : ℕ)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  frozenBoundary
    (rectangleDualBoundaryCondition
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)))
    (rectangleSubgraphDualOpenRemovedState
      (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))
      (slitRightDualRectangleHostRemovedState m X)).val

theorem nativeSideReduced_probability_le_rightResidual_of_boundary_and_surgery
    (q : Set.Icc (1 : ℝ) 4) (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hpart : ∀ K : Configuration (rightNativeHostGraph m X),
      (nativeSideFullBoundary m).partition ≤
        (isolatedExtensionPullbackBoundary (rightNativeToHostDual m)
          (frozenBoundary (rightNativeHostBoundary m X) K)).partition)
    (hsurgery : ∀ D : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m))
        (slitRightDualRectangleReveal m X),
      embeddedConfigurationRestriction (nativeSideReducedGraph m) (rightNativeHostGraph m X)
        (rightNativeToHostDual m) (rightNativeReduced_map_le_hostDual m hm X)
        (slitRightResidualToHostDual m X D) ∈ nativeSideReducedCrossingEvent m →
      D.val ∪ (X ∩ slitRightDualRectangleRevealEdges m) ∈
        FKC.FiniteFK.slitScreenRightCrossingEvent m) :
    (measure (nativeSideReducedGraph m) (RSW.selfDualParameters (⟨q,q.2.1⟩ : Set.Ici (1:ℝ)))
      (nativeSideFullBoundary m) (nativeSideReducedCrossingEvent m)).toReal ≤
        slitRightResidualCrossingProbability q m X := by
  let G := FKC.FiniteFK.slitBoxGraph (16*m)
  let J := nativeSideReducedGraph m
  let H := rightNativeHostGraph m X
  let θ := criticalParameters (⟨q,q.2.1⟩ : Set.Ici (1:ℝ))
  let ξ := rightNativeHostBoundary m X
  let f := rightNativeToHostDual m
  let hsub := rightNativeReduced_map_le_hostDual m hm X
  let E := nativeSideReducedCrossingEvent m
  let restr : Configuration H → Configuration J := embeddedConfigurationRestriction J H f hsub
  let R := slitRightDualRectangleReveal m X
  let μ := remainingLaw G θ
    (frozenBoundary (Thm4.fkcBoundaryToPD (FKC.FiniteFK.slitBoxBoundary (16*m)))
      (Exploration.revealRecordConfiguration (slitRightDualRectangleReveal m) X).val) R
  let T : Set (Configuration H) := {C | restr C ∈ E}
  have hpart' : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (J.map f) H),
      (nativeSideFullBoundary m).partition ≤
        (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition :=
    fun K => hpart K.val
  have hbound := embeddedConfigurationRestriction_preimage_measure_ge_of_frozen_partition
    J H f hsub θ ξ (nativeSideFullBoundary m) E
    (nativeSideReducedCrossingEvent_isUpperSet m) hpart'
  have hmap : μ.map (slitRightResidualToHostDual m X) = law H θ ξ :=
    slitRight_residual_hostDual_law_named m (⟨q,q.2.1⟩ : Set.Ici (1:ℝ)) X
  have hmass : measure H θ ξ T = μ.toMeasure ((slitRightResidualToHostDual m X) ⁻¹' T) := by
    change (law H θ ξ).toMeasure T = _
    rw [← hmap]
    exact PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top
  calc
    (measure J θ (nativeSideFullBoundary m) E).toReal ≤ (measure H θ ξ T).toReal := hbound
    _ = (μ.toMeasure ((slitRightResidualToHostDual m X) ⁻¹' T)).toReal := congrArg ENNReal.toReal hmass
    _ ≤ slitRightResidualCrossingProbability q m X := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro D hD
      exact hsurgery D hD

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
