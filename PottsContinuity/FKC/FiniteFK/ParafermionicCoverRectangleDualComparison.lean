-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverRectangleDualComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleBottomWiredDuality
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverRectangleBoundary

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory

noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance parafermionicDualComparisonStripEdgeFintype (n : ℕ) :
    Fintype (ParafermionicStripGraph n).edgeSet := Fintype.ofFinite _
local instance parafermionicDualComparisonStripEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicStripGraph n).edgeSet := Classical.decEq _
local instance parafermionicDualComparisonDualEdgeFintype (n : ℕ) :
    Fintype (rectangleDualBottomCollarInnerGraph n).edgeSet := Fintype.ofFinite _
local instance parafermionicDualComparisonDualEdgeDecidableEq (n : ℕ) :
    DecidableEq (rectangleDualBottomCollarInnerGraph n).edgeSet := Classical.decEq _
local instance parafermionicDualComparisonAmbientEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance parafermionicDualComparisonAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _

def parafermionicCoverStripDualRestriction (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ)) :
    Configuration (ParafermionicAmbientGraph n) →
      Configuration (rectangleDualBottomCollarInnerGraph n) :=
  rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n ∘
    embeddedConfigurationRestriction (ParafermionicStripGraph n)
      (ParafermionicAmbientGraph n)
      (parafermionicCoverStripEmbedding n k hk)
      (parafermionicCoverStrip_map_le n k hk)

/-- Complementation of primal edges reverses inclusion, so the primal
preimage of an increasing dual event is a lower set. -/
theorem rectanglePrimalDualPreimage_compl_isUpper
    (n : ℕ) (D : Set (Configuration (rectangleDualBottomCollarInnerGraph n)))
    (hD : IsUpperSet D) :
    IsUpperSet ((rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n ⁻¹' D)ᶜ) := by
  intro A B hAB hA hB
  change rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n A ∉ D at hA
  change rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n B ∈ D at hB
  apply hA
  apply hD
  · intro e he
    let d := (rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n).symm e
    have hdualB : rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n B =
        rectangleDualConfiguration (-(n:ℤ),0) (2*n) n B := by
      rw [rectanglePrimalDualConfigurationEquiv_apply]
      rfl
    have hdualA : rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n A =
        rectangleDualConfiguration (-(n:ℤ),0) (2*n) n A := by
      rw [rectanglePrimalDualConfigurationEquiv_apply]
      rfl
    have hmem : rectangleDualGraphEdgeEquiv (-(n:ℤ),0) (2*n) n d ∈
        rectangleDualConfiguration (-(n:ℤ),0) (2*n) n B := by
      rw [← hdualB]
      simpa [d] using he
    have hnotB := (mem_rectangleDualConfiguration (-(n:ℤ),0) (2*n) n B d).mp hmem
    have hnotA : d.primalEdge ∉ A := fun hA' => hnotB (hAB hA')
    rw [hdualA]
    simpa [d] using
      (mem_rectangleDualConfiguration (-(n:ℤ),0) (2*n) n A d).mpr hnotA
  · exact hB

/-- Under any actual frozen outside state, the three-sided dual law is
dominated by the conditional cover law of the dualized strip restriction. -/
theorem measure_parafermionicCoverStrip_dual_threeSides_le_conditional
    (n : ℕ) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (q : ClusterWeight)
    (K : RemovedConfiguration (ParafermionicAmbientGraph n)
      (subgraphRemovedEdges
        ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
        (ParafermionicAmbientGraph n)))
    (D : Set (Configuration (rectangleDualBottomCollarInnerGraph n)))
    (hD : IsUpperSet D) :
    (measure (rectangleDualBottomCollarInnerGraph n) q
      (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n)) D).toReal ≤
    ((((law (ParafermionicAmbientGraph n) q
      (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))).filter
      (frozenStateEvent
        (subgraphRemovedEdges
          ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
          (ParafermionicAmbientGraph n)) K)
      (frozenStateEvent_support q
        (BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n)))
        (subgraphRemovedEdges
          ((ParafermionicStripGraph n).map (parafermionicCoverStripEmbedding n k hk))
          (ParafermionicAmbientGraph n)) K)).map
      (parafermionicCoverStripDualRestriction n k hk)).toMeasure D).toReal := by
  let G := ParafermionicStripGraph n
  let H := ParafermionicAmbientGraph n
  let f := parafermionicCoverStripEmbedding n k hk
  let emb := embeddedConfigurationRestriction G H f (parafermionicCoverStrip_map_le n k hk)
  let φ := rectanglePrimalDualConfigurationEquiv (-(n:ℤ),0) (2*n) n
  let Ψ := parafermionicCoverStripDualRestriction n k hk
  let ξ := BoundaryCondition.free (∅ : Set (ParafermionicAmbientVertex n))
  let R := subgraphRemovedEdges (G.map f) H
  let P := (law H q ξ).filter (frozenStateEvent R K)
      (frozenStateEvent_support q ξ R K)
  let μ := P.map emb
  let F : Set (Configuration G) := (φ ⁻¹' D)
  let E : Set (Configuration G) := Fᶜ
  have hE : IsUpperSet E := by
    simpa [E, F, φ] using rectanglePrimalDualPreimage_compl_isUpper n D hD
  have hstrip := filtered_parafermionicCoverStrip_frozenFree_probability_le_bottomWired
    n k hk q K E hE
  have hcondComp : (μ.toMeasure E).toReal + (μ.toMeasure Eᶜ).toReal = 1 := by
    exact MeasureTheory.probReal_add_probReal_compl
      (μ := μ.toMeasure) (s := E) MeasurableSpace.measurableSet_top
  have hbottomComp :
      (measure G q (BoundaryCondition.wired (parafermionicCoverStripBottom n)) E).toReal +
        (measure G q (BoundaryCondition.wired (parafermionicCoverStripBottom n)) Eᶜ).toReal = 1 := by
    exact MeasureTheory.probReal_add_probReal_compl
      (μ := measure G q (BoundaryCondition.wired (parafermionicCoverStripBottom n)))
      (s := E) MeasurableSpace.measurableSet_top
  have hcomplementE :
      (measure G q (BoundaryCondition.wired (parafermionicCoverStripBottom n)) Eᶜ).toReal ≤
        (μ.toMeasure Eᶜ).toReal := by
    have hstrip' : (μ.toMeasure E).toReal ≤
        (measure G q (BoundaryCondition.wired (parafermionicCoverStripBottom n)) E).toReal := by
      simpa [μ, G, H, f, emb, R, ξ] using hstrip
    linarith [hcondComp, hbottomComp, hstrip']
  have hcomplement : (measure G q (BoundaryCondition.wired
      (parafermionicCoverStripBottom n)) F).toReal ≤ (μ.toMeasure F).toReal := by
    simpa [E, F] using hcomplementE
  have hdualPMF := rectangleBottomWiredDuality_law_map n q
  have hdualMeasure : measure G q (BoundaryCondition.wired
      (parafermionicCoverStripBottom n)) F =
      measure (rectangleDualBottomCollarInnerGraph n) q
        (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n)) D := by
    have hm := congrArg PMF.toMeasure hdualPMF
    rw [← PMF.toMeasure_map _ _ measurable_from_top] at hm
    calc
      (measure G q (BoundaryCondition.wired (parafermionicCoverStripBottom n))) F =
          Measure.map φ (law G q (BoundaryCondition.wired
            (parafermionicCoverStripBottom n))).toMeasure D := by
              change (law G q (BoundaryCondition.wired (parafermionicCoverStripBottom n))).toMeasure
                (φ ⁻¹' D) = _
              rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
      _ = (measure (rectangleDualBottomCollarInnerGraph n) q
          (BoundaryCondition.wired (rectangleDualBottomCollarInnerThreeSides n))) D := by
            exact congrArg (fun ν : Measure (Configuration
              (rectangleDualBottomCollarInnerGraph n)) => ν D) hm
  have hpush : μ.toMeasure F = (P.map Ψ).toMeasure D := by
    have hpmf : μ.map φ = P.map Ψ := by
      dsimp [μ, Ψ, parafermionicCoverStripDualRestriction]
      rw [PMF.map_comp]
    have hmeasureMap := congrArg PMF.toMeasure hpmf
    rw [← PMF.toMeasure_map _ _ measurable_from_top] at hmeasureMap
    calc
      μ.toMeasure F = Measure.map φ μ.toMeasure D := by
        rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
      _ = (P.map Ψ).toMeasure D := congrArg (fun ν : Measure _ => ν D) hmeasureMap
  have hfinal := hcomplement
  rw [hdualMeasure] at hfinal
  rw [hpush] at hfinal
  exact hfinal

end
end PottsContinuity.FKC.FiniteFK
