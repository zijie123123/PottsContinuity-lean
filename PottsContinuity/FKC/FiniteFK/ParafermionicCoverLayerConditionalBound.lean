-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/ParafermionicCoverLayerConditionalBound.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteStatisticFrozenLaw
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverBranchRootPolynomialBound
public import PottsContinuity.FKC.FiniteFK.ParafermionicCoverLayerBlocks
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial MeasureTheory
noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance coverLayerConditionalAmbientEdgeFintype (n : ℕ) :
    Fintype (ParafermionicAmbientGraph n).edgeSet := Fintype.ofFinite _
local instance coverLayerConditionalAmbientEdgeDecidableEq (n : ℕ) :
    DecidableEq (ParafermionicAmbientGraph n).edgeSet := Classical.decEq _
local instance coverLayerConditionalConfigurationFintype (n : ℕ) :
    Fintype (Configuration (ParafermionicAmbientGraph n)) := Fintype.ofFinite _
local instance coverLayerConditionalConfigurationNonempty (n : ℕ) :
    Nonempty (Configuration (ParafermionicAmbientGraph n)) := ⟨∅⟩
local instance coverLayerConditionalDualConfigurationFintype (n : ℕ) :
    Fintype (Configuration (rectangleDualBottomCollarInnerGraph n)) := Fintype.ofFinite _

/-- The branch-root event retains its polynomial lower bound on every actual
normalized conditional law obtained by recording all states outside one cover
layer. -/
theorem parafermionicCoverLayerBranchRootEvent_conditional_ge_polynomial
    (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hk : -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ))
    (q : ClusterWeight)
    (y : Set.range (fun A : Configuration (ParafermionicAmbientGraph n) =>
      A \ parafermionicCoverLayerBlock n k hk)) :
    (1 / (60 * (n : ℝ)^4) : ℝ) ≤
      ((finiteStatisticConditionalPMF
        (law (ParafermionicAmbientGraph n) q
          (BoundaryCondition.free ∅ : BoundaryCondition (ParafermionicAmbientVertex n)))
        (fun A => (law_pos (ParafermionicAmbientGraph n) q
          (BoundaryCondition.free ∅) A).ne')
        (fun A : Configuration (ParafermionicAmbientGraph n) =>
          A \ parafermionicCoverLayerBlock n k hk) y).toMeasure
        (parafermionicCoverLayerBranchRootEvent n k hk hn)).toReal := by
  classical
  let H := ParafermionicAmbientGraph n
  let G := ParafermionicStripGraph n
  let f := parafermionicCoverStripEmbedding n k hk
  let block := parafermionicCoverLayerBlock n k hk
  let R := subgraphRemovedEdges (G.map f) H
  let ξ : BoundaryCondition (ParafermionicAmbientVertex n) := BoundaryCondition.free ∅
  let Ψ := parafermionicCoverStripDualRestriction n k hk
  let D := parafermionicCoverBranchRootEvent n hn
  have hcomp : configurationOutsideBlock block = R := by
    change Finset.univ \ block = R
    exact univ_sdiff_parafermionicCoverLayerBlock n k hk
  let K0 := configurationOutsideBlockState block y
  have hKproperty : y.1 ⊆ R := by
    rw [← hcomp]
    exact K0.property
  let K : RemovedConfiguration H R := ⟨y.1, hKproperty⟩
  have hKval : K.val = K0.val := rfl
  have hEvent : frozenStateEvent R K =
      frozenStateEvent (configurationOutsideBlock block) K0 := by
    ext A
    simp only [frozenStateEvent]
    rw [hKval, ← hcomp]
  have hconditional := finiteStatisticConditionalPMF_configurationOutsideBlock
    (G := H) q ξ block y
  have hpmf :
      finiteStatisticConditionalPMF (law H q ξ) (fun A => (law_pos H q ξ A).ne')
        (fun A : Configuration H => A \ block) y =
      (law H q ξ).filter (frozenStateEvent R K)
        (frozenStateEvent_support q ξ R K) := by
    rw [hconditional]
    have hfilter :
        (law H q ξ).filter (frozenStateEvent R K)
          (frozenStateEvent_support q ξ R K) =
        (law H q ξ).filter (frozenStateEvent (configurationOutsideBlock block) K0)
          (frozenStateEvent_support q ξ (configurationOutsideBlock block) K0) := by
      apply PMF.ext
      intro A
      simp only [PMF.filter_apply]
      rw [hEvent]
    exact hfilter.symm
  have hpoly := measure_parafermionicCoverBranchRootEvent_conditional_ge_polynomial
    n hn k hk q K
  have hmap :
      (((law H q ξ).filter (frozenStateEvent R K)
        (frozenStateEvent_support q ξ R K)).map Ψ).toMeasure D =
      (((law H q ξ).filter (frozenStateEvent R K)
        (frozenStateEvent_support q ξ R K)).toMeasure (Ψ ⁻¹' D)) := by
    rw [← PMF.toMeasure_map _ _ measurable_from_top]
    rw [Measure.map_apply measurable_from_top MeasurableSpace.measurableSet_top]
  rw [hpmf]
  change (1 / (60 * (n : ℝ)^4) : ℝ) ≤
    (((law H q ξ).filter (frozenStateEvent R K)
      (frozenStateEvent_support q ξ R K)).toMeasure
      (parafermionicCoverLayerBranchRootEvent n k hk hn)).toReal
  have hpre : Ψ ⁻¹' D = parafermionicCoverLayerBranchRootEvent n k hk hn := by
    rfl
  rw [← hpre, ← hmap]
  simpa [H, G, f, R, ξ, Ψ, D] using hpoly

end
end PottsContinuity.FKC.FiniteFK
