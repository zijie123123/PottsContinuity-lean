module

public import PottsContinuity.Thm3.Push.SourcePocketIdentityRootBound
public import PottsContinuity.Thm3.Push.ConfinedPrefixSourceGeometry
public import PottsContinuity.Thm3.Push.CompleteSourcePrefixDMP

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance completePrefixIntervalEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Actual open retained paths at a direct-prefix record. This contains
only physical sampled paths and their exact source geometry. -/
structure CaseTwoDirectPrefixSourcePaths (n s : ℕ) (hfit : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (trace : List (RectangleVertex (0,0) (2*n) (2*n))) where
  paths : SourceWalkPair (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C)
  geometry : RetainedRectanglePathGeometry (2*n) (2*n) (4*(s:ℤ))
    (sourceWalkPairUnderlying _ C paths)
  first_in : paths.firstStart ∈ intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ))
  second_in : paths.secondStart ∈ intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ))
  first_support : paths.first.support = trace
  second_support : paths.second.support = caseTwoTipOriginalTrace n s hfit b.1
  second_end : paths.secondEnd = b.2

/-- On a direct-prefix branch, the complete source-record conditional law
connects the original two intervals with the finite slit lower bound.
Only the deterministic prefix locality and actual sampled path record are
interfaces; all conditional-law, carrier and comparison steps are proved. -/
theorem caseTwoCompleteSource_prefix_interval_lower_bound_of_prefixLocality_and_sourcePaths
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n) (q : Set.Ici (1:ℝ))
    (ξ : BoundaryCondition (RectangleVertex (0,0) (2*n) (2*n)))
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (hprefix : ∀ C D b trace,
      caseTwoTipEndpointSelector n s hfit C = some b → 0 < b.2.val.2 →
      selectPrefix b C = some trace →
      D ∩ caseTwoStoppedPrefixReveal n s hfit b trace =
        C ∩ caseTwoStoppedPrefixReveal n s hfit b trace → selectPrefix b D = some trace)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (b : CaseTwoTipEndpointRecord n s)
    (trace : List (RectangleVertex (0,0) (2*n) (2*n)))
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hr : caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some (.inl trace))
    (D : CaseTwoDirectPrefixSourcePaths n s hfit C b trace) :
    let reveal := caseTwoCompleteSourceRevealMap n s hfit selectPrefix
    let hstable := caseTwoCompleteSourceRevealMap_stable_of_prefixLocality n s hs hfit selectPrefix hprefix
    1/(1+(q:ℝ)^2) ≤
      (((law (rectangleGraph (0,0) (2*n) (2*n)) (criticalParameters q) ξ).filter
        (revealRecordEvent reveal C) (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C]
          exact frozenStateEvent_support _ _ _ (revealRecordConfiguration reveal C))).toMeasure
        (caseTwoSourceIntervalConnection n s)).toReal := by
  dsimp only
  let P := sourceWalkPairUnderlying _ C D.paths
  have hcarrier : caseTwoCompleteSourceRevealMap n s hfit selectPrefix C =
      pocketAugmentedSourceReveal (2*n) (2*n) (4*(s:ℤ)) P.secondEnd.val.2
        (Subtype.val '' {z | z ∈ P.first.support}) (Subtype.val '' {z | z ∈ P.second.support}) := by
    rw [caseTwoCompleteSourceRevealMap_eq_of_prefix n s hfit selectPrefix C b trace hb hr]
    simp only [P,sourceWalkPairUnderlying,SimpleGraph.Walk.support_mapLe_eq_support,
      D.first_support,D.second_support,D.second_end,caseTwoStoppedPrefixReveal]
  have hp : ∀ z, z ∈ D.paths.first.support ↔ z ∈ P.first.support := by
    intro z
    simp only [P,sourceWalkPairUnderlying,SimpleGraph.Walk.support_mapLe_eq_support]
  have hq : ∀ z, z ∈ D.paths.second.support ↔ z ∈ P.second.support := by
    intro z
    simp only [P,sourceWalkPairUnderlying,SimpleGraph.Walk.support_mapLe_eq_support]
  have hbase := sourcePocket_source_roots_lower_bound_of_recordLocality (2*n) (2*n) (4*(s:ℤ)) P
    D.geometry q ξ (caseTwoCompleteSourceRevealMap n s hfit selectPrefix)
    (caseTwoCompleteSourceRevealMap_stable_of_prefixLocality n s hs hfit selectPrefix hprefix)
    C hcarrier D.paths hp hq
  apply hbase.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  exact ⟨P.firstStart,D.first_in,P.secondStart,D.second_in,hω⟩

end
end PottsContinuity.Push
