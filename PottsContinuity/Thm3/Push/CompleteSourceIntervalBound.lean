module

public import PottsContinuity.Thm3.Push.CompletePrefixIntervalBound

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance completeSourceIntervalEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The fully observed connection alternative has conditional probability
one, for every original boundary partition. -/
theorem caseTwoCompleteSource_connection_branch_probability_one_of_prefixLocality
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
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hr : caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some (.inr ())) :
    let reveal := caseTwoCompleteSourceRevealMap n s hfit selectPrefix
    let hstable := caseTwoCompleteSourceRevealMap_stable_of_prefixLocality n s hs hfit selectPrefix hprefix
    (((law (rectangleGraph (0,0) (2*n) (2*n)) (criticalParameters q) ξ).filter
        (revealRecordEvent reveal C) (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C]
          exact frozenStateEvent_support _ _ _ (revealRecordConfiguration reveal C))).toMeasure
        (caseTwoSourceIntervalConnection n s)).toReal = 1 := by
  dsimp only
  let reveal := caseTwoCompleteSourceRevealMap n s hfit selectPrefix
  let hstable := caseTwoCompleteSourceRevealMap_stable_of_prefixLocality n s hs hfit selectPrefix hprefix
  let μ := (law (rectangleGraph (0,0) (2*n) (2*n)) (criticalParameters q) ξ).filter
    (revealRecordEvent reveal C) (by
      rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C]
      exact frozenStateEvent_support _ _ _ (revealRecordConfiguration reveal C))
  have hprob : μ.toMeasure (caseTwoSourceIntervalConnection n s) = 1 := by
    apply (μ.toMeasure_apply_eq_one_iff MeasurableSpace.measurableSet_top).mpr
    intro ω hω
    have hrec := (PMF.mem_support_filter_iff _).mp hω |>.1
    rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C] at hrec
    change ω ∩ reveal C = C ∩ reveal C at hrec
    have hfull := (caseTwoCompleteSource_connection_branch_geometry n s hfit selectPrefix C b hb hr).1
    have heq : ω = C := by simpa only [reveal,hfull,Finset.inter_univ] using hrec
    exact heq ▸ caseTwoCompletePrefixSelector_inr_connects n s hfit selectPrefix b C hr
  exact (congrArg ENNReal.toReal hprob).trans ENNReal.toReal_one

/-- Both successful complete-record branches give the physical interval
connection lower bound. Only direct prefixes need sampled path geometry. -/
theorem caseTwoCompleteSource_interval_lower_bound_of_prefixLocality_and_sourcePaths
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
    (rec : Sum (List (RectangleVertex (0,0) (2*n) (2*n))) Unit)
    (hb : caseTwoTipEndpointSelector n s hfit C = some b)
    (hr : caseTwoCompletePrefixSelector n s hfit selectPrefix b C = some rec)
    (hpaths : ∀ trace, rec = .inl trace → Nonempty (CaseTwoDirectPrefixSourcePaths n s hfit C b trace)) :
    let reveal := caseTwoCompleteSourceRevealMap n s hfit selectPrefix
    let hstable := caseTwoCompleteSourceRevealMap_stable_of_prefixLocality n s hs hfit selectPrefix hprefix
    1/(1+(q:ℝ)^2) ≤
      (((law (rectangleGraph (0,0) (2*n) (2*n)) (criticalParameters q) ξ).filter
        (revealRecordEvent reveal C) (by
          rw [revealRecordEvent_eq_frozenStateEvent reveal hstable C]
          exact frozenStateEvent_support _ _ _ (revealRecordConfiguration reveal C))).toMeasure
        (caseTwoSourceIntervalConnection n s)).toReal := by
  cases rec with
  | inl trace =>
    obtain ⟨D⟩ := hpaths trace rfl
    exact caseTwoCompleteSource_prefix_interval_lower_bound_of_prefixLocality_and_sourcePaths
      n s hs hfit q ξ selectPrefix hprefix C b trace hb hr D
  | inr u =>
    cases u
    have hone := caseTwoCompleteSource_connection_branch_probability_one_of_prefixLocality
      n s hs hfit q ξ selectPrefix hprefix C b hb hr
    dsimp only at hone ⊢
    rw [hone]
    apply (div_le_one₀ (by positivity : 0 < 1+(q:ℝ)^2)).mpr
    have hsq := sq_nonneg (q:ℝ)
    linarith

end
end PottsContinuity.Push
