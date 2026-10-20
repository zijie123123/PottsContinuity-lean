module

public import PottsContinuity.Thm3.Push.CaseTwoCompleteSourceLinear
public import PottsContinuity.Thm3.Push.EmbeddedLinearEventBound

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit Exploration MeasureTheory
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance completeSourceEmbeddedEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

section
variable
    (n s : ℕ) (hs : 1 ≤ s) (hfit : 9*s ≤ 2*n) (q : Set.Ici (1:ℝ))
    (selectPrefix : CaseTwoTipEndpointRecord n s →
      Configuration (rectangleGraph (0,0) (2*n) (2*n)) →
      Option (List (RectangleVertex (0,0) (2*n) (2*n))))
    (hprefix : ∀ C D b trace,
      caseTwoTipEndpointSelector n s hfit C = some b → 0 < b.2.val.2 →
      selectPrefix b C = some trace →
      D ∩ caseTwoStoppedPrefixReveal n s hfit b trace =
        C ∩ caseTwoStoppedPrefixReveal n s hfit b trace → selectPrefix b D = some trace)
    (hsearch : ∀ C b,
      caseTwoConfinedPrefixConfiguration n s hfit b C ∈
        arcsConnectionEvent (caseTwoConfinedPrefixGraph n s hfit b)
          (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
          {z | z.val.1 = 4*(s:ℤ)-1 ∧ b.2.val.2 ≤ z.val.2} → (selectPrefix b C).isSome)
    (hpaths : ∀ C b trace,
      caseTwoTipEndpointSelector n s hfit C = some b →
      selectPrefix b C = some trace → Nonempty (CaseTwoDirectPrefixSourcePaths n s hfit C b trace))

include hs hfit selectPrefix hprefix hsearch hpaths

/-- Integrate the boundary-uniform source linear bound over actual outside
states, then apply host positive association to the two host arm marginals. -/
theorem embedded_caseTwoCompleteSource_product_of_prefixLocality_and_sourcePaths
    {W : Type*} [Finite W] (H : SimpleGraph W)
    (f : RectangleVertex (0,0) (2*n) (2*n) ↪ W)
    (hGH : (rectangleGraph (0,0) (2*n) (2*n)).map f ≤ H)
    (ξ : BoundaryCondition W)
 :
    ((measure H (criticalParameters q) ξ
      {C | embeddedConfigurationRestriction _ H f hGH C ∈ sourceCaseTwoFirstArm n s}).toReal *
      (measure H (criticalParameters q) ξ
        {C | embeddedConfigurationRestriction _ H f hGH C ∈ sourceCaseTwoSecondArm n s}).toReal)/(1+(q:ℝ)^2) ≤
      (measure H (criticalParameters q) ξ
        {C | embeddedConfigurationRestriction _ H f hGH C ∈ caseTwoSourceIntervalConnection n s}).toReal := by
  let E := sourceCaseTwoFirstArm n s
  let F := sourceCaseTwoSecondArm n s
  have hbase := embedded_linear_event_bound_of_all_boundaries
    (rectangleGraph (0,0) (2*n) (2*n)) H f hGH (criticalParameters q) ξ
    (E ∩ F) (caseTwoSourceIntervalConnection n s) (1/(1+(q:ℝ)^2)) (fun η =>
      caseTwoCompleteSource_linear_of_prefixLocality_and_sourcePaths
        n s hs hfit q η selectPrefix hprefix hsearch hpaths)
  have hupper : ∀ S : Set (Configuration (rectangleGraph (0,0) (2*n) (2*n))),
      IsUpperSet S → IsUpperSet
        {C | embeddedConfigurationRestriction (rectangleGraph (0,0) (2*n) (2*n)) H f hGH C ∈ S} := by
    intro S hS C C' hCC' hC
    exact hS (embeddedConfigurationRestriction_monotone _ H f hGH hCC') hC
  have hfkg := measure_positive_association (criticalParameters q) ξ _ _ (hupper E (sourceSquareSideArmEvent_isUpperSet _ _ _ _ _ _))
      (hupper F (sourceSquareSideArmEvent_isUpperSet _ _ _ _ _ _))
  calc
    _ = (1/(1+(q:ℝ)^2)) *
        ((measure H (criticalParameters q) ξ {C | embeddedConfigurationRestriction _ H f hGH C ∈ E}).toReal *
          (measure H (criticalParameters q) ξ {C | embeddedConfigurationRestriction _ H f hGH C ∈ F}).toReal) := by ring
    _ ≤ (1/(1+(q:ℝ)^2)) *
        (measure H (criticalParameters q) ξ
          {C | embeddedConfigurationRestriction _ H f hGH C ∈ E ∩ F}).toReal :=
      mul_le_mul_of_nonneg_left hfkg (by positivity)
    _ ≤ _ := hbase


end
end
end PottsContinuity.Push
