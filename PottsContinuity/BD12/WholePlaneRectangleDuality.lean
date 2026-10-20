module

public import PottsContinuity.BD12.InfiniteRectangleEvents
public import PottsContinuity.BD12.WholePlaneDuality

/-! Exact rectangle complement identity for arbitrary whole-plane states. -/

@[expose] public section

namespace PottsContinuity.BD12

open MeasureTheory PD.FK PD.FK.Medial PD.Duality PD.RCInfinite

noncomputable section

/-- Finite complementary duality agrees with restriction of the actual
whole-plane dual state, edge by edge. -/
theorem embeddedRestriction_dual (a : LatticeVertex) (w h : ℕ)
    (ω : LatticeConfiguration) :
    embeddedRestriction (rectangleDualGraph a w h)
      (rectangleDualEdgeToSquareEdge a w h) (wholePlaneDualConfigurationHomeomorph ω) =
    rectanglePrimalDualConfigurationEquiv a w h
      (embeddedRestriction (rectangleGraph a w h)
        (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h)) ω) := by
  classical
  ext g
  obtain ⟨e, rfl⟩ := (rectangleDualGraphEdgeEquiv a w h).surjective g
  rw [mem_embeddedRestriction, rectangleDualEdgeToSquareEdge_carrier]
  change latticeConfigurationBondState (wholePlaneDualConfigurationHomeomorph ω)
    e.crossingBond = true ↔ _
  rw [wholePlaneDualConfigurationHomeomorph_bondState]
  change Bool.not (ω (latticeBondEdge (primalBondOfDual e.crossingBond))) = true ↔ _
  rw [rectangleDualEdge_crossing_originalEdge]
  have hm := mem_embeddedRestriction (rectangleGraph a w h)
    (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h)) ω
    (e.primalEdge : (rectangleGraph a w h).edgeSet)
  have hj : rectanglePrimalEdgeToSquareEdge a w h e.primalEdge =
      frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e.primalEdge := by
    apply Subtype.ext
    rfl
  have hbool : Bool.not (ω (rectanglePrimalEdgeToSquareEdge a w h e.primalEdge)) = true ↔
      ¬ (ω (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e.primalEdge) = true) := by
    rw [hj]
    cases ω (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h) e.primalEdge) <;> simp
  exact hbool.trans ((not_congr hm).symm.trans
    (mem_rectanglePrimalDualConfigurationEquiv a w h _ e).symm)

/-- Actual primal crossing fails exactly when the actual dual state has the
true-dual bottom-to-top port crossing. -/
theorem horizontalRectangle_compl (a : LatticeVertex) (w h : ℕ) :
    (horizontalRectangle a w h)ᶜ =
      wholePlaneDualConfigurationHomeomorph ⁻¹' dualPortRectangle a w h := by
  ext ω
  change (embeddedRestriction (rectangleGraph a w h)
      (frozenEdgeEmbedding (PD.FK.latticeRectangle a w h)) ω ∉
        rectangleHorizontalCrossingEvent a w h) ↔
    embeddedRestriction (rectangleDualGraph a w h)
      (rectangleDualEdgeToSquareEdge a w h) (wholePlaneDualConfigurationHomeomorph ω) ∈
        rectangleDualBottomTopCrossingEvent a w h
  rw [embeddedRestriction_dual]
  exact rectangle_crossing_duality a w h _

/-- At p_sd the wired noncrossing probability equals the free probability of
the true-dual port event, without a finite-volume boundary approximation. -/
theorem wired_horizontal_compl_eq_free_dualPort (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (criticalParameters q).toP
      (criticalParameters q).toQ 1 μ₁)
    (a : LatticeVertex) (w h : ℕ) :
    μ₁ ((horizontalRectangle a w h)ᶜ) = μ₀ (dualPortRectangle a w h) := by
  rw [horizontalRectangle_compl, ← wired_limit_map_dual_selfDual q μ₀ μ₁ hμ₀ hμ₁,
    Measure.map_apply wholePlaneDualConfigurationHomeomorph_measurable
      (dualPortRectangle_isCylinder a w h).measurableSet]

end
end PottsContinuity.BD12
