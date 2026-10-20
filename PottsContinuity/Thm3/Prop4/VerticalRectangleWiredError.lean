module

public import PottsContinuity.Thm3.Prop4.RectangleWiredCrossing
public import PottsContinuity.PlanarTopology.RectangleTranspose
public import PottsContinuity.Infinite.Symmetry

/-!
# Vertical rectangle errors for the corridor construction

Coordinate interchange is applied to the genuine frozen wired law and to the
entire crossing event. The width and height, including their integral face
offset, are retained by the transposed horizontal estimate.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial PD.RCInfinite

/-- The frozen wired law is invariant under the original coordinate interchange. -/
theorem selfDual_wired_transpose_invariant (q : Set.Ici (1 : ℝ))
    (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ) :
    μ.map (latticeConfigurationIsoHomeomorph PlanarTopology.latticeTransposeIso) = μ := by
  apply Infinite.infinite_volume_latticeIso_invariant _ _
    (edgeParameter_pos (RSW.selfDualParameters q))
    (edgeParameter_lt_one (RSW.selfDualParameters q))
    (RSW.selfDualParameters q).property 1 μ hμ
  intro c v r
  change v.swap ∈ latticeBox c.swap r ↔ v ∈ latticeBox c r
  simp only [mem_latticeBox]
  exact and_comm

/-- Actual vertical noncrossing costs at most h dual arms of square radius w+1. -/
theorem selfDual_wired_vertical_rectangle_noncrossing_le_stretched (q : Set.Ici (1 : ℝ))
    (μ₀ μ₁ : Measure LatticeConfiguration)
    (hμ₀ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP
      (RSW.selfDualParameters q).toQ 1 μ₁)
    (c₀ α : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hdecay : ∀ n : ℕ, 1 ≤ n → RSW.oneArmProbability μ₀ n ≤ Real.exp (-c₀*(n : ℝ)^α))
    (a : ℤ × ℤ) (w h : ℕ) :
    μ₁.real (BD12.verticalRectangle a w h)ᶜ ≤
      (h : ℝ)*Real.exp (-c₀*((w : ℝ)+1)^α) := by
  have hmap := selfDual_wired_transpose_invariant q μ₁ hμ₁
  have he := congrArg (fun ν : Measure LatticeConfiguration =>
    ν.real (BD12.horizontalRectangle a.swap h w)ᶜ) hmap
  rw [Measure.real_def,Measure.map_apply (latticeConfigurationIsoHomeomorph_measurable _)
    (BD12.horizontalRectangle_isCylinder _ _ _).measurableSet.compl,
    Set.preimage_compl,PlanarTopology.horizontalRectangle_transpose_preimage] at he
  exact he.le.trans (selfDual_wired_rectangle_noncrossing_le_stretched q μ₀ μ₁ hμ₀ hμ₁
    c₀ α hc₀ hα hdecay a.swap h w)

end PottsContinuity.Thm3.Prop4
