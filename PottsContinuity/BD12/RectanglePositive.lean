module

public import PottsContinuity.BD12.InfiniteFinitePatternPositive
public import PottsContinuity.FKC.FiniteFK.SlitBoxExteriorReturnPath
public import PottsContinuity.PlanarTopology.KSTRectangleRealization

/-! Every finite actual rectangle crossing has positive probability at an
interior FK parameter, witnessed by the open bottom horizontal path. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- Positivity on every finite rectangle, including degenerate side lengths. -/
theorem infinite_horizontalRectangle_probability_pos (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (a : LatticeVertex) (w h : ℕ) : 0 < μ.real (horizontalRectangle a w h) := by
  let : IsProbabilityMeasure μ := hμ.1
  let e : FKC.squareLattice ≃g PD.squareLattice := {
    toEquiv := Equiv.refl _
    map_rel_iff' := by intro x y; rw [PD.FK.squareLattice_adj_iff,FKC.squareLattice_adj_iff]; rfl }
  let p0 := FKC.FiniteFK.slitReturnHorizontalRightWalk a.1 a.2 w
  let p := p0.map e.toHom
  have hsupport : p.support = p0.support := by
    rw [SimpleGraph.Walk.support_map]
    change p0.support.map id = p0.support
    exact List.map_id _
  have hpos := infinite_kstPathOpen_probability_pos θ i μ hμ p
  have hsub : {ω | kstPathOpen ω p} ⊆ horizontalRectangle a w h := by
    intro ω hω
    apply PlanarTopology.horizontalRectangle_of_kst_open_walk a w h ω p hω rfl rfl
    intro z hz
    rw [hsupport] at hz
    have hb := FKC.FiniteFK.slitReturnHorizontalRightWalk_support_bounds a.1 a.2 w hz
    exact ⟨hb.2.1,hb.2.2,by omega,by omega⟩
  exact hpos.trans_le (measureReal_mono hsub)

end
end PottsContinuity.BD12
