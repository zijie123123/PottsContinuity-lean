module

public import PottsContinuity.BD12.InfiniteFinitePatternPositive
public import PottsContinuity.FKC.FiniteFK.SlitBoxExteriorReturnPath

/-! Positive probability of a literal KST bridge, witnessed by the horizontal
path along the top boundary and the finite-energy property. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK MeasureTheory
noncomputable section

/-- Every actual finite bridge scale has positive probability at interior
FK parameters, for either frozen boundary limit. -/
theorem infinite_kstBridge_probability_pos (θ : Parameters) (i : Fin 2)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ i μ)
    (m : ℕ) : 0 < μ.real (kstBridge m) := by
  let : IsProbabilityMeasure μ := hμ.1
  let e : FKC.squareLattice ≃g PD.squareLattice := {
    toEquiv := Equiv.refl _
    map_rel_iff' := by
      intro x y
      rw [PD.FK.squareLattice_adj_iff,FKC.squareLattice_adj_iff]
      rfl }
  let p0 := FKC.FiniteFK.slitReturnHorizontalRightWalk (-(m : ℤ)) (m : ℤ) (2*m)
  let p := p0.map e.toHom
  have hp : p.IsPath := (FKC.FiniteFK.slitReturnHorizontalRightWalk_isPath _ _ _).map e.injective
  have hsupport : p.support = p0.support := by
    rw [SimpleGraph.Walk.support_map]
    change p0.support.map id = p0.support
    exact List.map_id _
  have hpos := infinite_kstPathOpen_probability_pos θ i μ hμ p
  have he : -(m : ℤ) + ((2*m : ℕ) : ℤ) = (m : ℤ) := by omega
  have hleft : kstBridgeLeft m (-(m : ℤ),(m : ℤ)) := by
    simp [kstBridgeLeft]
    omega
  have hright : kstBridgeRight m (-(m : ℤ) + ((2*m : ℕ) : ℤ),(m : ℤ)) := by
    rw [he]
    simp [kstBridgeRight]
    omega
  have hsub : {ω | kstPathOpen ω p} ⊆ kstBridge m := by
    intro ω hω
    refine ⟨_,_,p,hp,hω,hleft,hright,?_⟩
    intro z hz
    rw [hsupport] at hz
    have hb := FKC.FiniteFK.slitReturnHorizontalRightWalk_support_bounds (-(m : ℤ)) (m : ℤ) (2*m) hz
    have hab : |z.1| ≤ (m : ℤ) := abs_le.mpr ⟨by omega,by omega⟩
    refine ⟨by omega,?_⟩
    rw [hb.1,abs_of_nonneg (Int.natCast_nonneg m)]
  exact hpos.trans_le (measureReal_mono hsub)

end
end PottsContinuity.BD12
