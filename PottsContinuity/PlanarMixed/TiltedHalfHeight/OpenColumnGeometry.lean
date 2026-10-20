module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.ColumnEvents
public import PottsContinuity.PlanarTopology.ExteriorBottomExtension

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial
noncomputable section

/-- Every genuine lattice step within a fully open vertical column is open. -/
theorem fullyOpenColumn_adj (N : ℕ) (t : ℝ) (x : ℤ)
    (ω : TiltedConfiguration N t) (hfull : FullyOpenColumn N t x ω)
    (u v : tiltedStripVertices N t) (hu : u.val.1=x) (hv : v.val.1=x)
    (hadj : (tiltedStripGraph N t).Adj u v) : (tiltedOpenGraph N t ω).Adj u v := by
  obtain ⟨b,hbp,_⟩ := LatticeBond.existsUnique_of_adj (show PD.FK.squareLattice.Adj u.val v.val from hadj)
  have hends : (b.source=u.val ∧ b.target=v.val) ∨ (b.source=v.val ∧ b.target=u.val) :=
    Sym2.eq_iff.mp hbp
  have hs : b.source∈tiltedStripVertices N t := by
    rcases hends with h | h
    · exact h.1 ▸ u.property
    · exact h.1 ▸ v.property
  have ht : b.target∈tiltedStripVertices N t := by
    rcases hends with h | h
    · exact h.2 ▸ v.property
    · exact h.2 ▸ u.property
  have hbx : b.base.1=x := by
    rcases hends with h | h
    · exact (congrArg Prod.fst h.1).trans hu
    · exact (congrArg Prod.fst h.1).trans hv
  have htx : b.target.1=x := by
    rcases hends with h | h
    · exact (congrArg Prod.fst h.2).trans hv
    · exact (congrArg Prod.fst h.2).trans hu
  have haxis : b.axis=.vertical := by
    cases ha : b.axis with
    | vertical => rfl
    | horizontal =>
      simp only [LatticeBond.target,ha] at htx
      omega
  let B : TiltedBond N t := ⟨b,hs,ht⟩
  have hstate := hfull B haxis hbx
  have heq : tiltedBondEdge N t B =
      (⟨s(u,v),(tiltedStripGraph N t).mem_edgeSet.mpr hadj⟩ : (tiltedStripGraph N t).edgeSet) := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    simpa [tiltedBondEdge,LatticeBond.toSym2,B] using hbp
  apply (tiltedOpenGraph_adj_iff N t ω u v).mpr
  exact ⟨hadj,heq ▸ hstate⟩

/-- Any vertex of a fully open column reaches an intrinsic top vertex by a
finite original open path, without using a boundary-identification edge. -/
theorem fullyOpenColumn_connectedToTop (N : ℕ) (hN : 1≤N) (t : ℝ) (x : ℤ)
    (ω : TiltedConfiguration N t) (hfull : FullyOpenColumn N t x ω)
    (z : tiltedStripVertices N t) (hzx : z.val.1=x) :
    tiltedConnectedToTop N t ω z.val := by
  let k : ℤ := ⌊t*(x:ℝ)+(N:ℝ)⌋
  have hk := top_column_mem N hN t x
  have hzy : z.val.2≤k := by
    apply Int.le_floor.mpr
    have h := z.property.2
    dsimp [tiltedHeight] at h
    have hxR : (z.val.1:ℝ)=(x:ℝ) := congrArg Int.cast hzx
    rw [hxR] at h
    linarith
  let S : Set (ℤ×ℤ) := {w | w.1=x ∧ z.val.2≤w.2 ∧ w.2≤k}
  have hstrip : ∀ w∈S, w∈tiltedStripVertices N t := by
    intro w hw
    have hlo : t*(x:ℝ)≤(z.val.2:ℝ) := by
      have h := z.property.1
      dsimp [tiltedHeight] at h
      have hxR : (z.val.1:ℝ)=(x:ℝ) := congrArg Int.cast hzx
      rw [hxR] at h
      linarith
    have hhi := Int.floor_le (t*(x:ℝ)+(N:ℝ))
    have h1 : (z.val.2:ℝ)≤(w.2:ℝ) := by exact_mod_cast hw.2.1
    have h2 : (w.2:ℝ)≤(k:ℝ) := by exact_mod_cast hw.2.2
    constructor <;> dsimp [tiltedHeight] <;> rw [hw.1] <;> linarith
  let hom : (PD.FK.squareLattice.induce S) →g tiltedOpenGraph N t ω :=
    { toFun := fun (w : S) => ⟨w.val,hstrip w.val w.property⟩
      map_rel' := by
        intro u v huv
        exact fullyOpenColumn_adj N t x ω hfull _ _ u.property.1 v.property.1 huv }
  obtain ⟨p,hp⟩ := PlanarTopology.vertical_walk_between x z.val.2 k
  have hsupport : ∀ w∈p.support, w∈S := by
    intro w hw
    have h := hp w hw
    simpa [S,min_eq_left hzy,max_eq_right hzy] using h
  let v : tiltedStripVertices N t := ⟨(x,k),hk⟩
  let P := (p.induce S hsupport).map hom
  have hsource : hom ⟨(x,z.val.2),hsupport _ p.start_mem_support⟩=z := by
    apply Subtype.ext
    exact Prod.ext hzx.symm rfl
  have htarget : hom ⟨(x,k),hsupport _ p.end_mem_support⟩=v := rfl
  exact ⟨z.property,v,top_column_isTop N t x,(P.copy hsource htarget).reachable⟩

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
