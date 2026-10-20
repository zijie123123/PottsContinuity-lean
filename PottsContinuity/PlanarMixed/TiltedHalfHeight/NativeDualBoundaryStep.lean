module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.ContractedCircuitGeometry
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.ReducedCarrierHalfHeight
public import PottsContinuity.Thm3.RSW.TiltedStripReducedDualCoordinates

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- In the nonpositive branch the genuine dual height reverses about N-1. -/
theorem reducedDualVertex_height_nonpositive (N : ℕ) (t : ℝ) (ht : t ≤ 0) (z : LatticeVertex) :
    tiltedHeight t (RSW.tiltedStripReducedDualVertex N t z) =
      (N : ℝ)-1-tiltedHeight t z := by
  simp only [RSW.tiltedStripReducedDualVertex,not_lt.mpr ht,ite_false,
    sub_zero,tiltedHeight,Int.cast_neg,Int.cast_sub,Int.cast_natCast,Int.cast_one]
  ring

theorem reducedDualVertex_adj (N : ℕ) (t : ℝ) {u v : LatticeVertex}
    (huv : squareLattice.Adj u v) :
    squareLattice.Adj (RSW.tiltedStripReducedDualVertex N t u)
      (RSW.tiltedStripReducedDualVertex N t v) := by
  change |u.1-v.1|+|u.2-v.2|=1 at huv
  change |(-u.1-(if 0<t then 1 else 0))-(-v.1-(if 0<t then 1 else 0))|+
    |((N:ℤ)-1-u.2)-((N:ℤ)-1-v.2)|=1
  rw [show (-u.1-(if 0<t then 1 else 0))-(-v.1-(if 0<t then 1 else 0))=v.1-u.1 by ring,
    show ((N:ℤ)-1-u.2)-((N:ℤ)-1-v.2)=v.2-u.2 by ring,
    abs_sub_comm v.1 u.1,abs_sub_comm v.2 u.2]
  exact huv

/-- A hull boundary step started below the transported wired top is a
literal original open edge of the native reduced dual sample. -/
theorem hullBoundary_step_to_native_dual (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 0) (ω : TiltedConfiguration N t)
    (C : Finset LatticeVertex) (hC : ∀ z ∈ C, tiltedHeight t z ≤ (N:ℝ)-1)
    (hsat : ∀ b : TiltedBond N t, ω (tiltedBondEdge N t b)=true →
      (b.val.source∈C ↔ b.val.target∈C))
    {u v : LatticeVertex} (huv : (latticeCellBoundaryGraph (vertexCellBases C)).Adj u v)
    (hu : RSW.tiltedStripReducedDualVertex N t u ∈ tiltedStripVertices N t)
    (hnot : ¬ tiltedTop N t (RSW.tiltedStripReducedDualVertex N t u)) :
    ∃ hv : RSW.tiltedStripReducedDualVertex N t v ∈ tiltedStripVertices N t,
      (tiltedOpenGraph N t (reducedCarrierLift N t
        (RSW.tiltedStripReducedDualTransport N t (by exact ⟨ht.1,by linarith [ht.2]⟩)
          (RSW.tiltedStripReducedRestriction N t ω)))).Adj
        ⟨RSW.tiltedStripReducedDualVertex N t u,hu⟩
        ⟨RSW.tiltedStripReducedDualVertex N t v,hv⟩ := by
  have htfull : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
  have hbounds := cellBoundary_height_le_of_hull_not_top N t ht.2 C hC huv
  have ha := reducedDualVertex_adj N t (latticeCellBoundaryGraph_le _ huv)
  have hv : RSW.tiltedStripReducedDualVertex N t v ∈ tiltedStripVertices N t := by
    constructor
    · rw [reducedDualVertex_height_nonpositive N t ht.2]
      linarith [hbounds.2]
    · have hs := tiltedHeight_step_le htfull ha
      rw [tiltedTop_iff_height N htfull,not_lt] at hnot
      linarith
  refine ⟨hv,?_⟩
  obtain ⟨_,d,hd,hfaces⟩ := (latticeCellBoundaryGraph_adj_iff _ u v).mp huv
  let b := primalBondOfDual d
  let B := RSW.tiltedStripReducedCrossedBond N t b
  have hpair : B.toSym2 = s(RSW.tiltedStripReducedDualVertex N t u,
      RSW.tiltedStripReducedDualVertex N t v) := by
    have h := RSW.tiltedStripReducedDualBond_dualBondOfPrimal_pair N t b
    rw [show dualBondOfPrimal b=d from dualBondOfPrimal_primalBondOfDual d,hd,Sym2.map_mk] at h
    exact h.symm
  have hends := Sym2.eq_iff.mp hpair
  have hB : B.source∈tiltedStripVertices N t ∧ B.target∈tiltedStripVertices N t ∧
      ¬ (tiltedTop N t B.source ∧ tiltedTop N t B.target) := by
    rcases hends with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact ⟨h1 ▸ hu,h2 ▸ hv,by rintro ⟨h,_⟩; exact hnot (h1 ▸ h)⟩
    · exact ⟨h1 ▸ hv,h2 ▸ hu,by rintro ⟨_,h⟩; exact hnot (h2 ▸ h)⟩
  let β : RSW.tiltedStripReducedCarrier N t := ⟨⟨B,hB.1,hB.2.1⟩,hB.2.2⟩
  let γ := RSW.tiltedStripReducedBondEquiv N t htfull β
  have hγ : γ.val.val = b := RSW.tiltedStripReducedCrossedBond_involutive N t b
  have hγβ : RSW.tiltedStripReducedBondEquiv N t htfull γ = β :=
    (RSW.tiltedStripReducedBondEquiv N t htfull).left_inv β
  have hclosed : ω (tiltedBondEdge N t γ.val)=false := by
    cases hs : ω (tiltedBondEdge N t γ.val)
    · rfl
    · have hrel := hsat γ.val hs
      have hc0 : ((d.faceBase false).1+1,(d.faceBase false).2+1)=γ.val.val.source := by
        rw [hγ]
        rcases d with ⟨⟨x,y⟩,axis⟩
        cases axis <;> simp [b,LatticeBond.faceBase,primalBondOfDual,LatticeBond.source]
      have hc1 : ((d.faceBase true).1+1,(d.faceBase true).2+1)=γ.val.val.target := by
        rw [hγ]
        rcases d with ⟨⟨x,y⟩,axis⟩
        cases axis <;> simp [b,LatticeBond.faceBase,primalBondOfDual,LatticeBond.target]
      apply False.elim
      apply hfaces
      rw [mem_vertexCellBases,mem_vertexCellBases,hc1,hc0]
      exact propext hrel.symm
  have hstate := reducedLift_dual_at_image N t htfull ω γ
  rw [hγβ,hclosed] at hstate
  let U : tiltedStripVertices N t := ⟨RSW.tiltedStripReducedDualVertex N t u,hu⟩
  let V : tiltedStripVertices N t := ⟨RSW.tiltedStripReducedDualVertex N t v,hv⟩
  have heq : tiltedBondEdge N t β.val = (⟨s(U,V),ha⟩ : (tiltedStripGraph N t).edgeSet) := by
    apply Subtype.ext
    apply Sym2.map.injective Subtype.val_injective
    exact hpair
  apply (tiltedOpenGraph_adj_iff N t _ U V).mpr
  exact ⟨ha,by rw [←heq]; exact hstate⟩

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
