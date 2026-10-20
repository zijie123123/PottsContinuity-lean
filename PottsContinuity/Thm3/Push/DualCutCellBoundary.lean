module

public import PottsContinuity.Thm3.Push.BondFaceIndex
public import PottsContinuity.PD.Duality.RectangleLabelCutIncidence
public import PottsContinuity.PD.Duality.LatticeCellBoundary
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Medial
noncomputable section

/-- The finite cells whose actual rectangle labels are true. -/
def rectangleLabelFaceCells (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) : Finset LatticeVertex := by
  classical
  letI : Fintype (RectangleVertex a w h) := Fintype.ofFinite _
  exact (Finset.univ.filter fun v => σ v = true).map (Function.Embedding.subtype _)

@[simp] theorem mem_rectangleLabelFaceCells (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (v : RectangleVertex a w h) :
    v.val ∈ rectangleLabelFaceCells a w h σ ↔ σ v = true := by
  classical
  constructor
  · rintro hv
    obtain ⟨u,hu,huv⟩ := Finset.mem_map.mp hv
    have heq : u = v := Subtype.ext huv
    simpa only [heq,Finset.mem_filter,Finset.mem_univ,true_and] using hu
  · intro hv
    exact Finset.mem_map.mpr ⟨v,by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hv,rfl⟩

/-- Taking the inverse dual bond recovers the two original face endpoints. -/
theorem primalBondOfDual_face_endpoints (b : LatticeBond) :
    (primalBondOfDual b).faceBase false = b.source ∧
      (primalBondOfDual b).faceBase true = b.target := by
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [primalBondOfDual,LatticeBond.faceBase,LatticeBond.source,LatticeBond.target]

/-- A second dualization returns to original lattice coordinates with the
literal (1,1) translation, for both bond orientations. -/
theorem primalBondOfDual_endpoints_faceIndexMark (b : LatticeBond) :
    (primalBondOfDual b).source = faceIndexMark (b.faceBase false) ∧
      (primalBondOfDual b).target = faceIndexMark (b.faceBase true) := by
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> simp [primalBondOfDual,faceIndexMark,LatticeBond.faceBase,
    LatticeBond.source,LatticeBond.target]

/-- Every dual label-cut step is an actual cell-boundary step after the
coordinate shift. Original edge labels and both face indicators are retained. -/
theorem labelCutDual_adj_cellBoundary_shift (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) (u v : RectangleDualVertex a w h)
    (huv : (rectangleLabelCutDualGraph a w h σ).Adj u v) :
    (latticeCellBoundaryGraph (rectangleLabelFaceCells a w h σ)).Adj
      (faceIndexMark u.val) (faceIndexMark v.val) := by
  obtain ⟨b,hs,ht,hdiff,hends⟩ := (rectangleLabelCutDual_adj_iff_bond a w h σ u v).mp huv
  let c := primalBondOfDual b
  have hfaces : ((c.faceBase true ∈ rectangleLabelFaceCells a w h σ) ≠
      (c.faceBase false ∈ rectangleLabelFaceCells a w h σ)) := by
    have hc := primalBondOfDual_face_endpoints b
    change ((primalBondOfDual b).faceBase true ∈ _) ≠ ((primalBondOfDual b).faceBase false ∈ _)
    rw [hc.1,hc.2]
    have hsLabel := mem_rectangleLabelFaceCells a w h σ ⟨b.source,hs⟩
    have htLabel := mem_rectangleLabelFaceCells a w h σ ⟨b.target,ht⟩
    intro heq
    cases hs0 : σ ⟨b.source,hs⟩ <;> cases ht0 : σ ⟨b.target,ht⟩ <;> simp_all
  have hcadj : squareLattice.Adj c.source c.target := by
    rcases b with ⟨⟨x,y⟩,ax⟩
    cases ax <;> simp [c,primalBondOfDual,LatticeBond.source,LatticeBond.target,squareLattice_adj_iff]
  have hcoords :
      (c.source = faceIndexMark u.val ∧ c.target = faceIndexMark v.val) ∨
      (c.source = faceIndexMark v.val ∧ c.target = faceIndexMark u.val) := by
    have hc := primalBondOfDual_endpoints_faceIndexMark b
    rcases hends with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact Or.inl ⟨hc.1.trans (congrArg faceIndexMark hu.symm),
        hc.2.trans (congrArg faceIndexMark hv.symm)⟩
    · exact Or.inr ⟨hc.1.trans (congrArg faceIndexMark hv.symm),
        hc.2.trans (congrArg faceIndexMark hu.symm)⟩
  apply (latticeCellBoundaryGraph_adj_iff _ _ _).mpr
  rcases hcoords with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · exact ⟨by simpa only [hu,hv] using hcadj,c,
      by simp only [LatticeBond.toSym2,hu,hv],hfaces⟩
  · exact ⟨by simpa only [hu,hv] using hcadj.symm,c,
      by simpa only [LatticeBond.toSym2,hu,hv] using
        (Sym2.eq_swap : s(faceIndexMark v.val,faceIndexMark u.val) = _),hfaces⟩

/-- A coordinate-faithful homomorphism returning the whole dual cut walk to
the actual boundary of its labelled cells. -/
def labelCutDualCellBoundaryHom (a : LatticeVertex) (w h : ℕ)
    (σ : RectangleVertex a w h → Bool) :
    rectangleLabelCutDualGraph a w h σ →g
      latticeCellBoundaryGraph (rectangleLabelFaceCells a w h σ) where
  toFun v := faceIndexMark v.val
  map_rel' := labelCutDual_adj_cellBoundary_shift a w h σ _ _

end
end PottsContinuity.Push
