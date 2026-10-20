-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/GeneralRectangleDualBottomLeaves.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.GeneralRectangleDualBottomCollarBoundary
public import PottsContinuity.FKC.FiniteFK.RectangleDualAmbient

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC PottsContinuity.FKC.Medial
noncomputable section

/-- The vertices at or above the bottom face-base row; the removed row is
kept out of this subtype because its noncorner vertices are free leaves. -/
abbrev generalRectangleDualBottomCoreVertex (a : LatticeVertex) (w h : ℕ) :=
  {v : RectangleDualVertex a w h // a.2 ≤ v.1.2}

def generalRectangleDualBottomCoreVertexEquiv (a : LatticeVertex) (w h : ℕ) :
    generalRectangleDualBottomCoreVertex a w h ≃
      RectangleVertex (a.1 - 1, a.2) (w + 1) h where
  toFun v := ⟨v.1.1, by
    have hv : v.1.1 ∈ latticeRectangle (a.1 - 1, a.2) (w + 1) h := by
      have hvexp := v.1.2
      change v.1.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) at hvexp
      rw [mem_latticeRectangle] at hvexp
      apply (mem_latticeRectangle _ _ _ _).2
      constructor
      · constructor <;> omega
      · constructor <;> omega
    exact hv⟩
  invFun v := by
    have hv := v.2
    rw [mem_latticeRectangle] at hv
    refine ⟨⟨v.1, ?_⟩, ?_⟩
    · change v.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1)
      apply (mem_latticeRectangle _ _ _ _).2
      constructor
      · constructor <;> omega
      · constructor <;> omega
    · exact hv.2.1
  left_inv v := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := by apply Subtype.ext; rfl

def generalRectangleDualBottomCoreGraph (a : LatticeVertex) (w h : ℕ) :
    SimpleGraph (generalRectangleDualBottomCoreVertex a w h) :=
  (rectangleDualGraph a w h).induce
    {v : RectangleDualVertex a w h | a.2 ≤ v.1.2}

/-- Every true dual edge in the core is an edge of the full ordinary lattice
rectangle with the exact expanded-face coordinates. -/
theorem generalRectangleDualBottomCoreGraph_le_rectangle
    (a : LatticeVertex) (w h : ℕ) :
    generalRectangleDualBottomCoreGraph a w h ≤
      SimpleGraph.comap (generalRectangleDualBottomCoreVertexEquiv a w h)
        (rectangleGraph (a.1 - 1, a.2) (w + 1) h) := by
  intro u v huv
  change (rectangleDualGraph a w h).Adj u.1 v.1 at huv
  have hamb := (rectangleDualGraph_le_ambient a w h) huv
  rw [rectangleDualAmbientGraph_adj_iff] at hamb
  change (rectangleGraph (a.1 - 1, a.2) (w + 1) h).Adj
    (generalRectangleDualBottomCoreVertexEquiv a w h u)
    (generalRectangleDualBottomCoreVertexEquiv a w h v)
  rw [rectangleGraph_adj_iff]
  simpa [generalRectangleDualBottomCoreVertexEquiv] using hamb

theorem generalRectangleDualBottomCore_mem_boundary_iff
    (a : LatticeVertex) (w h : ℕ)
    (v : generalRectangleDualBottomCoreVertex a w h) :
    v.1.1 ∈ rectangleDualBoundary a w h ↔
      v.1.1.1 = a.1 - 1 ∨ v.1.1.1 = a.1 + (w : ℤ) ∨
        v.1.1.2 = a.2 + (h : ℤ) := by
  have hv : v.1.1 ∈ latticeRectangle (a.1 - 1, a.2 - 1) (w + 1) (h + 1) := by
    simpa [rectangleDualExpanded] using v.1.2
  rw [mem_latticeRectangle] at hv
  simp only [rectangleDualBoundary, Finset.mem_filter, rectangleDualExpanded,
    mem_latticeRectangle, rectangleDualInterior, Finset.mem_filter,
    rectangleDualExpanded, mem_latticeRectangle]
  have hy : a.2 ≤ v.1.1.2 := v.2
  omega

theorem generalRectangleDualBottomCore_extraEdge_endpoints_wired
    (a : LatticeVertex) (w h : ℕ)
    (u v : generalRectangleDualBottomCoreVertex a w h)
    (hadj : (rectangleGraph (a.1 - 1, a.2) (w + 1) h).Adj
      (generalRectangleDualBottomCoreVertexEquiv a w h u)
      (generalRectangleDualBottomCoreVertexEquiv a w h v))
    (hnot : ¬ (generalRectangleDualBottomCoreGraph a w h).Adj u v) :
    (u.1.1.1 = a.1 - 1 ∨ u.1.1.1 = a.1 + (w : ℤ) ∨
      u.1.1.2 = a.2 + (h : ℤ)) ∧
    (v.1.1.1 = a.1 - 1 ∨ v.1.1.1 = a.1 + (w : ℤ) ∨
      v.1.1.2 = a.2 + (h : ℤ)) := by
  have hamb : (rectangleDualAmbientGraph a w h).Adj u.1 v.1 := by
    rw [rectangleDualAmbientGraph_adj_iff]
    rw [rectangleGraph_adj_iff] at hadj
    exact hadj
  have hnot' : ¬ (rectangleDualGraph a w h).Adj u.1 v.1 := by
    intro hx
    exact hnot hx
  have hactual := rectangleDualAmbient_extraEdge_endpoints_boundary a w h u.1 v.1 hamb hnot'
  exact ⟨(generalRectangleDualBottomCore_mem_boundary_iff a w h u).mp hactual.1,
    (generalRectangleDualBottomCore_mem_boundary_iff a w h v).mp hactual.2⟩

private theorem grdbl_primalBond_endpoints_mem (a : LatticeVertex) (w h : ℕ)
    (e : rectanglePrimalEdgeCarrier a w h) :
    (rectanglePrimalEdgeBond a w h e).source ∈ latticeRectangle a w h ∧
      (rectanglePrimalEdgeBond a w h e).target ∈ latticeRectangle a w h := by
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have hb : (rectanglePrimalEdgeBond a w h e).toSym2 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 := by
    have he := congrArg Subtype.val
      (wholePlaneBondEdgeEquiv.apply_symm_apply (rectanglePrimalEdgeToSquareEdge a w h e))
    change (rectanglePrimalEdgeBond a w h e).toSym2 = _ at he
    exact he
  have hm : Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 =
      s(p.1.val, p.2.val) := by rw [← hrepr]; rfl
  have heq : s((rectanglePrimalEdgeBond a w h e).source,
      (rectanglePrimalEdgeBond a w h e).target) = s(p.1.val, p.2.val) := by
    simpa [LatticeBond.toSym2] using hb.trans hm
  rcases Sym2.eq_iff.mp heq with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · exact ⟨by simp [hs], by simp [ht]⟩
  · rw [hs, ht]
    exact ⟨p.2.property, p.1.property⟩

private theorem grdbl_dual_adj_primal_bond
    (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleDualVertex a w h)
    (hadj : (rectangleDualGraph a w h).Adj u v) :
    ∃ b : LatticeBond,
      b.source ∈ latticeRectangle a w h ∧ b.target ∈ latticeRectangle a w h ∧
      s(u.1, v.1) = s(b.faceBase false, b.faceBase true) := by
  obtain ⟨e, hp⟩ := (rectangleDualGraph_adj_iff a w h u v).mp hadj
  let b := rectanglePrimalEdgeBond a w h e.primalEdge
  have hbmem := grdbl_primalBond_endpoints_mem a w h e.primalEdge
  refine ⟨b, hbmem.1, hbmem.2, ?_⟩
  have hpair : s(u.1, v.1) = s(e.crossingBond.source, e.crossingBond.target) := by
    simpa [rectangleDualCarrierPair, rectangleDualEdgeSource_val,
      rectangleDualEdgeTarget_val] using congrArg (Sym2.map Subtype.val) hp
  have hcross : e.crossingBond = dualBondOfPrimal b := by
    dsimp [b]
    exact e.crossingBond_eq
  rw [hcross, dualBondOfPrimal_source, dualBondOfPrimal_target] at hpair
  exact hpair

theorem generalRectangleDualBottomRow_adj_iff
    (a : LatticeVertex) (w h : ℕ)
    (x : ℤ) (u v : RectangleDualVertex a w h)
    (hu : u.1 = (x, a.2 - 1)) (hv : v.1 = (x, a.2)) :
    (rectangleDualGraph a w h).Adj u v ↔
      a.1 ≤ x ∧ x < a.1 + (w : ℤ) := by
  constructor
  · intro hadj
    obtain ⟨b, hbs, hbt, hpair⟩ :=
      grdbl_dual_adj_primal_bond a w h u v hadj
    all_goals rcases b with ⟨⟨bx, byy⟩, axis⟩
    all_goals cases axis
    all_goals rcases Sym2.eq_iff.mp hpair with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    all_goals simp [LatticeBond.faceBase] at hu' hv'
    all_goals simp [hu, hv, LatticeBond.source,
      LatticeBond.target, mem_latticeRectangle, Prod.mk.injEq] at hu' hv' hbs hbt
    all_goals omega
  · intro hx
    let p : RectangleVertex a w h := ⟨(x, a.2), by
      apply (mem_latticeRectangle _ _ _ _).2
      constructor <;> constructor <;> omega⟩
    let qv : RectangleVertex a w h := ⟨(x + 1, a.2), by
      apply (mem_latticeRectangle _ _ _ _).2
      constructor <;> constructor <;> omega⟩
    have hpq : (rectangleGraph a w h).Adj p qv := by
      rw [rectangleGraph_adj_iff]
      change squareLattice.Adj (x, a.2) (x + 1, a.2)
      simp [squareLattice]
    let pe : rectanglePrimalEdgeCarrier a w h :=
      ⟨s(p, qv), (rectangleGraph a w h).mem_edgeSet.mpr hpq⟩
    let de := (rectanglePrimalDualEdgeEquiv a w h) pe
    have hbond : (rectanglePrimalEdgeBond a w h pe) = ⟨(x, a.2), .horizontal⟩ := by
      apply LatticeBond.toSym2_injective
      have he := congrArg Subtype.val
        (wholePlaneBondEdgeEquiv.apply_symm_apply (rectanglePrimalEdgeToSquareEdge a w h pe))
      change (rectanglePrimalEdgeBond a w h pe).toSym2 = _ at he
      have hpe : Sym2.map (fun z : RectangleVertex a w h => z.val) pe.1 =
          s((x, a.2), (x + 1, a.2)) := rfl
      have hval : (rectanglePrimalEdgeToSquareEdge a w h pe).val =
          s((x, a.2), (x + 1, a.2)) := hpe
      rw [hval] at he
      simpa [LatticeBond.toSym2, LatticeBond.source, LatticeBond.target] using he
    let u0 : RectangleDualVertex a w h := ⟨(x, a.2 - 1), by
      rw [rectangleDualExpanded, mem_latticeRectangle]
      constructor <;> constructor <;> omega⟩
    let v0 : RectangleDualVertex a w h := ⟨(x, a.2), by
      rw [rectangleDualExpanded, mem_latticeRectangle]
      constructor <;> constructor <;> omega⟩
    have huEq : u = u0 := by apply Subtype.ext; exact hu
    have hvEq : v = v0 := by apply Subtype.ext; exact hv
    have hs : rectangleDualEdgeSource a w h de = u0 := by
      apply Subtype.ext
      rw [rectangleDualEdgeSource_faceBase]
      change (rectanglePrimalEdgeBond a w h pe).faceBase false = (u0.1)
      rw [hbond]
      rfl
    have ht : rectangleDualEdgeTarget a w h de = v0 := by
      apply Subtype.ext
      rw [rectangleDualEdgeTarget_faceBase]
      change (rectanglePrimalEdgeBond a w h pe).faceBase true = (v0.1)
      rw [hbond]
      rfl
    have hp : s(u, v) = rectangleDualCarrierPair a w h de := by
      rw [huEq, hvEq]
      rw [rectangleDualCarrierPair, hs, ht]
    exact (rectangleDualGraph_adj_iff a w h u v).2 ⟨de, hp⟩

theorem generalRectangleDualBottomRow_adj_neighbor
    (a : LatticeVertex) (w h : ℕ)
    (x : ℤ) (u v : RectangleDualVertex a w h)
    (hu : u.1 = (x, a.2 - 1))
    (hadj : (rectangleDualGraph a w h).Adj u v) :
    v.1 = (x, a.2) ∧ a.1 ≤ x ∧ x < a.1 + (w : ℤ) := by
  obtain ⟨b, hbs, hbt, hpair⟩ := grdbl_dual_adj_primal_bond a w h u v hadj
  rcases b with ⟨⟨bx, byy⟩, axis⟩
  cases axis
  · rcases Sym2.eq_iff.mp hpair with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    · simp [LatticeBond.faceBase] at hu' hv'
      simp [hu] at hu'
      simp [mem_latticeRectangle, LatticeBond.source, LatticeBond.target] at hbs hbt
      constructor
      · rw [hv']
        apply Prod.ext <;> omega
      · constructor <;> omega
    · simp [LatticeBond.faceBase] at hu' hv'
      simp [hu] at hu'
      simp [mem_latticeRectangle, LatticeBond.source, LatticeBond.target] at hbs hbt
      omega
  · rcases Sym2.eq_iff.mp hpair with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    all_goals simp [LatticeBond.faceBase, hu] at hu' hv'
    all_goals simp [mem_latticeRectangle, LatticeBond.source,
      LatticeBond.target] at hbs hbt
    all_goals omega

end
end PottsContinuity.FKC.FiniteFK
