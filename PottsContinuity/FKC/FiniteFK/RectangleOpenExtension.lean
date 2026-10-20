-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/RectangleOpenExtension.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleDualConfiguration
public import PottsContinuity.FKC.Medial.WholePlaneDualConfiguration
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

noncomputable def rectangleOpenExtensionState {a : LatticeVertex} {w h : ℕ}
    (A : Configuration (rectangleGraph a w h)) (e : rectanglePrimalEdgeCarrier a w h) :
    Bool := by
  classical
  exact decide (e ∈ A)

@[simp] theorem rectangleOpenExtensionState_eq_true_iff {a : LatticeVertex} {w h : ℕ}
    (A : Configuration (rectangleGraph a w h)) (e : rectanglePrimalEdgeCarrier a w h) :
    rectangleOpenExtensionState A e = true ↔ e ∈ A := by
  classical
  simp [rectangleOpenExtensionState]

@[simp] theorem rectangleOpenExtensionState_eq_false_iff {a : LatticeVertex} {w h : ℕ}
    (A : Configuration (rectangleGraph a w h)) (e : rectanglePrimalEdgeCarrier a w h) :
    rectangleOpenExtensionState A e = false ↔ e ∉ A := by
  classical
  simp [rectangleOpenExtensionState]

/-- Extend a finite rectangle configuration by declaring every primal edge
outside the literal rectangle edge image open. -/
noncomputable def rectangleOpenOutsideExtension (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) : LatticeConfiguration := by
  classical
  exact fun e => if he : ∃ f : rectanglePrimalEdgeCarrier a w h,
      rectanglePrimalEdgeToSquareEdge a w h f = e then
    rectangleOpenExtensionState A (Classical.choose he) else true

theorem rectanglePrimalEdgeToSquareEdge_injective (a : LatticeVertex) (w h : ℕ) :
    Function.Injective (rectanglePrimalEdgeToSquareEdge a w h) := by
  intro e f hef
  have hval := congrArg Subtype.val hef
  have hmap : Sym2.map (fun z : RectangleVertex a w h => z.val) e.1 =
      Sym2.map (fun z : RectangleVertex a w h => z.val) f.1 := by
    simpa [rectanglePrimalEdgeToSquareEdge] using hval
  have hsub : e.1 = f.1 := (Sym2.map.injective Subtype.val_injective) hmap
  exact Subtype.ext hsub

@[simp] theorem rectangleOpenOutsideExtension_on_edge (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (e : rectanglePrimalEdgeCarrier a w h) :
    rectangleOpenOutsideExtension a w h A (rectanglePrimalEdgeToSquareEdge a w h e) =
      rectangleOpenExtensionState A e := by
  classical
  unfold rectangleOpenOutsideExtension
  let hex : ∃ f : rectanglePrimalEdgeCarrier a w h,
      rectanglePrimalEdgeToSquareEdge a w h f = rectanglePrimalEdgeToSquareEdge a w h e :=
    ⟨e, rfl⟩
  rw [dite_eq_left hex]
  have he : Classical.choose hex = e :=
    rectanglePrimalEdgeToSquareEdge_injective a w h (Classical.choose_spec hex)
  rw [he]

 theorem rectangleOpenOutsideExtension_outside_open (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) (e : squareLattice.edgeSet)
    (hout : ∀ f : rectanglePrimalEdgeCarrier a w h,
      rectanglePrimalEdgeToSquareEdge a w h f ≠ e) :
    rectangleOpenOutsideExtension a w h A e = true := by
  simp [rectangleOpenOutsideExtension, hout]

/-- The finite actual open primal graph embeds into the whole-plane open graph
of the open-outside extension. -/
noncomputable def rectangleOpenOutsidePrimalGraphHom (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    openGraph (rectangleGraph a w h) A →g
      wholePlaneOpenPrimalGraph (rectangleOpenOutsideExtension a w h A) where
  toFun := fun u => u.val
  map_rel' := by
    intro u v huv
    have hmem : s(u,v) ∈ openEdges (rectangleGraph a w h) A :=
      (openGraph_adj _ _ _ _).mp huv
    rcases hmem with ⟨e, heA, heuv⟩
    let er : rectanglePrimalEdgeCarrier a w h := ⟨e.val, e.property⟩
    have herA : er ∈ A := heA
    have hadj : (rectangleGraph a w h).Adj u v := by
      apply (rectangleGraph a w h).mem_edgeSet.mp
      rw [← heuv]
      exact e.property
    have hsq : squareLattice.Adj u.val v.val :=
      (rectangleGraph_adj_iff a w h u v).mp hadj
    change ∃ hsq : squareLattice.Adj u.val v.val,
      rectangleOpenOutsideExtension a w h A
        ⟨s(u.val,v.val), squareLattice.mem_edgeSet.mpr hsq⟩ = true
    refine ⟨hsq, ?_⟩
    have hedge : rectanglePrimalEdgeToSquareEdge a w h er =
        ⟨s(u.val,v.val), squareLattice.mem_edgeSet.mpr hsq⟩ := by
      apply Subtype.ext
      change Sym2.map (fun z : RectangleVertex a w h => z.val) er.1 = s(u.val,v.val)
      have hm := congrArg (Sym2.map (fun z : RectangleVertex a w h => z.val)) heuv
      simpa [er] using hm
    rw [← hedge, rectangleOpenOutsideExtension_on_edge]
    exact (rectangleOpenExtensionState_eq_true_iff A er).2 herA

/-- Complementary finite dual edges embed as closed-dual edges of the same
open-outside extension. -/
noncomputable def rectangleOpenOutsideDualGraphHom (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    openGraph (rectangleDualGraph a w h) (rectangleDualConfiguration a w h A) →g
      wholePlaneClosedDualGraph (rectangleOpenOutsideExtension a w h A) where
  toFun := fun u => u.val
  map_rel' := by
    intro u v huv
    have hmem : s(u,v) ∈ openEdges (rectangleDualGraph a w h)
        (rectangleDualConfiguration a w h A) :=
      (openGraph_adj _ _ _ _).mp huv
    rcases hmem with ⟨g, hg, hpair⟩
    let e : RectangleDualEdgeCarrier a w h :=
      (rectangleDualGraphEdgeEquiv a w h).symm g
    have heq : rectangleDualGraphEdgeEquiv a w h e = g := Equiv.apply_symm_apply _ _
    have heA : e.primalEdge ∉ A := by
      rw [← heq] at hg
      exact (mem_rectangleDualConfiguration a w h A e).mp hg
    have hpair' : rectangleDualCarrierPair a w h e = s(u,v) := by
      calc
        rectangleDualCarrierPair a w h e = (rectangleDualGraphEdgeEquiv a w h e :
            (rectangleDualGraph a w h).edgeSet).val := by rfl
        _ = g.val := congrArg Subtype.val heq
        _ = s(u,v) := hpair
    have huvv : (u.val = e.crossingBond.source ∧ v.val = e.crossingBond.target) ∨
        (u.val = e.crossingBond.target ∧ v.val = e.crossingBond.source) := by
      have hm := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.val)) hpair'
      have hend : s(e.crossingBond.source,e.crossingBond.target) = s(u.val,v.val) := by
        simpa [rectangleDualCarrierPair, LatticeBond.toSym2,
          rectangleDualEdgeSource_val, rectangleDualEdgeTarget_val] using hm
      rcases Sym2.eq_iff.mp hend with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · exact Or.inl ⟨h1.symm, h2.symm⟩
      · exact Or.inr ⟨h2.symm, h1.symm⟩
    have hclosed : latticeConfigurationBondState
        (rectangleOpenOutsideExtension a w h A) (primalBondOfDual e.crossingBond) = false := by
      change rectangleOpenOutsideExtension a w h A
        (latticeBondEdge (primalBondOfDual e.crossingBond)) = false
      rw [rectangleDualEdge_crossing_originalEdge]
      rw [rectangleOpenOutsideExtension_on_edge]
      exact (rectangleOpenExtensionState_eq_false_iff A e.primalEdge).2 heA
    exact (wholePlaneClosedDualGraph_adj_iff_dualBond
      (rectangleOpenOutsideExtension a w h A) u.val v.val).mpr
        ⟨e.crossingBond, hclosed, huvv⟩

end
end PottsContinuity.FKC.FiniteFK
