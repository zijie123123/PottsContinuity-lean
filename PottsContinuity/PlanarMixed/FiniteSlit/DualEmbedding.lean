module

public import PottsContinuity.PlanarMixed.FiniteSlit.Configurations
public import PottsContinuity.PlanarMixed.FiniteSlit.RectangleConditioning
public import PottsContinuity.PD.Duality.RectangleDualAmbient

/-! The finite reflected graph as actual cells in the original rectangle dual.
The half-integer dual shift is retained explicitly, including boundary cells. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12 DualityExt
noncomputable section

/-- Reflected integer vertices become original dual face bases. -/
def faceMap (x : ℤ) (z : LatticeVertex) : LatticeVertex := (2*x-1-z.1,z.2-1)

theorem faceMap_injective (x : ℤ) : Function.Injective (faceMap x) := by
  intro u v h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> dsimp [faceMap] at hx hy <;> omega

/-- This bounded map includes original bottom and side exterior faces. -/
theorem faceMap_mem_expanded (M : ℕ) (x : ℤ) (hM : 2 ≤ M) (u : Vertex M x) :
    faceMap x u.val ∈ rectangleDualExpanded (x-(M : ℤ),0) (2*M-1) M := by
  have hu := (mem_rectangle_iff M x (by omega) u.val).mp u.property
  have hw : ((2*M-1 : ℕ) : ℤ) = 2*(M : ℤ)-1 := by omega
  simp only [rectangleDualExpanded,PD.FK.mem_latticeRectangle,faceMap,
    Nat.cast_add,Nat.cast_one,hw]
  omega

/-- Literal finite reflected vertex embedding into the actual dual host. -/
def cellEmbedding (M : ℕ) (x : ℤ) (hM : 2 ≤ M) :
    Vertex M x ↪ RectangleDualVertex (x-(M : ℤ),0) (2*M-1) M where
  toFun u := ⟨faceMap x u.val,faceMap_mem_expanded M x hM u⟩
  inj' := fun _ _ h => Subtype.ext (faceMap_injective x (congrArg Subtype.val h))

/-- Original crossing edges coincide with the face-image of reflected bonds. -/
theorem crossingBond_faceMap_pair (x : ℤ) (b : LatticeBond) :
    (dualBondOfPrimal b).toSym2 = Sym2.map (faceMap x) (slitReflectedBond x b).toSym2 := by
  rcases b with ⟨⟨a,k⟩,ax⟩
  cases ax <;> simp [dualBondOfPrimal,LatticeBond.toSym2,LatticeBond.source,
    LatticeBond.target,faceMap,slitReflectedBond,Prod.mk.injEq]; omega

/-- A normalized source bond determines its literal labelled rectangle crossing. -/
def crossingEdge (M : ℕ) (x : ℤ) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M)
    (ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M) :
    RectangleDualEdgeCarrier (x-(M : ℤ),0) (2*M-1) M :=
  rectanglePrimalDualEdgeEquiv _ _ _ (rectanglePrimalBondToEdge _ _ _ ⟨b,hs,ht⟩)

/-- Its actual crossing bond is exactly the original normalized dual bond. -/
theorem crossingEdge_bond (M : ℕ) (x : ℤ) (b : LatticeBond) (hs ht) :
    (crossingEdge M x b hs ht).crossingBond = dualBondOfPrimal b := by
  change dualBondOfPrimal (rectanglePrimalEdgeBond _ _ _
    (rectanglePrimalBondToEdge _ _ _ ⟨b,hs,ht⟩)) = _
  have hb := congrArg Subtype.val
    ((rectanglePrimalEdgeBondEquiv (x-(M : ℤ),0) (2*M-1) M).right_inv ⟨b,hs,ht⟩)
  exact congrArg dualBondOfPrimal hb

/-- Every reflected active sampled edge embeds as its true original crossing
edge in the rectangle dual, including ports adjacent to exterior faces. -/
theorem dualGraph_map_le_rectangleDual (M : ℕ) (x y : ℤ) (hM : 2 ≤ M) :
    (dualGraph M x y).map (cellEmbedding M x hM) ≤
      rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M := by
  intro u v huv
  obtain ⟨a,c,hac,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp huv
  obtain ⟨⟨b,hb,hpair⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hac
  let e := crossingEdge M x b hb.1 hb.2.1
  apply (rectangleDualGraph_adj_iff _ _ _ _ _).mpr
  refine ⟨e,?_⟩
  symm
  apply Sym2.map.injective Subtype.val_injective
  change Sym2.map Subtype.val (rectangleDualCarrierPair _ _ _ e) =
    s(faceMap x a.val,faceMap x c.val)
  calc
    _ = e.crossingBond.toSym2 := by
      simp [rectangleDualCarrierPair,LatticeBond.toSym2]
    _ = (dualBondOfPrimal b).toSym2 := congrArg LatticeBond.toSym2 (crossingEdge_bond M x b _ _)
    _ = Sym2.map (faceMap x) (slitReflectedBond x b).toSym2 := crossingBond_faceMap_pair x b
    _ = _ := by rw [hpair]; rfl

end
end PottsContinuity.PlanarMixed.FiniteSlit
