module

public import PottsContinuity.Thm3.Prop4.RetainedCentralRows
public import PottsContinuity.PlanarTopology.RectangleSampledClosedDual

/-!
# Every eligible connector row is genuinely sampled and can be closed

The row edge is constructed directly from its two physical endpoints. Its
actual remaining-edge membership and restored original state agree exactly.
Closing the retained row set therefore supplies every required sampled dual step.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK PD.FK.Medial
noncomputable section
local instance retainedRowOriginalEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _
local instance retainedRowRemainingEdgeFintype (n : ℕ) (r : ℝ) (u v : LatticeVertex) :
    Fintype (tubePrimalRemainingGraph n r u v).edgeSet := Fintype.ofFinite _

def centralPhysicalPrimalBond {n : ℕ} (hn : 1 ≤ n) (y : ℤ)
    (hy : -(n : ℤ) ≤ y ∧ y ≤ n) : RectanglePrimalBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) := by
  refine ⟨⟨(0,y),.horizontal⟩,?_,?_⟩
  all_goals
    rw [PlanarTopology.latticeRectangle_neg_eq_box]
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (by dsimp [LatticeBond.source,LatticeBond.target]; omega),
      Finset.mem_Icc.mpr hy⟩

/-- The unique actual retained edge of an eligible physical central row. -/
def retainedCentralRowEdge {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (u v : LatticeVertex)
    (y : ℤ) (hy : -(n : ℤ) ≤ y ∧ y ≤ n) (hyNot : y ∉ radiusTubeCutRows n r u v 0) :
    (tubePrimalRemainingGraph n r u v).edgeSet :=
  (edgeRestrictionEdgeEquiv _ (rectangleTubeRevealedEdges n r u v)).symm
    ⟨rectanglePrimalBondToEdge _ _ _ (centralPhysicalPrimalBond hn y hy),by
      intro he
      exact hyNot ((central_horizontal_revealed_iff_row n r u v y
        (centralPhysicalPrimalBond hn y hy) rfl).mp he)⟩

/-- The retained row edge keeps exactly its original two physical endpoints. -/
theorem retainedCentralRowEdge_coordinates {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (u v : LatticeVertex)
    (y : ℤ) (hy : -(n : ℤ) ≤ y ∧ y ≤ n) (hyNot : y ∉ radiusTubeCutRows n r u v 0) :
    Sym2.map Subtype.val (retainedCentralRowEdge hn r u v y hy hyNot).val = s((0,y),(1,y)) := rfl

/-- Every eligible physical row of the interval occurs in the actual connector
set, so none of the source's required sampled steps is omitted. -/
theorem retainedCentralRowEdge_mem_rows {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (u v : LatticeVertex)
    (a b y : ℤ) (hy : -(n : ℤ) ≤ y ∧ y ≤ n) (hyNot : y ∉ radiusTubeCutRows n r u v 0)
    (hyIcc : y ∈ Finset.Icc a b) :
    retainedCentralRowEdge hn r u v y hy hyNot ∈ tubeRemainingCentralRows n r u v a b := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hyIcc,retainedCentralRowEdge_coordinates hn r u v y hy hyNot⟩

/-- Restoring a prescribed revealed state changes no membership of a retained
original edge; this is an exact state identity on the whole remaining carrier. -/
theorem remaining_restored_edge_mem_iff {V : Type*} (G : SimpleGraph V) [DecidableEq G.edgeSet]
    (R : Configuration G) (B : RemovedConfiguration G R)
    (e : (edgeRestriction G R).edgeSet) (C : Configuration (edgeRestriction G R)) :
    edgeRestrictionEdgeEmbedding G R e ∈ (edgeRestrictionConfigurationEquiv G R C).val ∪ B.val ↔ e ∈ C := by
  have hnotB : edgeRestrictionEdgeEmbedding G R e ∉ B.val := by
    intro he
    exact (edgeRestrictionEdgeEquiv G R e).property (B.property he)
  constructor
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · rw [edgeRestrictionConfigurationEquiv_val] at he
      obtain ⟨g,hg,hge⟩ := Finset.mem_map.mp he
      exact (edgeRestrictionEdgeEmbedding G R).injective hge ▸ hg
    · exact False.elim (hnotB he)
  · intro he
    apply Finset.mem_union_left
    rw [edgeRestrictionConfigurationEquiv_val]
    exact Finset.mem_map.mpr ⟨e,he,rfl⟩

/-- Closing the actual retained connector set gives the actual closed-dual
step at every eligible original row in the SAME restored primal sample. -/
theorem tubeRemainingCentralRows_closed_dual_step {n : ℕ} (hn : 1 ≤ n) (r : ℝ)
    (u v : LatticeVertex) (a b y : ℤ) (hy : -(n : ℤ) ≤ y ∧ y ≤ n)
    (hyNot : y ∉ radiusTubeCutRows n r u v 0) (hyIcc : y ∈ Finset.Icc a b)
    (C : Configuration (tubePrimalRemainingGraph n r u v))
    (hC : Disjoint C (tubeRemainingCentralRows n r u v a b)) :
    (PlanarTopology.rectangleSampledClosedDualGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      ((edgeRestrictionConfigurationEquiv _ (rectangleTubeRevealedEdges n r u v) C).val ∪
        rectangleTubeRevealedEdges n r u v)).Adj (0,y-1) (0,y) := by
  let e := retainedCentralRowEdge hn r u v y hy hyNot
  have heF := retainedCentralRowEdge_mem_rows hn r u v a b y hy hyNot hyIcc
  have heNot : e ∉ C := fun he => (Finset.disjoint_left.mp hC) he heF
  have hstate := remaining_restored_edge_mem_iff _ (rectangleTubeRevealedEdges n r u v)
    ⟨rectangleTubeRevealedEdges n r u v,Finset.Subset.refl _⟩ e C
  have hnot : rectanglePrimalBondToEdge (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (centralPhysicalPrimalBond hn y hy) ∉
      (edgeRestrictionConfigurationEquiv _ (rectangleTubeRevealedEdges n r u v) C).val ∪
        rectangleTubeRevealedEdges n r u v := by
    change edgeRestrictionEdgeEmbedding _ (rectangleTubeRevealedEdges n r u v) e ∉ _
    exact fun h => heNot (hstate.mp h)
  simpa [centralPhysicalPrimalBond,dualBondOfPrimal,LatticeBond.source,LatticeBond.target] using
    PlanarTopology.rectangleSampledClosedDualGraph_adj_of_closed_bond _ _ _ _
      (centralPhysicalPrimalBond hn y hy) hnot

end
end PottsContinuity.Thm3.Prop4
