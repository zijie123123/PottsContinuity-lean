module

public import PottsContinuity.Thm3.Push.AuxiliaryIndexInvariance
public import PottsContinuity.Thm3.Push.ClosedClusterFrontier
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.Duality
noncomputable section

/-- An actual closed dual edge preserves the index of a closed primal walk
whose in-rectangle bonds are all open in the sampled configuration. -/
theorem rectangle_closed_dual_adj_index_eq_of_open_trace
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hopen : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges → f ∈ A)
    {u v : RectangleDualVertex a w h}
    (huv : (openGraph (rectangleDualGraph a w h)
      (auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv a w h) A)).Adj u v) :
    rayIndex (faceIndexMark u.val) p = rayIndex (faceIndexMark v.val) p := by
  let e := DualityExt.rectangleDualEdgeEquiv a w h
  obtain ⟨g,hg,hpair⟩ := (openGraph_adj _ _ u v).mp huv
  let f := e.symm g
  let d := rectanglePrimalDualEdgeEquiv a w h f
  have hp : (e f).val = s(u,v) := by
    dsimp only [f]
    rw [Equiv.apply_symm_apply]
    exact hpair
  have hclosed : f ∉ A := (mem_auxiliaryClosedConfiguration e A g).mp hg
  have hidx := rayIndex_bond_faces_eq_of_not_mem p (rectanglePrimalEdgeBond a w h f)
    (fun he => hclosed (hopen f he))
  have hs : (rectangleDualEdgeSource a w h d).val =
      (rectanglePrimalEdgeBond a w h f).faceBase false := rectangleDualEdgeSource_faceBase a w h d
  have ht : (rectangleDualEdgeTarget a w h d).val =
      (rectanglePrimalEdgeBond a w h f).faceBase true := rectangleDualEdgeTarget_faceBase a w h d
  rw [← hs,← ht] at hidx
  have hp' : s(rectangleDualEdgeSource a w h d,rectangleDualEdgeTarget a w h d) = s(u,v) := hp
  rcases Sym2.eq_iff.mp hp' with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · simpa only [hu,hv] using hidx
  · have hi : rayIndex (faceIndexMark v.val) p = rayIndex (faceIndexMark u.val) p := by
      simpa only [hu,hv] using hidx
    exact hi.symm

/-- The same sampled-state argument propagates through an entire genuine
closed-dual walk, retaining the exact face-index mark shift. -/
theorem rectangle_closed_dual_walk_index_eq_of_open_trace
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hopen : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges → f ∈ A)
    {u v : RectangleDualVertex a w h}
    (q : (openGraph (rectangleDualGraph a w h)
      (auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv a w h) A)).Walk u v) :
    rayIndex (faceIndexMark u.val) p = rayIndex (faceIndexMark v.val) p := by
  induction q with
  | nil => rfl
  | @cons u t v hut q ih =>
    exact (rectangle_closed_dual_adj_index_eq_of_open_trace a w h A p hopen hut).trans ih

/-- Every face reached by the actual raw exploration inherits the index
computed at its genuine seed. -/
theorem rectangle_closed_reached_index_of_open_trace
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (seeds : Finset (RectangleDualVertex a w h))
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hopen : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges → f ∈ A)
    (k : ℤ) (hseed : ∀ s ∈ seeds, rayIndex (faceIndexMark s.val) p = k)
    (v : RectangleDualVertex a w h)
    (hv : v ∈ closedClusterReached (DualityExt.rectangleDualEdgeEquiv a w h) seeds A) :
    rayIndex (faceIndexMark v.val) p = k := by
  obtain ⟨s,hs,⟨q⟩⟩ := hv
  exact (rectangle_closed_dual_walk_index_eq_of_open_trace a w h A p hopen q).symm.trans (hseed s hs)

/-- Each raw queried original bond has a genuine crossing face carrying
the seed index. This applies to the unfilled exploration itself. -/
theorem rectangle_raw_query_has_seed_index_of_open_trace
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (seeds : Finset (RectangleDualVertex a w h))
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hopen : ∀ f : (rectangleGraph a w h).edgeSet,
      (rectanglePrimalEdgeBond a w h f).toSym2 ∈ p.edges → f ∈ A)
    (k : ℤ) (hseed : ∀ s ∈ seeds, rayIndex (faceIndexMark s.val) p = k)
    (f : (rectangleGraph a w h).edgeSet)
    (hf : f ∈ closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) seeds A) :
    ∃ v ∈ (DualityExt.rectangleDualEdgeEquiv a w h f).val,
      rayIndex (faceIndexMark v.val) p = k := by
  obtain ⟨v,hvf,hv⟩ := (mem_closedClusterReveal_iff_endpoint _ seeds A f).mp hf
  exact ⟨v,hvf,rectangle_closed_reached_index_of_open_trace a w h A seeds p hopen k hseed v hv⟩

end
end PottsContinuity.Push
