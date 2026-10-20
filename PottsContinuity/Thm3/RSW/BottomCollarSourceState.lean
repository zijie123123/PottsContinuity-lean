module

public import PottsContinuity.Thm3.RSW.BottomCollarSourcePartition
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- The two existing rectangle graph presentations have exactly the same
nearest-neighbour relation on their unchanged common vertex carrier. -/
theorem rectangleGraph_eq_FKC (a : LatticeVertex) (w h : ℕ) :
    rectangleGraph a w h = FKC.rectangleGraph a w h := by
  ext u v
  exact (PD.FK.squareLattice_adj_iff u.val v.val).trans
    (FKC.squareLattice_adj_iff u.val v.val).symm

/-- All deleted collar bonds are fixed open. This is the genuine PD removed
state on the PD sampled graph, with no change of edge carrier. -/
def bottomCollarSourceState (a : LatticeVertex) (w h : ℕ) :
    RemovedConfiguration (rectangleGraph (a.1,a.2-1) w (h+1))
      (subgraphRemovedEdges
        ((rectangleGraph a w h).map (FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h))
        (rectangleGraph (a.1,a.2-1) w (h+1))) :=
  ⟨_,Finset.Subset.rfl⟩

/-- The exact PD collar observation realizes the bottom-wired partition. -/
theorem bottomCollarSourceState_partition (a : LatticeVertex) (w h : ℕ) :
    (isolatedExtensionPullbackBoundary
      (FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h)
      (frozenBoundary (BoundaryCondition.free ∅)
        (bottomCollarSourceState a w h).val)).partition =
    (BoundaryCondition.wired {v : RectangleVertex a w h | v.val.2 = a.2}).partition := by
  have hgen (J : SimpleGraph (RectangleVertex a w h))
      (H : SimpleGraph (RectangleVertex (a.1,a.2-1) w (h+1)))
      (hJ : J = FKC.rectangleGraph a w h)
      (hH : H = FKC.rectangleGraph (a.1,a.2-1) w (h+1)) :
      Setoid.comap (FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h)
        (componentSetoid H (BoundaryCondition.free ∅)
          (subgraphRemovedEdges
            (J.map (FKC.FiniteFK.rectangleArbitraryBottomCollarEmbedding a w h)) H)) =
      (BoundaryCondition.wired {v : RectangleVertex a w h | v.val.2 = a.2}).partition := by
    subst J
    subst H
    exact bottomCollar_source_partition a w h
  exact hgen _ _ (rectangleGraph_eq_FKC a w h)
    (rectangleGraph_eq_FKC (a.1,a.2-1) w (h+1))

end
end PottsContinuity.RSW
