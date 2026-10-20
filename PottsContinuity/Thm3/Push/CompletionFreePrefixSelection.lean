module

public import PottsContinuity.Thm3.Push.BoundaryPathCodeWitness
public import PottsContinuity.Thm3.Push.FirstContactTrace
public import PottsContinuity.Thm3.Push.PocketAugmentedSourceReveal
public import PottsContinuity.Exploration.SourceTraceFiberOpen

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance completionFreePrefixEdgeEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- A literal prefix remains open on every augmented source fiber. This
consumes the general walk-transfer API; it does not preserve a discarded
completion or claim stability of a least-code choice. -/
theorem source_prefix_openWalk_on_augmented_fiber
    (w h : ℕ) (x y : ℤ) (first second : Set LatticeVertex)
    (C D : Configuration (rectangleGraph (0,0) w h))
    {a b : RectangleVertex (0,0) w h}
    (p : (openGraph (rectangleGraph (0,0) w h) C).Walk a b)
    (htrace : ∀ z ∈ p.support, z.val ∈ first)
    (hstates : D ∩ pocketAugmentedSourceReveal w h x y first second =
      C ∩ pocketAugmentedSourceReveal w h x y first second) :
    ∃ q : (openGraph (rectangleGraph (0,0) w h) D).Walk a b, q.support = p.support := by
  classical
  apply openWalk_transfer_of_edgewise_adjacency (rectangleGraph (0,0) w h) C D p
  intro u v he
  have hadj := openGraph_le _ C (p.adj_of_mem_edges he)
  let e : (rectangleGraph (0,0) w h).edgeSet := ⟨s(u,v),(rectangleGraph (0,0) w h).mem_edgeSet.mpr hadj⟩
  have hC : e ∈ C := (coe_mem_openEdges_iff _ C e).mp
    ((openGraph_adj _ C u v).mp (p.adj_of_mem_edges he))
  have hu : u ∈ pocketAugmentedSourceLeftExterior w h x y (sourceCoordinateTrace w h first) :=
    Or.inl (Or.inr ⟨u,htrace u (p.fst_mem_support_of_mem_edges he),rfl⟩)
  have hv : v ∈ pocketAugmentedSourceLeftExterior w h x y (sourceCoordinateTrace w h first) :=
    Or.inl (Or.inr ⟨v,htrace v (p.snd_mem_support_of_mem_edges he),rfl⟩)
  have hR : e ∈ pocketAugmentedSourceReveal w h x y first second :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inl
      ((mem_internalBonds_pair _ _ u v hadj).mpr ⟨hu,hv⟩))))
  have hD : e ∈ D := by
    have hd : e ∈ D ∩ pocketAugmentedSourceReveal w h x y first second := by
      rw [hstates]
      exact Finset.mem_inter.mpr ⟨hC,hR⟩
    exact (Finset.mem_inter.mp hd).1
  exact (openGraph_adj _ D u v).mpr ⟨e,hD,rfl⟩

end
end PottsContinuity.Push
