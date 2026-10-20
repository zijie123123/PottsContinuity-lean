module

public import PottsContinuity.Thm3.Push.CompletionFreePrefixSelection
public import PottsContinuity.PlanarMixed.FiniteSlit.NativeSourceArms

@[expose] public section

namespace PottsContinuity.Push
open PD.FK Exploration PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance retainedAugmentedEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- The retained tip remains an actual open walk on an augmented source
fiber. No discarded source-arm completion is requested. -/
theorem source_tip_openWalk_on_augmented_fiber
    (w h : ℕ) (x y : ℤ) (first second : Set LatticeVertex)
    (C D : Configuration (rectangleGraph (0,0) w h))
    {a b : RectangleVertex (0,0) w h}
    (p : (openGraph (rectangleGraph (0,0) w h) C).Walk a b)
    (htrace : ∀ z ∈ p.support, z.val ∈ second)
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
  have hu : u ∈ pocketAugmentedSourceRightExterior w h x y (sourceCoordinateTrace w h second) :=
    Or.inl (Or.inr ⟨u,htrace u (p.fst_mem_support_of_mem_edges he),rfl⟩)
  have hv : v ∈ pocketAugmentedSourceRightExterior w h x y (sourceCoordinateTrace w h second) :=
    Or.inl (Or.inr ⟨v,htrace v (p.snd_mem_support_of_mem_edges he),rfl⟩)
  have hR : e ∈ pocketAugmentedSourceReveal w h x y first second :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_union.mpr (Or.inr
      ((mem_internalBonds_pair _ _ u v hadj).mpr ⟨hu,hv⟩))))
  have hD : e ∈ D := by
    have hd : e ∈ D ∩ pocketAugmentedSourceReveal w h x y first second := by
      rw [hstates]
      exact Finset.mem_inter.mpr ⟨hC,hR⟩
    exact (Finset.mem_inter.mp hd).1
  exact (openGraph_adj _ D u v).mpr ⟨e,hD,rfl⟩

/-- Correct fiber decoder: keep the base geometry and transport exactly
its retained prefix and tip into the agreeing sample. A full first-arm
completion in that sample is neither assumed nor concluded. -/
theorem native_retained_paths_open_on_augmented_fiber
    (n : ℕ) (C C' : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (I J : Set (RectangleVertex (0,0) (2*n) (2*n)))
    (D : NativeSourceArms n C I J)
    (hstates : C' ∩ pocketAugmentedSourceReveal (2*n) (2*n) D.column D.paths.secondEnd.val.2
        D.croppedTrace D.tipTrace =
      C ∩ pocketAugmentedSourceReveal (2*n) (2*n) D.column D.paths.secondEnd.val.2
        D.croppedTrace D.tipTrace) :
    ∃ p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C').Walk
        D.paths.firstStart (D.paths.first.getVert D.cropIndex),
    ∃ q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C').Walk
        D.paths.secondStart D.paths.secondEnd,
      p.support = (D.paths.first.take D.cropIndex).support ∧ q.support = D.paths.second.support := by
  obtain ⟨p,hp⟩ := source_prefix_openWalk_on_augmented_fiber (2*n) (2*n) D.column D.paths.secondEnd.val.2
    D.croppedTrace D.tipTrace C C' (D.paths.first.take D.cropIndex)
    (fun z hz => ⟨z,hz,rfl⟩) hstates
  obtain ⟨q,hq⟩ := source_tip_openWalk_on_augmented_fiber (2*n) (2*n) D.column D.paths.secondEnd.val.2
    D.croppedTrace D.tipTrace C C' D.paths.second (fun z hz => ⟨z,hz,rfl⟩) hstates
  exact ⟨p,q,hp,hq⟩

end
end PottsContinuity.Push
