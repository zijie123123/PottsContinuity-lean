module

public import PottsContinuity.Thm3.Push.NativeRetainedPathsOnAugmented
public import PottsContinuity.Thm3.Push.StrictFirstHitPrefixSelection
public import PottsContinuity.PlanarMixed.FiniteSlit.OpenSourceCrosscuts
public import PottsContinuity.PlanarMixed.EmbeddedOpenRestriction
public import PottsContinuity.PlanarMixed.RetainedWalk
public import PottsContinuity.PlanarMixed.SlitGlobalOpenGraph

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 RSW PlanarMixed PlanarMixed.FiniteSlit
noncomputable section
local instance nativeSlitPrefixEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- The genuine stopped source domain: keep retained slit bonds and isolate every
vertex of the already selected tip. All remaining vertices are original. -/
def sourceSlitPrefixGraph (w h : ℕ) (x y : ℤ) (tip : Set (RectangleVertex (0,0) w h)) :
    SimpleGraph (RectangleVertex (0,0) w h) where
  Adj u v := (sourceRetainedGraph w h x y).Adj u v ∧ u ∉ tip ∧ v ∉ tip
  symm := by constructor; rintro u v ⟨h,hu,hv⟩; exact ⟨h.symm,hv,hu⟩
  loopless := by constructor; intro u hloop; exact (sourceRetainedGraph w h x y).loopless.irrefl u hloop.1

/-- Every stopped-domain bond remains the exact original source bond. -/
theorem sourceSlitPrefixGraph_map_le (w h : ℕ) (x y : ℤ) (tip : Set (RectangleVertex (0,0) w h)) :
    (sourceSlitPrefixGraph w h x y tip).map (Function.Embedding.refl _) ≤ rectangleGraph (0,0) w h := by
  change (sourceSlitPrefixGraph w h x y tip).map id ≤ _
  rw [SimpleGraph.map_id]
  intro u v huv
  have hret := huv.1
  change (slitRetainedBondGraph x y).Adj u.val v.val at hret
  exact ((slitRetainedBondGraph_adj_iff x y _ _).mp hret).1

/-- The exact native prefix bonds belong to the stopped slit graph and
avoid the selected tip. The finite reference crop supplies retained bonds. -/
theorem native_prefix_bonds_in_stopped_slit
    (n : ℕ) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (I J : Set (RectangleVertex (0,0) (2*n) (2*n))) (D : NativeSourceArms n C I J)
    {u v : RectangleVertex (0,0) (2*n) (2*n)}
    (he : s(u,v) ∈ (D.paths.first.take D.cropIndex).edges) :
    (sourceSlitPrefixGraph (2*n) (2*n) D.column D.paths.secondEnd.val.2
      {z | z ∈ D.paths.second.support}).Adj u v := by
  have hx := D.column_pos
  obtain ⟨R,_,_,_,_,_,_,hPe,_⟩ := openSourceSquare_exists_crosscutData_at_firstContact n
    D.column D.paths.secondEnd.val.2 D.rightColumn D.column_pos D.column_le C
    D.paths.first D.paths.second D.first_bottom D.second_bottom D.first_end_column
    D.first_start_right D.starts_order (Prod.ext D.second_end_column rfl)
    D.first_bounds D.second_bounds D.disjoint D.cropIndex D.first_contact
  have hRf : s((sourceSquareSlitEmbedding n D.column (by omega) D.column_le) u,
      (sourceSquareSlitEmbedding n D.column (by omega) D.column_le) v) ∈ R.first.edges := by
    rw [hPe]
    exact List.mem_map.mpr ⟨s(u,v),he,rfl⟩
  have hRA := R.first.adj_of_mem_edges hRf
  have hn := hRA.2
  change ¬ (D.paths.secondEnd.val.2 < u.val.2 ∧ D.paths.secondEnd.val.2 < v.val.2 ∧
    ((u.val.1 = D.column-1 ∧ v.val.1 = D.column) ∨ (v.val.1 = D.column-1 ∧ u.val.1 = D.column))) at hn
  have hu := (mem_latticeRectangle _ _ _ _).mp u.property
  have hv := (mem_latticeRectangle _ _ _ _).mp v.property
  refine ⟨?_,?_,?_⟩
  · change (slitRetainedBondGraph D.column D.paths.secondEnd.val.2).Adj u.val v.val
    rw [slitRetainedBondGraph_adj_iff]
    exact ⟨openGraph_le _ C ((D.paths.first.take D.cropIndex).adj_of_mem_edges he),by dsimp at hu; omega,by dsimp at hv; omega,hn⟩
  · exact D.disjoint u ((D.paths.first.isSubwalk_take D.cropIndex).support_subset
      ((D.paths.first.take D.cropIndex).fst_mem_support_of_mem_edges he))
  · exact D.disjoint v ((D.paths.first.isSubwalk_take D.cropIndex).support_subset
      ((D.paths.first.take D.cropIndex).snd_mem_support_of_mem_edges he))

end
end PottsContinuity.Push
