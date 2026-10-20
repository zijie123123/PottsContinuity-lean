module

public import PottsContinuity.PlanarMixed.FiniteSlit.ClosedBandIdentification
public import PottsContinuity.PlanarMixed.FiniteSlit.BoundaryPartition
public import PottsContinuity.Thm3.Push.SourceAlphaBarrierIndex

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK PD.Duality PlanarMixed.FiniteSlit
noncomputable section
local instance barrierIndexEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- An internal arc walk starting on beta stays on beta: the two wired arcs
are disjoint and each auxiliary bond belongs to one arc. -/
theorem internalArc_walk_beta_support (M : ℕ) (x y : ℤ) (hM : 2 ≤ M)
    (hy : 0 < y) (hyM : y < (M:ℤ))
    {a b : Vertex M x} (p : (openGraph (graph M x y) (internalEdges M x y)).Walk a b)
    (ha : a ∈ beta M x y) : ∀ z ∈ p.support, z ∈ beta M x y := by
  classical
  induction p with
  | nil => simpa using ha
  | @cons a c b hac p ih =>
    obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ a c).mp hac
    have hG := openGraph_le _ _ hac
    have heval : e = (⟨s(a,c),(graph M x y).mem_edgeSet.mpr hG⟩ : (graph M x y).edgeSet) := Subtype.ext heq
    have heF : e ∈ (internalEdges M x y : Finset (graph M x y).edgeSet) := he
    clear he
    rw [heval,internalEdges,Finset.mem_union,
      mem_internalBonds_pair _ _ a c hG,mem_internalBonds_pair _ _ a c hG] at heF
    have hc : c ∈ beta M x y := by
      rcases heF with he | he
      · exact (Set.disjoint_left.mp (alpha_disjoint_beta M x y hM hy hyM) he.1 ha).elim
      · exact he.2
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ha
    · exact ih hc z hz

/-- Beta-side source reachability transports the reference barrier index,
including paths through either deterministic exterior vertex. -/
theorem sourceBeta_cutReach_index_of_slitBarrier
    (M : ℕ) (x y b : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ)<0) (hright : (w:ℤ)<x+(M:ℤ)-1)
    (hh : h<M) (hyh : y ≤ (h:ℤ)) {t z : LatticeVertex}
    (q : squareLattice.Walk (b,0) t)
    (hsource : ∀ v ∈ q.support, v ∈ PD.FK.latticeRectangle (0,0) w h)
    (p : squareLattice.Walk z z)
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges M x y b q)
    (k : ℤ) (hβ : ∀ v : Vertex M x, v ∈ beta M x y → v.val ∉ q.support → rayIndex v.val p=k)
    (u : RectangleVertex (0,0) w h)
    (hu : Sum.inl u ∈ cutReachRegion (sourceExteriorGraph w h x y)
      (Sum.inl '' sourceCoordinateTrace w h {v | v ∈ q.support}) (sourceBeta w h x y)) :
    rayIndex u.val p=k := by
  classical
  let f := rectangleIntoReference M x w h (by omega) hleft.le hright.le hh.le
  have hcut : f '' sourceCoordinateTrace w h {v | v ∈ q.support} =
      {v : Vertex M x | v.val ∈ q.support} := by
    ext v
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro hv
      exact ⟨⟨v.val,hsource v.val hv⟩,hv,Subtype.ext rfl⟩
  have ht := source_cutReachRegion_iff M x y w h hM hx hxw hleft hright hh hyh
    (sourceCoordinateTrace w h {v | v ∈ q.support}) (beta M x y) u
  rw [exteriorProjection_image_beta M x y w h hM hx hxw hleft hright hh] at ht
  have href := ht.mp hu
  change f u ∈ cutReachRegion (graph M x y)
    (f '' sourceCoordinateTrace w h {v | v ∈ q.support}) (beta M x y) at href
  rw [hcut] at href
  obtain ⟨a,ha,r,hr⟩ := href
  have hi := rayIndex_eq_of_slitBarrier M x y b hM q p hallowed r hr
  exact hi.symm.trans (hβ a ha (hr a r.start_mem_support))

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
