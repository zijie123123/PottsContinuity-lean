module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.PaddedCompletion
public import PottsContinuity.PlanarMixed.StripRSWSelectors.PrefixBarrierIndices
public import PottsContinuity.PlanarMixed.StripRSWSelectors.LeftSlitPortIndices
public import PottsContinuity.PlanarMixed.StripRSWSelectors.UpperRayExterior
public import PottsContinuity.Thm3.Push.OffTraceFaceIndex
public import PottsContinuity.Thm3.Push.ClosedDualTraceIndex
public import PottsContinuity.Thm3.Push.AugmentedOppositeReach

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK PD.Duality Push PlanarMixed.FiniteSlit
noncomputable section

/-- Every original raw left query has both endpoints in the augmented left
exterior of the stopped prefix. The literal open barrier, its two computed
indices and its support are retained as deterministic geometric data. -/
theorem raw_left_source_query_endpoints_of_barrier
    (n M : ℕ) (x y a t : ℤ) (hM : 2 ≤ M) (hx : 1 ≤ x) (hxa : x ≤ a)
    (hxw : x ≤ (2*n:ℕ)) (hleft : x-(M:ℤ)<0) (hright : (2*n:ℕ)<x+(M:ℤ)-1)
    (hNM : 2*n+2 ≤ M) (hyt : y ≤ t) (hyh : y ≤ (2*n:ℕ))
    (P : squareLattice.Walk (a,0) (x-1,t))
    (hsource : ∀ z ∈ P.support, z ∈ PD.FK.latticeRectangle (0,0) (2*n) (2*n))
    (hfirst : firstContactTrace {z | z.1=x-1 ∧ y ≤ z.2} P.support=some P.support)
    (L : squareLattice.Walk (a,0) (a,0))
    (hallowed : ∀ e ∈ L.edges, e ∈ slitBarrierEdges M x y a P)
    (hα : ∀ v : Vertex M x, v ∈ alpha M x → rayIndex v.val L=1)
    (hβ : ∀ v : Vertex M x, v ∈ beta M x y → rayIndex v.val L=0)
    (hsupport : ∀ w ∈ L.support,
      x-(M:ℤ) ≤ w.1 → w.1 ≤ x+(M:ℤ)-1 → 0 ≤ w.2 → w.2 ≤ (M:ℤ) →
      w ∈ P.support ∨ (w.1=x-1 ∧ t ≤ w.2))
    (A : Configuration (prefixAuxGraph n))
    (hopen : ∀ f : (prefixAuxGraph n).edgeSet,
      (rectanglePrimalEdgeBond (0,0) (2*n+1) (2*n+1) f).toSym2 ∈ L.edges → f ∈ A)
    (e : (rectangleGraph (0,0) (2*n) (2*n)).edgeSet)
    (he : embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n)
      (DualityExt.rectangleGraph_map_rectangleVertexEmbedding (prefix_padding_rectangle_subset n)) e ∈
        intervalArmLeftReveal (2*n+1) x A)
    (u : PrefixSourceVertex n) (hu : u ∈ e.val) :
    u ∈ pocketAugmentedSourceLeftExterior (2*n) (2*n) x y
      (sourceCoordinateTrace (2*n) (2*n) {z | z ∈ P.support}) := by
  classical
  have hub := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  dsimp at hub
  by_cases huP : u.val ∈ P.support
  · left
    right
    exact ⟨u,huP,rfl⟩
  by_cases huL : u.val ∈ L.support
  · rcases hsupport u.val huL (by omega) (by omega) hub.2.1 (by omega) with huP' | huRay
    · exact (huP huP').elim
    · exact sourceLeftExterior_subset_pocketAugmented _ _ _ _ _
        (source_upper_ray_mem_leftExterior (2*n) (2*n) a x y t hyt P hfirst u huRay.1 huRay.2)
  apply mem_pocketAugmented_of_not_opposite_reachable
  intro hreach
  have hzero := sourceBeta_cutReach_index_of_slitBarrier M x y a (2*n) (2*n)
    hM hx hxw hleft hright (by omega) hyh P hsource L hallowed 0
    (fun v hv _ => hβ v hv) u hreach
  have hnonneg : ∀ z ∈ P.support, 0 ≤ z.1 := by
    intro z hz
    exact ((PD.FK.mem_latticeRectangle _ _ _ _).mp (hsource z hz)).1.1
  have hseeds := leftSlitBarrier_interval_left_ports_index_one (2*n+1) M x y a t hM hx hxa
    hleft.le (by omega) hNM P hnonneg L hallowed hα
  let E := embeddedEdgeEmbedding _ _ (prefixPaddingEmbedding n)
    (DualityExt.rectangleGraph_map_rectangleVertexEmbedding (prefix_padding_rectangle_subset n)) e
  obtain ⟨v,hv,hidx⟩ := rectangle_raw_query_has_seed_index_of_open_trace (0,0) (2*n+1) (2*n+1)
    A (intervalArmLeftDualPorts (2*n+1) x) L hopen 1 hseeds E he
  let d := rectanglePrimalDualEdgeEquiv (0,0) (2*n+1) (2*n+1) E
  let b := rectanglePrimalEdgeBond (0,0) (2*n+1) (2*n+1) E
  have hface : v.val=b.faceBase false ∨ v.val=b.faceBase true := by
    change v ∈ s(rectangleDualEdgeSource (0,0) (2*n+1) (2*n+1) d,
      rectangleDualEdgeTarget (0,0) (2*n+1) (2*n+1) d) at hv
    rcases Sym2.mem_iff'.mp hv with hv | hv
    · exact Or.inl ((congrArg Subtype.val hv).trans (rectangleDualEdgeSource_faceBase _ _ _ d))
    · exact Or.inr ((congrArg Subtype.val hv).trans (rectangleDualEdgeTarget_faceBase _ _ _ d))
  have hpoint : u.val ∈ b.toSym2 := by
    have hm : u.val ∈ Sym2.map (fun v : PrefixAuxVertex n => v.val) E.val := by
      apply Sym2.mem_map.mpr
      refine ⟨prefixPaddingEmbedding n u,?_,rfl⟩
      change prefixPaddingEmbedding n u ∈ Sym2.map (prefixPaddingEmbedding n) e.val
      exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
    exact (rectanglePrimalEdgeBond_toSym2_public (0,0) (2*n+1) (2*n+1) E).symm ▸ hm
  have hincident : b.source=u.val ∨ b.target=u.val :=
    (Sym2.mem_iff'.mp hpoint).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  have hi := rayIndex_incident_face_eq_of_off_support L u.val huL b hincident v.val hface
  have hone : rayIndex u.val L=1 := hi.symm.trans hidx
  omega

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
