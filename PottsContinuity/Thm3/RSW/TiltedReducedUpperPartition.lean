module

public import PottsContinuity.Thm3.RSW.TiltedReducedLowerEdges
public import PottsContinuity.Thm3.RSW.TiltedReducedBackground
public import PottsContinuity.PD.FK.EmbeddedClosedInteriorOuterBoundary

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial PD.Duality DualityExt Thm3.Prop4
noncomputable section

private theorem crossed_endpoint_source_box (N L M : ℕ) (t : ℝ) (hM : L+N+3 ≤ M)
    (b : LatticeBond) (z : LatticeVertex) (hz : z ∈ box L)
    (hmem : z ∈ (tiltedStripReducedCrossedBond N t b).toSym2) :
    b.source ∈ box M ∧ b.target ∈ box M := by
  have hb := (Foundations.mem_box_iff_abs_le L z).mp hz
  rw [Foundations.mem_box_iff_abs_le,Foundations.mem_box_iff_abs_le]
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> by_cases hp : 0<t
  all_goals
    simp only [tiltedStripReducedCrossedBond,hp,ite_true,ite_false,LatticeBond.toSym2,
      LatticeBond.source,LatticeBond.target] at hmem
    simp only [LatticeBond.source,LatticeBond.target,abs_le] at hb ⊢
    rcases (Sym2.mem_iff').mp hmem with he | he
    all_goals have hx := congrArg Prod.fst he
    all_goals have hy := congrArg Prod.snd he
    all_goals dsimp only at hx hy
    all_goals omega

private theorem host_bond_pair (N M : ℕ) (e : (tiltedReducedHost N M).edgeSet) :
    (rectanglePrimalEdgeBond (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) e).toSym2 =
      Sym2.map Subtype.val e.val := by
  exact congrArg Subtype.val (wholePlaneBondEdgeEquiv.apply_symm_apply
    (rectanglePrimalEdgeToSquareEdge (-(M:ℤ),-((M+N+2:ℕ):ℤ))
      (2*M) (2*(M+N+2)) e))

private theorem retained_host_edge_sampled (N M : ℕ) (t : ℝ)
    (e : (tiltedReducedHost N M).edgeSet)
    (hb : let b := rectanglePrimalEdgeBond (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) e;
      b.source ∈ tiltedStripVertices N t ∧ b.target ∈ tiltedStripVertices N t ∧
        ¬ (tiltedTop N t b.source ∧ tiltedTop N t b.target))
    (hbox : let b := rectanglePrimalEdgeBond (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) e;
      b.source ∈ box M ∧ b.target ∈ box M) :
    e.val ∈ ((tiltedWindowReducedGraph N M t).map (tiltedReducedHostEmbedding N M t)).edgeSet := by
  classical
  let b := rectanglePrimalEdgeBond (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) e
  let u : (tiltedWindow N M t : Set LatticeVertex) :=
    ⟨b.source,(mem_tiltedWindow N M t _).mpr ⟨hbox.1,hb.1⟩⟩
  let v : (tiltedWindow N M t : Set LatticeVertex) :=
    ⟨b.target,(mem_tiltedWindow N M t _).mpr ⟨hbox.2,hb.2.1⟩⟩
  let G := squareLattice.induce (tiltedWindow N M t : Set LatticeVertex)
  have hadj : (tiltedWindowReducedGraph N M t).Adj u v := by
    change s(u,v) ∈ (edgeRestriction G (tiltedWindowTopTopEdges N M t)).edgeSet
    rw [edgeRestriction_edgeSet]
    refine ⟨b.adjacent,?_⟩
    rintro ⟨g,hg,hgpair⟩
    have htop : ∀ z ∈ g.val, tiltedTop N t z.val := by
      simpa only [tiltedWindowTopTopEdges,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_coe] using hg
    exact hb.2.2 ⟨htop u (by rw [hgpair]; simp),htop v (by rw [hgpair]; simp)⟩
  have hp : e.val = s(tiltedReducedHostEmbedding N M t u,tiltedReducedHostEmbedding N M t v) := by
    apply Sym2.map.injective Subtype.val_injective
    exact (host_bond_pair N M e).symm
  rw [hp]
  exact (SimpleGraph.map_adj _ _ _ _).mpr ⟨u,v,hadj,rfl,rfl⟩

/-- Forced-open dual edges avoid every reflected non-top core vertex. -/
theorem tiltedReducedForcedDual_avoids_core
    (N L M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hM : L+N+3 ≤ M)
    (x : (tiltedWindow N L t : Set LatticeVertex)) (hx : ¬ tiltedTop N t x.val)
    (d : (rectangleDualGraph (-(M:ℤ),-((M+N+2:ℕ):ℤ))
      (2*M) (2*(M+N+2))).edgeSet)
    (hd : d ∈ (rectangleSubgraphDualOpenRemovedState (tiltedReducedHost_map_le N M t)
      (tiltedReducedHostRemovedState N M t ht)).val) :
    tiltedReducedCoreDualEmbedding N L M t hM x ∉ d.val := by
  classical
  intro hxm
  let g := (rectangleDualEdgeEquiv (-(M:ℤ),-((M+N+2:ℕ):ℤ))
    (2*M) (2*(M+N+2))).symm d
  let b := rectanglePrimalEdgeBond (-(M:ℤ),-((M+N+2:ℕ):ℤ))
    (2*M) (2*(M+N+2)) g
  have hdata : g ∈ subgraphRemovedEdges ((tiltedWindowReducedGraph N M t).map
      (tiltedReducedHostEmbedding N M t)) (tiltedReducedHost N M) ∧
      g ∉ (tiltedReducedHostRemovedState N M t ht).val := by
    simpa only [rectangleSubgraphDualOpenRemovedState,rectangleSubgraphRemovedDualEdges,
      Finset.mem_sdiff,Finset.mem_map_equiv] using hd
  have hpair : b.toSym2 = Sym2.map Subtype.val g.val := host_bond_pair N M g
  have hnotupper : ¬ tiltedReducedUpperBond N t b := by
    intro hb
    apply hdata.2
    simp only [tiltedReducedHostRemovedState,tiltedUpperCorridorState,
      Finset.mem_filter,Finset.mem_univ,true_and]
    intro z hz
    have hz' : z.val ∈ b.toSym2 := hpair.symm ▸ Sym2.mem_map.mpr ⟨z,hz,rfl⟩
    rcases (Sym2.mem_iff').mp hz' with he | he
    · exact he ▸ hb.1
    · exact he ▸ hb.2
  have hdPair : Sym2.map (fun z => tiltedStripReducedDualVertex N t z.val) d.val =
      (tiltedStripReducedCrossedBond N t b).toSym2 := by
    have hp := rectangleSubgraphDualEdgeEmbedding_crossingBond
      (G := tiltedReducedHost N M) le_rfl g
    change Sym2.map Subtype.val
      (rectangleDualEdgeEquiv (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2)) g).val =
        (dualBondOfPrimal b).toSym2 at hp
    have hp' : Sym2.map Subtype.val d.val = (dualBondOfPrimal b).toSym2 := by
      simpa only [g,Equiv.apply_symm_apply] using hp
    change Sym2.map ((tiltedStripReducedDualVertex N t) ∘ Subtype.val) d.val = _
    rw [← Sym2.map_map,hp']
    exact tiltedStripReducedDualBond_dualBondOfPrimal_pair N t b
  have hxpair : x.val ∈ (tiltedStripReducedCrossedBond N t b).toSym2 := by
    rw [← hdPair]
    exact Sym2.mem_map.mpr ⟨_,hxm,tiltedReducedCoreDualEmbedding_replay N L M t hM x⟩
  have hret : b.source ∈ tiltedStripVertices N t ∧ b.target ∈ tiltedStripVertices N t ∧
      ¬ (tiltedTop N t b.source ∧ tiltedTop N t b.target) := by
    by_contra hout
    have hc := tiltedReducedUpperBond_crossed_complement N hN t ht b hout
    have hdual : tiltedReducedUpperBond N t (tiltedStripReducedCrossedBond N t b) := by
      by_contra hd
      exact hnotupper (hc.mpr hd)
    have hxtop : (N:ℝ) < tiltedHeight t x.val+1 := by
      rcases (Sym2.mem_iff').mp hxpair with he | he
      · exact he ▸ hdual.1
      · exact he ▸ hdual.2
    exact hx ((tiltedTop_iff_height N ht x.val).mpr hxtop)
  have hbox := crossed_endpoint_source_box N L M t hM b x.val
    ((mem_tiltedWindow N L t x.val).mp x.property).1 hxpair
  exact ((mem_subgraphRemovedEdges g).mp hdata.1)
    (retained_host_edge_sampled N M t g hret hbox)

/-- The region supporting the finite induced partition, excluding precisely
reflected non-top vertices of the bounded core. -/
def tiltedReducedCoreSafeBoundarySet (N L M : ℕ) (t : ℝ) (hM : L+N+3 ≤ M) :
    Set (RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2))) :=
  (tiltedReducedCoreDualEmbedding N L M t hM '' {x | ¬ tiltedTop N t x.val})ᶜ

/-- The actual finite induced dual partition identifies only safe vertices. -/
theorem tiltedReducedFiniteDualBoundary_partition_le_safe
    (N L M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hM : L+N+3 ≤ M) :
    (tiltedReducedFiniteDualBoundary N M t ht).partition ≤
      (BoundaryCondition.wired (tiltedReducedCoreSafeBoundarySet N L M t hM)).partition := by
  let D := tiltedReducedCoreSafeBoundarySet N L M t hM
  let ξ := rectangleDualBoundaryCondition (-(M:ℤ),-((M+N+2:ℕ):ℤ)) (2*M) (2*(M+N+2))
  have hsub : ξ.boundary ⊆ D := by
    intro u hu himage
    obtain ⟨x,hx,hxu⟩ := himage
    have hi := tiltedReducedCoreDualEmbedding_interior N L M t hM x
    have hb : u.val ∈ rectangleDualBoundary (-(M:ℤ),-((M+N+2:ℕ):ℤ))
        (2*M) (2*(M+N+2)) := hu
    rw [rectangleDualBoundary,Finset.mem_filter] at hb
    exact hb.2 (hxu ▸ hi)
  have hA : ∀ ⦃e⦄, e ∈ (rectangleSubgraphDualOpenRemovedState (tiltedReducedHost_map_le N M t)
      (tiltedReducedHostRemovedState N M t ht)).val → ∀ ⦃u⦄, u ∈ e.val → u ∈ D := by
    intro e he u hu himage
    obtain ⟨x,hx,hxu⟩ := himage
    exact tiltedReducedForcedDual_avoids_core N L M hN t ht hM x hx e he (hxu ▸ hu)
  have hcomp := componentSetoid_le_wired_union_of_edge_endpoints ξ D
    (rectangleSubgraphDualOpenRemovedState (tiltedReducedHost_map_le N M t)
      (tiltedReducedHostRemovedState N M t ht)).val hA
  have hunion : ξ.boundary ∪ D = D := Set.union_eq_right.mpr hsub
  rw [hunion] at hcomp
  exact hcomp

/-- The same induced partition with its proved support, rather than the
all-vertex support used by the generic frozen-boundary descriptor. -/
def tiltedReducedSupportedDualBoundary
    (N L M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hM : L+N+3 ≤ M) :
    BoundaryCondition (RectangleDualVertex (-(M:ℤ),-((M+N+2:ℕ):ℤ))
      (2*M) (2*(M+N+2))) where
  boundary := tiltedReducedCoreSafeBoundarySet N L M t hM
  partition := (tiltedReducedFiniteDualBoundary N M t ht).partition
  supported := fun h => tiltedReducedFiniteDualBoundary_partition_le_safe N L M hN t ht hM h

/-- No reflected non-top core point belongs to this proved boundary support. -/
theorem tiltedReducedSupportedDualBoundary_avoids_core
    (N L M : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hM : L+N+3 ≤ M) (x : (tiltedWindow N L t : Set LatticeVertex))
    (hx : ¬ tiltedTop N t x.val) :
    tiltedReducedCoreDualEmbedding N L M t hM x ∉
      (tiltedReducedSupportedDualBoundary N L M hN t ht hM).boundary := by
  intro h
  exact h ⟨x,hx,rfl⟩

end
end PottsContinuity.RSW
