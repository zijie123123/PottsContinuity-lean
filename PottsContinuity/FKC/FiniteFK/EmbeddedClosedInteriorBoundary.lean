-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EmbeddedClosedInteriorBoundary.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import PottsContinuity.FKC.FiniteFK.IsolatedBoundaryComponents
public import PottsContinuity.FKC.FiniteFK.DomainMarkov
public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import PottsContinuity.FKC.FiniteFK.ConditionalEmbeddedLaw
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

private theorem removed_edge_endpoint_not_image_compl
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (_hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    ∀ ⦃e : H.edgeSet⦄, e ∈ K.val → ∀ ⦃w : W⦄, w ∈ e.1 →
      w ∉ f '' Bᶜ := by
  classical
  intro e he w hw himage
  rcases himage with ⟨x, hxB, hfx⟩
  have hnot : e.1 ∉ (G.map f).edgeSet :=
    (mem_subgraphRemovedEdges e).mp (K.property he)
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e.1
  have heval : e.1 = Sym2.mk a b := by simpa using hab.symm
  have habAdj : H.Adj a b := by
    apply H.mem_edgeSet.mp
    rw [← heval]
    exact e.2
  have hwAB : w = a ∨ w = b := by
    rw [heval] at hw
    exact (Sym2.mem_iff').mp hw
  rcases hwAB with hwa | hwb
  · have hxa : f x = a := hfx.trans hwa
    obtain ⟨z, hzb, hxz⟩ := hclosed hxB (by simpa [hxa] using habAdj)
    have hmapAdj : (G.map f).Adj (f x) (f z) :=
      (SimpleGraph.map_adj _ _ _ _).mpr ⟨x, z, hxz, rfl, rfl⟩
    have he' : e.1 = Sym2.mk (f x) (f z) := by
      calc
        e.1 = Sym2.mk a b := heval
        _ = Sym2.mk (f x) (f z) := by rw [← hxa, ← hzb]
    apply hnot
    rw [he']
    exact (G.map f).mem_edgeSet.mpr hmapAdj
  · have hxb : f x = b := hfx.trans hwb
    obtain ⟨z, hza, hxz⟩ := hclosed hxB (by simpa [hxb] using habAdj.symm)
    have hmapAdj : (G.map f).Adj (f x) (f z) :=
      (SimpleGraph.map_adj _ _ _ _).mpr ⟨x, z, hxz, rfl, rfl⟩
    have he' : e.1 = Sym2.mk (f x) (f z) := by
      calc
        e.1 = Sym2.mk a b := heval
        _ = Sym2.mk (f x) (f z) := by
          apply Sym2.eq_iff.mpr
          exact Or.inr ⟨hza.symm, hxb.symm⟩
    apply hnot
    rw [he']
    exact (G.map f).mem_edgeSet.mpr hmapAdj

/-- A frozen exterior configuration has no edge endpoint in the embedded
complement of the wired set, provided the ambient graph is closed there. -/
theorem isolatedExtensionPullback_frozenFree_partition_le_wired_of_closedInterior
    {V W : Type*} [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    (isolatedExtensionPullbackBoundary f
      (frozenBoundary (BoundaryCondition.free (∅ : Set W)) K.val)).partition ≤
        (BoundaryCondition.wired B).partition := by
  classical
  let ξ : BoundaryCondition W := BoundaryCondition.free (∅ : Set W)
  let D : Set W := (f '' Bᶜ)ᶜ
  have hcomp : componentSetoid H ξ K.val ≤
      (BoundaryCondition.wired (ξ.boundary ∪ D)).partition :=
    componentSetoid_le_wired_union_of_edge_endpoints ξ D K.val (by
      intro e he w hw
      exact removed_edge_endpoint_not_image_compl f hGH B hclosed K he hw)
  intro x y hxy
  have houter : (componentSetoid H ξ K.val).r (f x) (f y) :=
    (Setoid.comap_rel f (frozenBoundary ξ K.val).partition x y).mp hxy
  have hwired : (BoundaryCondition.wired D).partition.r (f x) (f y) := by
    simpa [ξ, D, BoundaryCondition.free] using hcomp houter
  rcases (BoundaryCondition.wired_rel D (f x) (f y)).mp hwired with heq | ⟨hxD, hyD⟩
  · exact (BoundaryCondition.wired_rel B x y).mpr (Or.inl (f.injective heq))
  · have hxB : x ∈ B := by
      by_contra hx
      apply hxD
      exact ⟨x, hx, rfl⟩
    have hyB : y ∈ B := by
      by_contra hy
      apply hyD
      exact ⟨y, hy, rfl⟩
    exact (BoundaryCondition.wired_rel B x y).mpr (Or.inr ⟨hxB, hyB⟩)

private theorem embeddedRestriction_openAdj_of_openAdj
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) (hGH : G.map f ≤ H) (A : Configuration H)
    {x y : V} (hxy : G.Adj x y)
    (hopen : (openGraph H A).Adj (f x) (f y)) :
    (openGraph G (embeddedConfigurationRestriction G H f hGH A)).Adj x y := by
  rw [openGraph_adj] at hopen ⊢
  rcases hopen with ⟨eH, heH, heval⟩
  let eG : G.edgeSet := ⟨Sym2.mk x y, G.mem_edgeSet.mpr hxy⟩
  have hval : (embeddedEdgeEmbedding G H f hGH eG).val = eH.val := by
    rw [embeddedEdgeEmbedding_coe]
    change Sym2.map f (Sym2.mk x y) = eH.val
    rw [Sym2.map_mk]
    exact heval.symm
  have he : embeddedEdgeEmbedding G H f hGH eG = eH := Subtype.ext hval
  exact ⟨eG, (mem_embeddedConfigurationRestriction G H f hGH A eG).mpr
    (he ▸ heH), rfl⟩

/-- A path leaving the embedded complement of the wired set must first reach
that set in the restricted embedded configuration. The path confinement is
derived one step at a time from the explicit neighbor-closure premise. -/
theorem embedded_openPath_restrict_hits_boundary_of_exterior
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V ↪ W) (hGH : G.map f ≤ H) (B : Set V)
    (hclosed : ∀ ⦃x : V⦄, x ∉ B → ∀ ⦃y : W⦄, H.Adj (f x) y →
      ∃ z : V, f z = y ∧ G.Adj x z)
    (x : V) (_hxB : x ∉ B) (v : W) (hv : v ∉ f '' Bᶜ)
    (A : Configuration H)
    (hpath : ActualConnected H A (f x) v) :
    ∃ y ∈ B, ActualConnected G (embeddedConfigurationRestriction G H f hGH A) x y := by
  classical
  let R : Configuration G := embeddedConfigurationRestriction G H f hGH A
  have hpath' : (openGraph H A).Reachable (f x) v := hpath
  rw [SimpleGraph.reachable_iff_reflTransGen] at hpath'
  let Lifted (z : W) : Prop :=
    (∃ y ∈ B, ActualConnected G R x y) ∨
    (∃ t : V, f t = z ∧ ActualConnected G R x t)
  have hlift : ∀ z : W,
      Relation.ReflTransGen (openGraph H A).Adj (f x) z → Lifted z := by
    intro z hwalk
    induction hwalk with
    | refl => exact Or.inr ⟨x, rfl, SimpleGraph.Reachable.refl _⟩
    | @tail y z hprefixOuter hadj ih =>
        rcases ih with hhit | ⟨t, hft, hprefix⟩
        · exact Or.inl hhit
        · by_cases htB : t ∈ B
          · exact Or.inl ⟨t, htB, hprefix⟩
          · have houter : (openGraph H A).Adj (f t) z := by
              simpa [hft] using hadj
            obtain ⟨s, hsz, hts⟩ := hclosed htB (openGraph_le H A houter)
            have houter' : (openGraph H A).Adj (f t) (f s) := by
              simpa [hsz] using houter
            have hinner : (openGraph G R).Adj t s := by
              dsimp [R]
              exact embeddedRestriction_openAdj_of_openAdj f hGH A hts houter'
            have hstep : ActualConnected G R t s := actualConnected_of_adj G R hinner
            exact Or.inr ⟨s, hsz, hprefix.trans hstep⟩
  rcases hlift v hpath' with hhit | ⟨t, htv, hprefix⟩
  · exact hhit
  · have htB : t ∈ B := by
      by_contra ht
      exact hv ⟨t, by simpa using ht, htv⟩
    exact ⟨t, htB, hprefix⟩

end
end PottsContinuity.FKC.FiniteFK
