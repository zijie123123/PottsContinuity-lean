module

public import PottsContinuity.PlanarTopology.DobrushinDualProjection
public import PottsContinuity.PlanarTopology.BoundaryWalkClipping
public import PottsContinuity.PlanarTopology.SeedWiring

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.Medial FKC.FiniteFK

/-- Closing more primal bonds can only add literal dual bonds. -/
theorem domainClosedDualGraph_antitone {δ : FKC.PositiveMesh} {D : Set ℂ}
    {C E : Configuration (domainLatticeGraph δ D)} (h : C ⊆ E) :
    domainClosedDualGraph E ≤ domainClosedDualGraph C := by
  rintro u v ⟨b,hb,he⟩
  exact ⟨b,fun hc => hb (h hc),he⟩

/-- The geometric pairing preserves the distinction between interior and
exterior occurrences. This does not identify different exterior dual faces. -/
theorem dobrushin_geometry_not_interior {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (p : P.RetainedPort δ a k)
    (hp : ¬(openLatticeCell δ p.val.toLatticePort.faceBase ⊆ P.domain δ)) :
    ¬(openLatticeCell δ (P.retainedGeometryPair δ a k p).val.toLatticePort.faceBase
      ⊆ P.domain δ) := by
  intro hi
  have he := dobrushin_geometry_faceBase_of_interior P δ a k
    (P.retainedGeometryPair δ a k p) hi
  rw [P.retainedGeometryPair_involutive] at he
  apply hp
  rwa [he]

/-- Exterior endpoint version of the clipping lemma. The endpoint faces are
actual exterior cells beside the two prescribed primal boundary classes.
The geometric classification premise is explicit; this lemma is not itself a
four-arc crossing theorem. The conclusion uses the ORIGINAL closed-dual configuration. -/
theorem dobrushin_exterior_dual_connection_of_classification {m : ℕ}
    (P : FKC.LatticePolygon m) (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (C : Configuration (domainLatticeGraph δ (P.domain δ)))
    (L R : Set (DomainVertex δ (P.domain δ)))
    {s t : P.RetainedPort δ a k × Bool}
    (w : (P.dobrushinPortGraph δ a k C).Walk s t)
    (hs : domainPortPrimalVertex s.1.val ∈ L)
    (ht : domainPortPrimalVertex t.1.val ∈ R)
    (hsout : ¬(openLatticeCell δ s.1.val.toLatticePort.faceBase ⊆ P.domain δ))
    (htout : ¬(openLatticeCell δ t.1.val.toLatticePort.faceBase ⊆ P.domain δ))
    (hexterior : ∀ z ∈ w.support,
      ¬(openLatticeCell δ z.1.val.toLatticePort.faceBase ⊆ P.domain δ) →
        domainPortPrimalVertex z.1.val ∈ L ∨ domainPortPrimalVertex z.1.val ∈ R) :
    ∃ x ∈ w.support, ∃ y ∈ w.support,
      (¬(openLatticeCell δ x.1.val.toLatticePort.faceBase ⊆ P.domain δ)) ∧
      (¬(openLatticeCell δ y.1.val.toLatticePort.faceBase ⊆ P.domain δ)) ∧
      domainPortPrimalVertex x.1.val ∈ L ∧ domainPortPrimalVertex y.1.val ∈ R ∧
      (domainClosedDualGraph C).Reachable
        x.1.val.toLatticePort.faceBase y.1.val.toLatticePort.faceBase := by
  let BL : Set (P.RetainedPort δ a k × Bool) := {z |
    ¬(openLatticeCell δ z.1.val.toLatticePort.faceBase ⊆ P.domain δ) ∧
      domainPortPrimalVertex z.1.val ∈ L}
  let BR : Set (P.RetainedPort δ a k × Bool) := {z |
    ¬(openLatticeCell δ z.1.val.toLatticePort.faceBase ⊆ P.domain δ) ∧
      domainPortPrimalVertex z.1.val ∈ R}
  obtain ⟨x,hx,y,hy,q,hqw,hxonly,hyonly⟩ :=
    walk_subwalk_between_sets w BL BR ⟨hsout,hs⟩ ⟨htout,ht⟩
  have hgeo : ∀ u v, s(u,v) ∈ q.edges → u.2 = true → v.2 = true →
      openLatticeCell δ u.1.val.toLatticePort.faceBase ⊆ P.domain δ := by
    intro u v he hu hv
    by_contra hnot
    have huq := q.fst_mem_support_of_mem_edges he
    have hvq := q.snd_mem_support_of_mem_edges he
    have hadj := q.adj_of_mem_edges he
    have hpair : P.retainedGeometryPairEquiv δ a k u.1 = v.1 := by
      change (u.1 = v.1 ∧ u.2 ≠ v.2) ∨
        (u.2 = false ∧ v.2 = false ∧ P.retainedLocalPairEquiv δ a k C u.1 = v.1 ∧ u.1 ≠ v.1) ∨
        (u.2 = true ∧ v.2 = true ∧ P.retainedGeometryPairEquiv δ a k u.1 = v.1 ∧ u.1 ≠ v.1) at hadj
      rcases hadj with ⟨_,hne⟩ | ⟨huf,_,_,_⟩ | ⟨_,_,hp,_⟩
      · exact (hne (hu.trans hv.symm)).elim
      · rw [hu] at huf
        cases huf
      · exact hp
    have heq : domainPortPrimalVertex u.1.val = domainPortPrimalVertex v.1.val := by
      rw [← hpair]
      exact (dobrushin_geometry_primalVertex P δ a k u.1).symm
    have hvout : ¬(openLatticeCell δ v.1.val.toLatticePort.faceBase ⊆ P.domain δ) := by
      rw [← hpair]
      exact dobrushin_geometry_not_interior P δ a k u.1 hnot
    rcases hexterior u (hqw.support_subset huq) hnot with huL | huR
    · have hvL : domainPortPrimalVertex v.1.val ∈ L := by rwa [← heq]
      have hue := hxonly u huq ⟨hnot,huL⟩
      have hve := hxonly v hvq ⟨hvout,hvL⟩
      exact (q.adj_of_mem_edges he).ne (hue.trans hve.symm)
    · have hvR : domainPortPrimalVertex v.1.val ∈ R := by rwa [← heq]
      have hue := hyonly u huq ⟨hnot,huR⟩
      have hve := hyonly v hvq ⟨hvout,hvR⟩
      exact (q.adj_of_mem_edges he).ne (hue.trans hve.symm)
  refine ⟨x,hqw.support_subset q.start_mem_support,y,hqw.support_subset q.end_mem_support,
    hx.1,hy.1,hx.2,hy.2,?_⟩
  exact (dobrushin_walk_dual_reachable_of_interior_geometry P δ a k C q hgeo).mono
    (domainClosedDualGraph_antitone Finset.subset_union_left)

end PottsContinuity.PlanarTopology
