module

public import PottsContinuity.PlanarTopology.DobrushinPrimalProjection
public import PottsContinuity.FKC.FiniteFK.Wiring

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.Medial FKC.FiniteFK

/-- Opening edges internal to a seed set does not enlarge the union of its
original actual open clusters. The witnessing seed may change. -/
theorem seed_connection_union_iff {V : Type*} {G : SimpleGraph V}
    [DecidableEq G.edgeSet] (C R : Configuration G) (A : Set V)
    (hR : ∀ u v (h : G.Adj u v),
      (⟨s(u,v), G.mem_edgeSet.mpr h⟩ : G.edgeSet) ∈ R → u ∈ A ∧ v ∈ A)
    (v : V) :
    (∃ u ∈ A, ActualConnected G (C ∪ R) u v) ↔
      ∃ u ∈ A, ActualConnected G C u v := by
  constructor
  · rintro ⟨u,hu,⟨p⟩⟩
    have hp : (∃ z ∈ A, ActualConnected G C z u) →
        ∃ z ∈ A, ActualConnected G C z v := by
      clear hu
      induction p with
      | nil => exact fun h => h
      | @cons x y t h p ih =>
        intro hx
        apply ih
        obtain ⟨e,he,hev⟩ := (openGraph_adj G (C ∪ R) x y).mp h
        rcases Finset.mem_union.mp he with heC | heR
        · obtain ⟨z,hz,hzx⟩ := hx
          exact ⟨z,hz,hzx.trans ((openGraph_adj G C x y).mpr ⟨e,heC,hev⟩).reachable⟩
        · have hG : G.Adj x y := openGraph_le G (C ∪ R) h
          have heq : e = ⟨s(x,y),G.mem_edgeSet.mpr hG⟩ := Subtype.ext hev
          have hy := (hR x y hG (heq ▸ heR)).2
          exact ⟨y,hy,SimpleGraph.Reachable.refl y⟩
    exact hp ⟨u,hu,SimpleGraph.Reachable.refl u⟩
  · rintro ⟨u,hu,h⟩
    exact ⟨u,hu,actualConnected_mono Finset.subset_union_left h⟩

/-- In the Dobrushin drawing, connectivity from the wired arc is still
connectivity from some actual vertex of that arc in the original configuration. -/
theorem forwardArc_seed_connection_union_iff {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (C : Configuration (domainLatticeGraph δ (P.domain δ)))
    (v : DomainVertex δ (P.domain δ)) :
    (∃ u ∈ P.forwardArcVertices δ a k,
      ActualConnected _ (C ∪ P.forwardArcRemovedEdges δ a k) u v) ↔
    ∃ u ∈ P.forwardArcVertices δ a k, ActualConnected _ C u v := by
  classical
  apply seed_connection_union_iff
  intro u v h he
  have hr := P.forwardArcRemovedEdges_related δ a k u v h he
  rcases hr with heq | hboth
  · exact (h.ne heq).elim
  · exact hboth

/-- Every primal endpoint of the unique interface belongs to an ORIGINAL
open cluster rooted on the selected wired arc, even though the drawing opens
its boundary edges. -/
theorem dobrushin_walk_original_seed_connection {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (a : ZMod (m+3)) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m+2)
    (C : Configuration (domainLatticeGraph δ (P.domain δ)))
    {t : P.RetainedPort δ a k × Bool}
    (w : (P.dobrushinPortGraph δ a k C).Walk (P.wiredStartPort δ a hk2,true) t)
    (z : P.RetainedPort δ a k × Bool) (hz : z ∈ w.support) :
    ∃ u ∈ P.forwardArcVertices δ a k,
      ActualConnected _ C u (domainPortPrimalVertex z.1.val) := by
  apply (forwardArc_seed_connection_union_iff P δ a k C _).mp
  refine ⟨P.boundaryVertex δ a, P.boundaryVertex_mem_forwardArc_start δ a hk1, ?_⟩
  have h := dobrushin_walk_primal_reachable P δ a k C w z hz
  have hs : domainPortPrimalVertex (P.wiredStartPort δ a hk2).val = P.boundaryVertex δ a := by
    apply Subtype.ext
    simp only [domainPortPrimalVertex_val, P.wiredStartPort_primalVertex, P.boundaryVertex_val]
  simpa only [hs] using h

end PottsContinuity.PlanarTopology
