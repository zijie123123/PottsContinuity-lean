module

public import PottsContinuity.PlanarTopology.DobrushinPrimalProjection

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.Medial FKC.FiniteFK

/-- The literal closed dual bonds of a domain configuration, on integer face bases.
Only bonds of the original domain graph are retained; no exterior cap is an edge. -/
def domainClosedDualGraph {δ : FKC.PositiveMesh} {D : Set ℂ}
    (C : Configuration (domainLatticeGraph δ D)) : SimpleGraph FKC.LatticeVertex where
  Adj u v := ∃ b : DomainBond δ D, b.toGraphEdge ∉ C ∧
    ((u = b.val.faceBase false ∧ v = b.val.faceBase true) ∨
     (u = b.val.faceBase true ∧ v = b.val.faceBase false))
  symm := ⟨by
    rintro u v ⟨b,hb,h | h⟩
    · exact ⟨b,hb,Or.inr ⟨h.2,h.1⟩⟩
    · exact ⟨b,hb,Or.inl ⟨h.2,h.1⟩⟩⟩
  loopless := ⟨by
    rintro u ⟨b,_,h | h⟩
    all_goals
      have hn := LatticePort.closedPair_faceBase_ne (⟨b.val,false,false⟩ : LatticePort)
      apply hn
    · exact h.2.symm.trans h.1
    · exact h.1.symm.trans h.2⟩

/-- A local port pairing stays in one dual face or follows the dual of its
actual closed original bond. -/
theorem domain_localPair_dual_reachable {δ : FKC.PositiveMesh} {D : Set ℂ}
    (C : Configuration (domainLatticeGraph δ D)) (p : DomainPort δ D) :
    (domainClosedDualGraph C).Reachable p.toLatticePort.faceBase
      (DomainPort.localPair C p).toLatticePort.faceBase := by
  classical
  by_cases hopen : p.bond.toGraphEdge ∈ C
  · rw [DomainPort.localPair_faceBase_of_open C p hopen]
  · have hs : DomainBond.isOpen C p.bond = false := by
      simp [DomainBond.isOpen,hopen]
    have hadj : (domainClosedDualGraph C).Adj
        (p.bond.val.faceBase false) (p.bond.val.faceBase true) :=
      ⟨p.bond,hopen,Or.inl ⟨rfl,rfl⟩⟩
    cases hp : p.side
    · simpa [DomainPort.localPair,hs,DomainPort.toLatticePort,LatticePort.faceBase,hp]
        using hadj.reachable
    · simpa [DomainPort.localPair,hs,DomainPort.toLatticePort,LatticePort.faceBase,hp]
        using hadj.symm.reachable

/-- Interior geometric pairing keeps its actual dual face. Exterior caps are
not included in this statement. -/
theorem dobrushin_geometry_faceBase_of_interior {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (p : P.RetainedPort δ a k)
    (hp : openLatticeCell δ p.val.toLatticePort.faceBase ⊆ P.domain δ) :
    (P.retainedGeometryPair δ a k p).val.toLatticePort.faceBase =
      p.val.toLatticePort.faceBase := by
  let ip : InteriorPort δ (P.domain δ) := ⟨p.val,hp⟩
  have he : P.retainedPortOfInterior δ a k ip = p := by
    apply Subtype.ext
    rfl
  rw [← he,P.retainedGeometryPair_interior,P.retainedPortOfInterior_val]
  exact ip.cornerPair_faceBase

/-- A Dobrushin graph edge whose geometric pairing is interior projects to
actual closed-dual connectivity, with no exterior jump. -/
theorem dobrushin_edge_dual_reachable_of_interior_geometry {m : ℕ}
    (P : FKC.LatticePolygon m) (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (C : Configuration (domainLatticeGraph δ (P.domain δ)))
    {x y : P.RetainedPort δ a k × Bool}
    (hxy : (P.dobrushinPortGraph δ a k C).Adj x y)
    (hgeo : x.2 = true → y.2 = true →
      openLatticeCell δ x.1.val.toLatticePort.faceBase ⊆ P.domain δ) :
    (domainClosedDualGraph (C ∪ P.forwardArcRemovedEdges δ a k)).Reachable
      x.1.val.toLatticePort.faceBase y.1.val.toLatticePort.faceBase := by
  change (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.2 = false ∧ y.2 = false ∧ P.retainedLocalPairEquiv δ a k C x.1 = y.1 ∧ x.1 ≠ y.1) ∨
    (x.2 = true ∧ y.2 = true ∧ P.retainedGeometryPairEquiv δ a k x.1 = y.1 ∧ x.1 ≠ y.1) at hxy
  rcases hxy with ⟨he,_⟩ | ⟨_,_,he,_⟩ | ⟨hx,hy,he,_⟩
  · rw [he]
  · rw [← he]
    exact domain_localPair_dual_reachable (C ∪ P.forwardArcRemovedEdges δ a k) x.1.val
  · rw [← he]
    change (domainClosedDualGraph _).Reachable _
      (P.retainedGeometryPair δ a k x.1).val.toLatticePort.faceBase
    rw [dobrushin_geometry_faceBase_of_interior P δ a k x.1 (hgeo hx hy)]

/-- A segment of the interface with only interior geometric steps yields an
actual closed-dual connection between its endpoint faces. -/
theorem dobrushin_walk_dual_reachable_of_interior_geometry {m : ℕ}
    (P : FKC.LatticePolygon m) (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (C : Configuration (domainLatticeGraph δ (P.domain δ)))
    {x y : P.RetainedPort δ a k × Bool}
    (w : (P.dobrushinPortGraph δ a k C).Walk x y)
    (hgeo : ∀ u v, s(u,v) ∈ w.edges → u.2 = true → v.2 = true →
      openLatticeCell δ u.1.val.toLatticePort.faceBase ⊆ P.domain δ) :
    (domainClosedDualGraph (C ∪ P.forwardArcRemovedEdges δ a k)).Reachable
      x.1.val.toLatticePort.faceBase y.1.val.toLatticePort.faceBase := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x z y h w ih =>
    have hhead := dobrushin_edge_dual_reachable_of_interior_geometry P δ a k C h
      (hgeo x z (by simp))
    have htail : ∀ u v, s(u,v) ∈ w.edges → u.2 = true → v.2 = true →
        openLatticeCell δ u.1.val.toLatticePort.faceBase ⊆ P.domain δ := by
      intro u v he
      exact hgeo u v (by simp [he])
    exact hhead.trans (ih htail)

end PottsContinuity.PlanarTopology
