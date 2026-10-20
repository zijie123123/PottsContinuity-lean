module

public import PottsContinuity.FKC.Domains.DobrushinInterface
public import PottsContinuity.FKC.Medial.PortEmbedding

/-! Actual primal connectivity beside the Dobrushin interface.
The drawing configuration is C union the explicitly removed wired-arc edges.
No virtual boundary relation is used as an actual open edge.
-/

@[expose] public section

namespace PottsContinuity.PlanarTopology
open FKC FKC.Medial FKC.FiniteFK

/-- The actual domain-graph vertex selected by a port's primal endpoint flag. -/
def domainPortPrimalVertex {δ : FKC.PositiveMesh} {D : Set ℂ}
    (p : DomainPort δ D) : DomainVertex δ D :=
  if p.tip then p.bond.target else p.bond.source

@[simp] theorem domainPortPrimalVertex_val {δ : FKC.PositiveMesh} {D : Set ℂ}
    (p : DomainPort δ D) :
    (domainPortPrimalVertex p).val = p.toLatticePort.primalVertex := by
  cases hp : p.tip <;>
    simp [domainPortPrimalVertex, hp, DomainPort.toLatticePort,
      LatticePort.primalVertex, LatticeBond.endpoint, DomainBond.source, DomainBond.target]

/-- A local medial pairing either stays at the primal endpoint or traverses
its actual open original bond. -/
theorem domain_localPair_primal_reachable {δ : FKC.PositiveMesh} {D : Set ℂ}
    (C : Configuration (domainLatticeGraph δ D)) (p : DomainPort δ D) :
    ActualConnected (domainLatticeGraph δ D) C
      (domainPortPrimalVertex p) (domainPortPrimalVertex (DomainPort.localPair C p)) := by
  classical
  by_cases hopen : p.bond.toGraphEdge ∈ C
  · have hs := (DomainBond.isOpen_eq_true C p.bond).mpr hopen
    have hadj : (openGraph (domainLatticeGraph δ D) C).Adj p.bond.source p.bond.target := by
      rw [openGraph_adj]
      exact ⟨p.bond.toGraphEdge, hopen, rfl⟩
    cases ht : p.tip
    · simpa [ActualConnected, domainPortPrimalVertex, DomainPort.localPair, hs, ht] using hadj.reachable
    · simpa [ActualConnected, domainPortPrimalVertex, DomainPort.localPair, hs, ht] using hadj.symm.reachable
  · have hs : DomainBond.isOpen C p.bond = false := by
      simp [DomainBond.isOpen, hopen]
    have he : domainPortPrimalVertex (DomainPort.localPair C p) =
        domainPortPrimalVertex p := by
      simp [domainPortPrimalVertex, DomainPort.localPair, hs]
    rw [he]
    exact SimpleGraph.Reachable.refl _

/-- A genuine geometric Dobrushin pairing preserves the domain primal vertex. -/
theorem dobrushin_geometry_primalVertex {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (p : P.RetainedPort δ a k) :
    domainPortPrimalVertex (P.retainedGeometryPair δ a k p).val =
      domainPortPrimalVertex p.val := by
  apply Subtype.ext
  simp only [domainPortPrimalVertex_val]
  exact P.retainedGeometryPair_primalVertex δ a k p

/-- Each edge of the actual two-layer Dobrushin graph projects to actual
primal connectivity in the drawing configuration. -/
theorem dobrushin_edge_primal_reachable {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (C : Configuration (domainLatticeGraph δ (P.domain δ)))
    {x y : P.RetainedPort δ a k × Bool}
    (hxy : (P.dobrushinPortGraph δ a k C).Adj x y) :
    ActualConnected (domainLatticeGraph δ (P.domain δ))
      (C ∪ P.forwardArcRemovedEdges δ a k)
      (domainPortPrimalVertex x.1.val) (domainPortPrimalVertex y.1.val) := by
  change (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.2 = false ∧ y.2 = false ∧ P.retainedLocalPairEquiv δ a k C x.1 = y.1 ∧ x.1 ≠ y.1) ∨
    (x.2 = true ∧ y.2 = true ∧ P.retainedGeometryPairEquiv δ a k x.1 = y.1 ∧ x.1 ≠ y.1) at hxy
  rcases hxy with ⟨he,_⟩ | ⟨_,_,he,_⟩ | ⟨_,_,he,_⟩
  · rw [he]
    exact SimpleGraph.Reachable.refl _
  · rw [← he]
    exact domain_localPair_primal_reachable (C ∪ P.forwardArcRemovedEdges δ a k) x.1.val
  · rw [← he]
    change ActualConnected _ _ _ (domainPortPrimalVertex (P.retainedGeometryPair δ a k x.1).val)
    rw [dobrushin_geometry_primalVertex]
    exact SimpleGraph.Reachable.refl _

/-- All original primal endpoints seen along a Dobrushin port walk lie in
one actual open component of the drawing configuration. -/
theorem dobrushin_walk_primal_reachable {m : ℕ} (P : FKC.LatticePolygon m)
    (δ : FKC.PositiveMesh) (a : ZMod (m+3)) (k : ℕ)
    (C : Configuration (domainLatticeGraph δ (P.domain δ)))
    {x y : P.RetainedPort δ a k × Bool}
    (w : (P.dobrushinPortGraph δ a k C).Walk x y) :
    ∀ z ∈ w.support, ActualConnected (domainLatticeGraph δ (P.domain δ))
      (C ∪ P.forwardArcRemovedEdges δ a k)
      (domainPortPrimalVertex x.1.val) (domainPortPrimalVertex z.1.val) := by
  induction w with
  | @nil x =>
    intro z hz
    have he : z = x := by simpa using hz
    subst z
    exact SimpleGraph.Reachable.refl _
  | @cons x y t h w ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact SimpleGraph.Reachable.refl _
    · exact (dobrushin_edge_primal_reachable P δ a k C h).trans (ih z hz)

end PottsContinuity.PlanarTopology
