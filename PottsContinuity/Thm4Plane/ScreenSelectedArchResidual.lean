module

public import PottsContinuity.Thm4Plane.ScreenArchCrossedCut

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK

private theorem screenActualDualWalk_support_mem_carrier
    (n : ℕ) (A : Configuration (slitBoxGraph n))
    (F : Finset LatticeVertex) {lb rb : LatticeVertex}
    (p : (generalScreenActualClosedDualGraph n A F).Walk lb rb)
    (hlb : lb ∈ F) :
    ∀ z ∈ p.support, z ∈ F := by
  induction p with
  | nil =>
      intro z hz
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
      rw [hz]
      exact hlb
  | @cons u v w hadj tail ih =>
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact hlb
      · have hv : v ∈ F := by
          rcases hadj with ⟨d, e, hcross, hclosed, hdir, huF, hvF⟩
          exact hvF
        exact ih hv z hz

/-- Event transfer for a fixed actual closed-dual walk. This keeps the walk
fixed while constructing its crossed-bond cut, the canonical cap component,
and the residual cap connection. It does not assert that the component avoids
the wired arc or that its conditional law is free; those are separate
planar-separation and DMP interfaces. -/
theorem generalEScreenEvent_fixedDualWalk_componentResidualConnection
    (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (slitBoxGraph (16 * m)))
    (hE : A ∈ generalEScreenEvent (16 * m))
    (lb rb : LatticeVertex)
    (hlb : lb ∈ generalScreenBottomTerminals (16 * m)
      (generalScreenLeftFaceBases (16 * m)))
    (p : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Walk lb rb) :
    (∀ e ∈ screenArchCrossedBondConfiguration m A p, e ∉ A) ∧
    (∀ e ∈ screenArchCrossedBondConfiguration m A p,
      ¬ screenTargetCapInternalEdge m e) ∧
    ∃ hcap : screenTargetCap m ⊆
      screenTargetCapEdgeDeletedComponent m
        (screenArchCrossedBondConfiguration m A p),
      (∀ u v : SlitBoxVertex (16 * m),
        u ∈ screenTargetCapEdgeDeletedComponent m
          (screenArchCrossedBondConfiguration m A p) →
        v ∉ screenTargetCapEdgeDeletedComponent m
          (screenArchCrossedBondConfiguration m A p) →
        (hAdj : (slitBoxGraph (16 * m)).Adj u v) →
        (⟨s(u, v), (slitBoxGraph (16 * m)).mem_edgeSet.mpr hAdj⟩ :
          (slitBoxGraph (16 * m)).edgeSet) ∈
            screenArchCrossedBondConfiguration m A p) ∧
      screenCapResidualConfiguration m
        (screenArchCrossedBondConfiguration m A p)
        (screenTargetCapEdgeDeletedComponent m
          (screenArchCrossedBondConfiguration m A p)) A ∈
        screenCapBoundaryConnectionEvent m
          (screenArchCrossedBondConfiguration m A p)
          (screenTargetCapEdgeDeletedComponent m
            (screenArchCrossedBondConfiguration m A p)) hcap := by
  have hlbCarrier : lb ∈ generalScreenArchFaceBases (16 * m) := by
    simp only [generalScreenArchFaceBases, Finset.mem_union]
    exact Or.inl (Or.inl hlb.1)
  have hsupport : ∀ z ∈ p.support,
      z ∈ generalScreenArchFaceBases (16 * m) :=
    screenActualDualWalk_support_mem_carrier (16 * m) A
      (generalScreenArchFaceBases (16 * m)) p hlbCarrier
  have hExterior : ∀ z ∈ p.support,
      2 * z.1 + 1 < -(2 * (m : ℤ)) ∨
        2 * (m : ℤ) < 2 * z.1 + 1 ∨
          -(30 * (m : ℤ)) < 2 * z.2 + 1 := by
    intro z hz
    exact generalScreenArchFaceCenters_outside_translatedTargetBox m hm z
      (hsupport z hz)
  let R := screenArchCrossedBondConfiguration m A p
  let D := screenTargetCapEdgeDeletedComponent m R
  have hclosed : ∀ e ∈ R, e ∉ A := by
    intro e he
    exact screenArchCrossedBondConfiguration_mem_closed m hm A p e he
  have havoid : ∀ e ∈ R, ¬ screenTargetCapInternalEdge m e := by
    exact screenArchCrossedBondConfiguration_avoids_capInternalEdge_of_exteriorSupport
      m A p hExterior
  have hcap : screenTargetCap m ⊆ D :=
    screenTargetCap_subset_edgeDeletedComponent_of_no_internal_removal
      m hm R havoid
  have hboundary : ∀ u v : SlitBoxVertex (16 * m),
      u ∈ D → v ∉ D →
      (hAdj : (slitBoxGraph (16 * m)).Adj u v) →
      (⟨s(u, v), (slitBoxGraph (16 * m)).mem_edgeSet.mpr hAdj⟩ :
        (slitBoxGraph (16 * m)).edgeSet) ∈ R := by
    intro u v hu hv hAdj
    exact screenTargetCapEdgeDeletedComponent_boundaryEdge_mem_removed
      m R u v hu hv hAdj
  have hResidual : screenCapResidualConfiguration m R D A ∈
      screenCapBoundaryConnectionEvent m R D hcap := by
    exact generalEScreenEvent_component_residualCapBoundaryConnection
      m hm R havoid A hE
  exact ⟨hclosed, havoid, hcap, hboundary, hResidual⟩

end PottsContinuity.Thm4Plane
