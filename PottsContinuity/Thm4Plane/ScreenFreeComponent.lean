module

public import PottsContinuity.Thm4Plane.ScreenSelectedArchResidual
public import PottsContinuity.Thm4Plane.ScreenTargetCapPlaneEvent
public import PottsContinuity.Thm4Plane.ScreenTargetCapComponent
public import PottsContinuity.PlanarTopology.SlitScreenCrosscut
public import PottsContinuity.PD.FK.EdgeRestriction
public import PottsContinuity.FKC.FiniteFK.DomainMarkov

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK

private theorem screenCap_open_adj_le_edgeRestriction_of_closedCut
    (m : ℕ) (A R : Configuration (slitBoxGraph (16 * m)))
    (hclosed : ∀ e ∈ R, e ∉ A)
    {u v : SlitBoxVertex (16 * m)}
    (hOpen : (openGraph (slitBoxGraph (16 * m)) A).Adj u v) :
    (edgeRestriction (slitBoxGraph (16 * m)) R).Adj u v := by
  let G := slitBoxGraph (16 * m)
  let H := edgeRestriction G R
  rcases (openGraph_adj_iff_openBond G A u v).mp hOpen with ⟨hG, heA⟩
  let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr hG⟩
  have heR : e ∉ R := by
    intro he
    exact hclosed e he heA
  have hHedge : s(u, v) ∈ H.edgeSet := by
    rw [edgeRestriction_edgeSet]
    refine ⟨G.mem_edgeSet.mpr hG, ?_⟩
    intro hopen
    exact heR ((coe_mem_openEdges_iff G R e).mp hopen)
  exact H.mem_edgeSet.mpr hHedge

/-- Given the crossed-path separation of the wired arc, the source sample has
no actual open connection from the retained target cap to that arc. The cut
edges are closed, so every open path stays in the edge-deleted component. -/
theorem screenTargetCap_openConnectionToWiredArc_false_of_crosscut
    (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (slitBoxGraph (16 * m)))
    (hE : A ∈ generalEScreenEvent (16 * m))
    (lb rb : LatticeVertex)
    (hlb : lb ∈ generalScreenBottomTerminals (16 * m)
      (generalScreenLeftFaceBases (16 * m)))
    (hrb : rb ∈ generalScreenBottomTerminals (16 * m)
      (generalScreenRightFaceBases (16 * m)))
    (p : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Walk lb rb)
    (hp : p.IsPath)
    (hcrosscut : ∀ (_hp : p.IsPath)
      (_hrb : rb ∈ generalScreenBottomTerminals (16 * m)
        (generalScreenRightFaceBases (16 * m))),
      ∀ v ∈ slitBoxWiredArc (16 * m),
        v ∉ screenTargetCapEdgeDeletedComponent m
          (screenArchCrossedBondConfiguration m A p)) :
    ∀ u ∈ screenTargetCap m, ∀ v ∈ slitBoxWiredArc (16 * m),
      ¬ ActualConnected (slitBoxGraph (16 * m)) A u v := by
  have hdata := generalEScreenEvent_fixedDualWalk_componentResidualConnection
    m hm A hE lb rb hlb p
  rcases hdata with ⟨hclosed, _havoid, ⟨hcap, _hboundary, _hResidual⟩⟩
  intro u hu v hv hconn
  let R := screenArchCrossedBondConfiguration m A p
  let H := edgeRestriction (slitBoxGraph (16 * m)) R
  have huD : u ∈ screenTargetCapEdgeDeletedComponent m R := hcap hu
  obtain ⟨w⟩ := (actualConnected_iff_walk (slitBoxGraph (16 * m)) A u v).mp hconn
  have hEdges : ∀ e ∈ w.edges, e ∈ H.edgeSet := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hAdj := w.adj_of_mem_edges he
        exact H.mem_edgeSet.mp
          (screenCap_open_adj_le_edgeRestriction_of_closedCut m A R hclosed hAdj)
  have hwalk : H.Reachable u v := w.transfer H hEdges |>.reachable
  have hvD : v ∈ screenTargetCapEdgeDeletedComponent m R := by
    change H.Reachable (slitBoxBottomCenterVertex (16 * m)) v
    change H.Reachable (slitBoxBottomCenterVertex (16 * m)) u at huD
    exact huD.trans hwalk
  exact hcrosscut hp hrb v hv hvD

end PottsContinuity.Thm4Plane
