module

public import PottsContinuity.Thm4Plane.SlitScreenEvent
public import PottsContinuity.FKC.FiniteFK.SlitScreenCrossingEvents
public import PottsContinuity.FKC.FiniteFK.SlitScreenActualClosedGraph
public import PottsContinuity.FKC.FiniteFK.SlitScreenDualEdgeClassification
public import PottsContinuity.PlanarTopology.RectangleIntersection

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC
open PottsContinuity.FKC.FiniteFK
open PottsContinuity.FKC.Medial
open PottsContinuity.PD.FK

noncomputable section

/-- The source connector event: a dual path in `R*` joins a point on a
bottom-to-top left-screen path to a point on a bottom-to-top right-screen path.
All three paths use actual closed primal edges in the finite slit graph. -/
def slitScreenConnectorEvent (m : ℕ) :
    Set (PottsContinuity.FKC.FiniteFK.Configuration
      (slitBoxGraph (16 * m))) :=
  {A | ∃ lb ∈ slitScreenBottomTerminals m (slitScreenLeftFaceBases m),
    ∃ lt ∈ slitScreenTopTerminals m (slitScreenLeftFaceBases m),
    ∃ pL : (slitScreenActualConfigurationClosedDualGraph m A
      (slitScreenLeftFaceBases m)).Walk lb lt,
    ∃ rb ∈ slitScreenBottomTerminals m (slitScreenRightFaceBases m),
    ∃ rt ∈ slitScreenTopTerminals m (slitScreenRightFaceBases m),
    ∃ pR : (slitScreenActualConfigurationClosedDualGraph m A
      (slitScreenRightFaceBases m)).Walk rb rt,
    ∃ u v, u ∈ pL.support ∧ v ∈ pR.support ∧
      (slitScreenActualConfigurationClosedDualGraph m A
        (slitScreenMiddleFaceBases m)).Reachable u v}

private theorem walk_support_pair_reachable
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) {u v : V}
    (hu : u ∈ p.support) (hv : v ∈ p.support) : G.Reachable u v := by
  induction p generalizing u v with
  | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu hv
      subst u
      subst v
      exact SimpleGraph.Reachable.rfl
  | @cons a b c hab tail ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hu hv
      rcases hu with hu | hu
      · subst u
        rcases hv with hv | hv
        · subst v
          exact SimpleGraph.Reachable.rfl
        · exact hab.reachable.trans (ih (by simp) hv)
      · rcases hv with hv | hv
        · subst v
          exact (ih hu (by simp)).trans hab.reachable.symm
        · exact ih hu hv

end
end PottsContinuity.Thm4Plane
