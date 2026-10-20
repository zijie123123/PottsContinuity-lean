module

public import PottsContinuity.Thm4Plane.ScreenCapResidualConfiguration
public import PottsContinuity.Thm4Plane.ScreenCapFreeLaw
public import PottsContinuity.Thm4Plane.GeneralScreenArchResidualDomain
public import PottsContinuity.PD.FK.SubgraphComparison
public import PottsContinuity.FKC.FiniteFK.CrossingComponentRemoval
public import PottsContinuity.Exploration.FiniteStoppingSetDMP

@[expose] public section

namespace PottsContinuity.Thm4Plane

open PottsContinuity.FKC.FiniteFK

noncomputable section

local instance screenCapComplementFreeLawEdgeFintype
    (m : ℕ) : Fintype (slitBoxGraph (16 * m)).edgeSet := Fintype.ofFinite _
local instance screenCapComplementFreeLawEdgeDecidableEq
    (m : ℕ) : DecidableEq (slitBoxGraph (16 * m)).edgeSet := Classical.decEq _
local instance screenCapComplementFreeLawRemovedFintype
    (m : ℕ) (R : Configuration (slitBoxGraph (16 * m))) :
    Fintype (PottsContinuity.PD.FK.RemovedConfiguration
      (slitBoxGraph (16 * m)) R) := Fintype.ofFinite _
local instance screenCapComplementFreeLawDomainEdgeFintype
    (m : ℕ) (R : Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    Fintype (screenCapEdgeDeletedDomainGraph m R D).edgeSet := Fintype.ofFinite _
local instance screenCapComplementFreeLawMappedEdgeFintype
    {V W : Type*} [Finite V] [Finite W] {G : SimpleGraph V}
    {f : V ↪ W} : Fintype (G.map f).edgeSet := Fintype.ofFinite _

/-- The deleted cap component represented on the fixed full slit-box vertex
carrier; vertices outside the component are isolated. -/
def screenCapEdgeDeletedFullCarrierGraph (m : ℕ)
    (R : Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    SimpleGraph (SlitBoxVertex (16 * m)) :=
  (screenCapEdgeDeletedDomainGraph m R D).map
    (screenCapDomainVertexEmbeddingToSlitBox m D)

/-- The full-carrier component graph remains a subgraph of the slit box. -/
theorem screenCapEdgeDeletedFullCarrierGraph_le_slitBox (m : ℕ)
    (R : Configuration (slitBoxGraph (16 * m)))
    (D : Set (SlitBoxVertex (16 * m))) :
    screenCapEdgeDeletedFullCarrierGraph m R D ≤ slitBoxGraph (16 * m) :=
  screenCapEdgeDeletedDomainGraph_map_to_slitBox m R D

private theorem screenArchWalk_support_mem_archCarrier
    (m : ℕ) (A : Configuration (slitBoxGraph (16 * m)))
    {lb rb : PottsContinuity.FKC.LatticeVertex}
    (p : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Walk lb rb)
    (hlb : lb ∈ generalScreenArchFaceBases (16 * m)) :
    ∀ z ∈ p.support, z ∈ generalScreenArchFaceBases (16 * m) := by
  have hAdj : ∀ ⦃x y⦄,
      (generalScreenActualClosedDualGraph (16 * m) A
        (generalScreenArchFaceBases (16 * m))).Adj x y →
      x ∈ generalScreenArchFaceBases (16 * m) ∧
        y ∈ generalScreenArchFaceBases (16 * m) := by
    intro x y hxy
    rcases hxy with ⟨_, _, _, _, _, hx, hy⟩
    exact ⟨hx, hy⟩
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
      · exact (hAdj hadj).1
      · exact ih (hAdj hadj).2 z hz

/-- A walk in the full arch carrier with its left endpoint on the source
left-bottom terminal has its whole face-center support outside the target box. -/
theorem generalScreenArchWalk_support_outsideTargetBox
    (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (slitBoxGraph (16 * m)))
    {lb rb : PottsContinuity.FKC.LatticeVertex}
    (p : (generalScreenActualClosedDualGraph (16 * m) A
      (generalScreenArchFaceBases (16 * m))).Walk lb rb)
    (hlb : lb ∈ generalScreenBottomTerminals (16 * m)
      (generalScreenLeftFaceBases (16 * m))) :
    ∀ z ∈ p.support,
      2 * z.1 + 1 < -(2 * (m : ℤ)) ∨
        2 * (m : ℤ) < 2 * z.1 + 1 ∨
          -(30 * (m : ℤ)) < 2 * z.2 + 1 := by
  have hstart : lb ∈ generalScreenArchFaceBases (16 * m) := by
    simp only [generalScreenArchFaceBases, Finset.mem_union]
    exact Or.inl (Or.inl hlb.1)
  intro z hz
  exact generalScreenArchFaceCenters_outside_translatedTargetBox m hm z
    (screenArchWalk_support_mem_archCarrier m A p hstart z hz)

end
end PottsContinuity.Thm4Plane
