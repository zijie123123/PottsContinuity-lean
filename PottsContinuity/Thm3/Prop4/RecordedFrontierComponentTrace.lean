module

public import PottsContinuity.Thm3.Prop4.FiniteComponentWalk
public import PottsContinuity.Thm3.RSW.StoppingAverage

/-!
# The canonical whole recorded-frontier component trace

The trace is defined by component membership, without choosing a path. An
actual walk covering precisely this trace exists whenever its target mark
belongs to the component. Branches and repeated visits are preserved.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
local instance recordedFrontierComponentVertexFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleVertex a w h) := Fintype.ofFinite _
local instance recordedFrontierComponentEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Every vertex in the component of the prescribed initial mark in the
original-edge frontier of the recorded closed-dual region. -/
def recordedFrontierComponentTrace (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    (u : RectangleVertex a w h) : Finset (RectangleVertex a w h) := by
  classical
  exact Finset.univ.filter fun z =>
    ActualConnected (rectangleGraph a w h) (recordedDualFaceFrontier a w h R B L) u z

/-- Component membership is exactly actual connection in the frontier graph. -/
theorem mem_recordedFrontierComponentTrace (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    (u z : RectangleVertex a w h) :
    z ∈ recordedFrontierComponentTrace a w h R B L u ↔
      ActualConnected (rectangleGraph a w h) (recordedDualFaceFrontier a w h R B L) u z := by
  classical
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ z))

/-- The canonical entire component is the support of an actual recorded OPEN
u-v walk, and every noninitial trace vertex has a recorded sampled dual arm
from the supplied seed faces to its genuine star port. -/
theorem recordedFrontierComponentTrace_exists_recorded_walk_and_arms
    (a : LatticeVertex) (w h : ℕ) (R B : Configuration (rectangleGraph a w h))
    (L : Set LatticeVertex) (u v : RectangleVertex a w h)
    (hconn : ActualConnected (rectangleGraph a w h) (recordedDualFaceFrontier a w h R B L) u v) :
    (∃ p : (openGraph (rectangleGraph a w h) B).Walk u v,
      p.support.toFinset = recordedFrontierComponentTrace a w h R B L u) ∧
    (∀ z ∈ recordedFrontierComponentTrace a w h R B L u, z ≠ u →
      ∃ f ∈ sampledStarFacePorts a w h z, ∃ s ∈ L,
        Nonempty ((recordedSampledClosedDualGraph a w h R B).Walk s f)) := by
  classical
  obtain ⟨p,hp⟩ := exists_walk_support_eq_finite_component
    (openGraph (rectangleGraph a w h) (recordedDualFaceFrontier a w h R B L)) u v hconn
  obtain ⟨q,hq⟩ := recorded_frontier_walk_open_in_record a w h R B L p
  refine ⟨⟨q,?_⟩,?_⟩
  · ext z
    rw [List.mem_toFinset,hq,hp,mem_recordedFrontierComponentTrace]
    rfl
  · intro z hz hne
    exact recorded_frontier_walk_vertex_has_lower_arm a w h R B L p z
      ((hp z).mpr ((mem_recordedFrontierComponentTrace a w h R B L u z).mp hz)) hne


/-- The whole component trace computed from the actual complete source record.
This defines a trace on every sample without selecting a particular path. -/
def recordedFrontierTraceOnSamples (a : LatticeVertex) (w h : ℕ)
    (reveal : Configuration (rectangleGraph a w h) → Configuration (rectangleGraph a w h))
    (L : Set LatticeVertex) (u : RectangleVertex a w h)
    (A : Configuration (rectangleGraph a w h)) : Finset (RectangleVertex a w h) :=
  recordedFrontierComponentTrace a w h (reveal A) (A ∩ reveal A) L u

/-- The whole frontier trace is observed on complete record fibres. No
stopping stability or observation representative is needed for this fact. -/
theorem recordedFrontierTraceOnSamples_eq_of_same_observation
    (a : LatticeVertex) (w h : ℕ)
    (reveal : Configuration (rectangleGraph a w h) → Configuration (rectangleGraph a w h))
    (L : Set LatticeVertex) (u : RectangleVertex a w h)
    (A C : Configuration (rectangleGraph a w h))
    (hobs : RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal C) :
    recordedFrontierTraceOnSamples a w h reveal L u A =
      recordedFrontierTraceOnSamples a w h reveal L u C := by
  have hR : reveal A = reveal C := congrArg Prod.fst (congrArg Subtype.val hobs)
  have hB : A ∩ reveal A = C ∩ reveal C := congrArg Prod.snd (congrArg Subtype.val hobs)
  change recordedFrontierComponentTrace a w h (reveal A) (A ∩ reveal A) L u =
    recordedFrontierComponentTrace a w h (reveal C) (C ∩ reveal C) L u
  rw [hB,hR]

end
end PottsContinuity.Thm3.Prop4
