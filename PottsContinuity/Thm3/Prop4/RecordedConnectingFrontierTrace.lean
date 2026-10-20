module

public import PottsContinuity.Thm3.Prop4.RecordedFrontierComponentTrace

/-!
# The whole frontier trace connecting two prescribed marks

Intersecting the two actual components describes exactly the vertices that
can occur on a frontier walk between the marks. This definition applies to
every sample and uses no selected path or fallback component.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
local instance connectingFrontierVertexFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (RectangleVertex a w h) := Fintype.ofFinite _
local instance connectingFrontierEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Vertices of the frontier components of BOTH prescribed marks. -/
def recordedConnectingFrontierTrace (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    (u v : RectangleVertex a w h) : Finset (RectangleVertex a w h) :=
  recordedFrontierComponentTrace a w h R B L u ∩ recordedFrontierComponentTrace a w h R B L v

/-- Nonempty connecting trace is equivalent to an actual frontier connection. -/
theorem recordedConnectingFrontierTrace_nonempty_iff (a : LatticeVertex) (w h : ℕ)
    (R B : Configuration (rectangleGraph a w h)) (L : Set LatticeVertex)
    (u v : RectangleVertex a w h) :
    (recordedConnectingFrontierTrace a w h R B L u v).Nonempty ↔
      ActualConnected (rectangleGraph a w h) (recordedDualFaceFrontier a w h R B L) u v := by
  constructor
  · rintro ⟨z,hz⟩
    obtain ⟨hu,hv⟩ := Finset.mem_inter.mp hz
    exact ((mem_recordedFrontierComponentTrace a w h R B L u z).mp hu).trans
      ((mem_recordedFrontierComponentTrace a w h R B L v z).mp hv).symm
  · intro huv
    refine ⟨v,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
    · exact (mem_recordedFrontierComponentTrace a w h R B L u v).mpr huv
    · exact (mem_recordedFrontierComponentTrace a w h R B L v v).mpr ⟨.nil⟩

/-- On a frontier connection the connecting trace is the WHOLE initial
component, retaining all branches and repeated-visit possibilities. -/
theorem recordedConnectingFrontierTrace_eq_component_of_connected
    (a : LatticeVertex) (w h : ℕ) (R B : Configuration (rectangleGraph a w h))
    (L : Set LatticeVertex) (u v : RectangleVertex a w h)
    (huv : ActualConnected (rectangleGraph a w h) (recordedDualFaceFrontier a w h R B L) u v) :
    recordedConnectingFrontierTrace a w h R B L u v = recordedFrontierComponentTrace a w h R B L u := by
  ext z
  constructor
  · exact fun hz => (Finset.mem_inter.mp hz).1
  · intro hz
    refine Finset.mem_inter.mpr ⟨hz,?_⟩
    apply (mem_recordedFrontierComponentTrace a w h R B L v z).mpr
    exact huv.symm.trans ((mem_recordedFrontierComponentTrace a w h R B L u z).mp hz)

/-- Any nonempty connecting trace has its exact recorded-open u-v walk
witness. The trace's nonemptiness itself supplies frontier connectivity. -/
theorem recordedConnectingFrontierTrace_exists_recorded_walk
    (a : LatticeVertex) (w h : ℕ) (R B : Configuration (rectangleGraph a w h))
    (L : Set LatticeVertex) (u v : RectangleVertex a w h)
    (htrace : (recordedConnectingFrontierTrace a w h R B L u v).Nonempty) :
    ∃ p : (openGraph (rectangleGraph a w h) B).Walk u v,
      p.support.toFinset = recordedConnectingFrontierTrace a w h R B L u v := by
  have hconn := (recordedConnectingFrontierTrace_nonempty_iff a w h R B L u v).mp htrace
  obtain ⟨⟨p,hp⟩,_⟩ := recordedFrontierComponentTrace_exists_recorded_walk_and_arms a w h R B L u v hconn
  exact ⟨p,hp.trans (recordedConnectingFrontierTrace_eq_component_of_connected a w h R B L u v hconn).symm⟩

/-- Every noninitial vertex of a connecting trace has an actual recorded
sampled-dual arm from L to a genuine star port, on its SAME source record. -/
theorem recordedConnectingFrontierTrace_vertex_has_lower_arm
    (a : LatticeVertex) (w h : ℕ) (R B : Configuration (rectangleGraph a w h))
    (L : Set LatticeVertex) (u v z : RectangleVertex a w h)
    (hz : z ∈ recordedConnectingFrontierTrace a w h R B L u v) (hne : z ≠ u) :
    ∃ f ∈ sampledStarFacePorts a w h z, ∃ s ∈ L,
      Nonempty ((recordedSampledClosedDualGraph a w h R B).Walk s f) := by
  have hconn := (recordedConnectingFrontierTrace_nonempty_iff a w h R B L u v).mp ⟨z,hz⟩
  exact (recordedFrontierComponentTrace_exists_recorded_walk_and_arms a w h R B L u v hconn).2
    z (Finset.mem_inter.mp hz).1 hne

/-- The two-mark connecting trace is computed from the complete attained
observation and therefore is observed without a representative choice. -/
theorem recordedConnectingFrontierTrace_eq_of_same_observation
    (a : LatticeVertex) (w h : ℕ)
    (reveal : Configuration (rectangleGraph a w h) → Configuration (rectangleGraph a w h))
    (L : Set LatticeVertex) (u v : RectangleVertex a w h)
    (A C : Configuration (rectangleGraph a w h))
    (hobs : RSW.stoppingObservationMap reveal A = RSW.stoppingObservationMap reveal C) :
    recordedConnectingFrontierTrace a w h (reveal A) (A ∩ reveal A) L u v =
      recordedConnectingFrontierTrace a w h (reveal C) (C ∩ reveal C) L u v := by
  have hu := recordedFrontierTraceOnSamples_eq_of_same_observation a w h reveal L u A C hobs
  have hv := recordedFrontierTraceOnSamples_eq_of_same_observation a w h reveal L v A C hobs
  exact congrArg₂ (fun x y : Finset (RectangleVertex a w h) => x ∩ y) hu hv

end
end PottsContinuity.Thm3.Prop4
