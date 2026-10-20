module

public import PottsContinuity.Thm3.Prop4.MarkedLowerDualReveal
public import PottsContinuity.Thm3.Prop4.RecordedConnectingFrontierTrace

/-! # The two-mark trace observed by the actual raw lower dual reveal -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PlanarTopology
noncomputable section
local instance markedExcursionTraceEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- Literal lattice labels on actual frontier walks joining the two marks,
computed from the actual lower-arc revealed set and open original states. -/
def markedLowerConnectingTrace (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h)) :
    Finset LatticeVertex :=
  (recordedConnectingFrontierTrace a w h (markedLowerDualReveal a w h u.val v.val A)
    (A ∩ markedLowerDualReveal a w h u.val v.val A)
    (rectangleLowerDualArc a w h u.val v.val) u v).image Subtype.val

/-- The concrete trace is observed on its actual complete raw-reveal fibres. -/
theorem markedLowerConnectingTrace_eq_of_same_observation (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A C : Configuration (rectangleGraph a w h))
    (hobs : RSW.stoppingObservationMap (markedLowerDualReveal a w h u.val v.val) A =
      RSW.stoppingObservationMap (markedLowerDualReveal a w h u.val v.val) C) :
    markedLowerConnectingTrace a w h u v A = markedLowerConnectingTrace a w h u v C := by
  exact congrArg (Finset.image (fun z : RectangleVertex a w h => z.val))
    (recordedConnectingFrontierTrace_eq_of_same_observation a w h
      (markedLowerDualReveal a w h u.val v.val) (rectangleLowerDualArc a w h u.val v.val) u v A C hobs)

/-- A nonempty concrete trace has an actual recorded-open prescribed walk
whose WHOLE mapped support equals that trace, including branches. -/
theorem markedLowerConnectingTrace_recorded_walk_of_nonempty (a : LatticeVertex) (w h : ℕ)
    (u v : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (htrace : (markedLowerConnectingTrace a w h u v A).Nonempty) :
    ∃ p : (openGraph (rectangleGraph a w h) (A ∩ markedLowerDualReveal a w h u.val v.val A)).Walk u v,
      markedLowerConnectingTrace a w h u v A = (p.support.map Subtype.val).toFinset := by
  classical
  obtain ⟨z,hz⟩ := htrace
  obtain ⟨x,hx,_⟩ := Finset.mem_image.mp hz
  obtain ⟨p,hp⟩ := recordedConnectingFrontierTrace_exists_recorded_walk a w h
    (markedLowerDualReveal a w h u.val v.val A) (A ∩ markedLowerDualReveal a w h u.val v.val A)
    (rectangleLowerDualArc a w h u.val v.val) u v ⟨x,hx⟩
  refine ⟨p,?_⟩
  change Finset.image Subtype.val _ = _
  rw [← hp]
  ext z
  simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]

/-- Every noninitial concrete trace vertex has a literal recorded sampled
closed-dual arm from the exact prescribed lower arc to a genuine star port. -/
theorem markedLowerConnectingTrace_vertex_lower_arm (a : LatticeVertex) (w h : ℕ)
    (u v z : RectangleVertex a w h) (A : Configuration (rectangleGraph a w h))
    (hz : z.val ∈ markedLowerConnectingTrace a w h u v A) (hne : z.val ≠ u.val) :
    ∃ f ∈ sampledStarFacePorts a w h z, ∃ s ∈ rectangleLowerDualArc a w h u.val v.val,
      Nonempty ((recordedSampledClosedDualGraph a w h (markedLowerDualReveal a w h u.val v.val A)
        (A ∩ markedLowerDualReveal a w h u.val v.val A)).Walk s f) := by
  obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hz
  have hxz' : x = z := Subtype.ext hxz
  subst x
  exact recordedConnectingFrontierTrace_vertex_has_lower_arm a w h _ _ _ u v z hx
    (fun hh => hne (congrArg Subtype.val hh))

end
end PottsContinuity.Thm3.Prop4
