module

public import PottsContinuity.Thm3.Prop4.MarkedLowerExcursionWitnesses
public import PottsContinuity.Thm3.Prop4.BoxTraceExcursionTransport

/-! # The concrete marked lower trace on the frozen original-box carrier -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite PlanarTopology
noncomputable section
local instance markedBoxFrontierSourceEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

local instance markedBoxFrontierTargetEdgeEq (n : ℕ) :
    DecidableEq (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet := Classical.decEq _

/-- The actual marked connecting trace pulled back to original box vertices. -/
def markedLowerBoxTrace (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) : Finset (box n : Set LatticeVertex) :=
  (recordedConnectingFrontierTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
    (markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val
      (configurationIso (boxTubeRectangleIso n) A))
    (configurationIso (boxTubeRectangleIso n) A ∩
      markedLowerDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val
        (configurationIso (boxTubeRectangleIso n) A))
    (rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val)
    (boxTubeRectangleIso n u) (boxTubeRectangleIso n v)).map
      (boxTubeRectangleIso n).symm.toEquiv.toEmbedding

/-- The coordinate-identical inverse box map keeps every literal vertex label. -/
theorem boxTubeRectangleIso_symm_val (n : ℕ)
    (z : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) :
    ((boxTubeRectangleIso n).symm z).val = z.val := by
  have h := congrArg Subtype.val ((boxTubeRectangleIso n).apply_symm_apply z)
  simpa only [boxTubeRectangleIso_val] using h

/-- The box trace transports EXACTLY to the concrete lower trace already
proved to have all recorded excursion fields. -/
theorem boxTraceOnRectangle_markedLowerBoxTrace (n : ℕ) (u v : (box n : Set LatticeVertex)) :
    boxTraceOnRectangle n (markedLowerBoxTrace n u v) =
      markedLowerConnectingTrace (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (boxTubeRectangleIso n u) (boxTubeRectangleIso n v) := by
  classical
  funext A
  ext z
  simp only [boxTraceOnRectangle,markedLowerBoxTrace,Equiv.apply_symm_apply,
    markedLowerConnectingTrace,boxTubeRectangleIso_val,Finset.mem_image,Finset.mem_map]
  constructor
  · rintro ⟨y,⟨x,hx,rfl⟩,hxz⟩
    exact ⟨x,hx,(boxTubeRectangleIso_symm_val n x).symm.trans hxz⟩
  · rintro ⟨x,hx,hxz⟩
    exact ⟨(boxTubeRectangleIso n).symm x,⟨x,hx,rfl⟩,(boxTubeRectangleIso_symm_val n x).trans hxz⟩

/-- All actual lower excursion fields on the original box, with NO source
record or planar converse hypothesis. -/
theorem markedLowerBoxTrace_has_recorded_excursion_witnesses
    {n : ℕ} (hn : 1 ≤ n) (η : ℝ) (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ)) :
    HasRecordedExcursionWitnesses n η u.val v.val u.property v.property
      (boxTraceOnRectangle n (markedLowerBoxTrace n u v)) := by
  rw [boxTraceOnRectangle_markedLowerBoxTrace]
  exact markedLowerConnectingTrace_has_recorded_excursion_witnesses hn η
    (boxTubeRectangleIso n u) (boxTubeRectangleIso n v) hu hv u.property v.property

end
end PottsContinuity.Thm3.Prop4
