module

public import PottsContinuity.Thm3.Prop4.MarkedBoxFrontierTrace
public import PottsContinuity.Thm3.Prop4.TubeTraceHalfTurn

/-! # The actual upper trace as inverse half-turn transport of the lower trace -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section

/-- Read the concrete lower trace at the rotated exchanged marks and return
its vertices to the original sample. This is an inverse trace transport. -/
def markedUpperBoxTrace (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) : Finset (box n : Set LatticeVertex) :=
  (markedLowerBoxTrace n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
    (configurationIso (boxHalfTurnIso n) A)).map (boxHalfTurnIso n).symm.toEquiv.toEmbedding

/-- The rotated upper trace is exactly the lower trace at the rotated
exchanged marks, with no omitted sample or endpoint parity case. -/
theorem halfTurnBoxTrace_markedUpperBoxTrace (n : ℕ) (u v : (box n : Set LatticeVertex)) :
    halfTurnBoxTrace n (markedUpperBoxTrace n u v) =
      markedLowerBoxTrace n (boxHalfTurnIso n v) (boxHalfTurnIso n u) := by
  classical
  funext A
  ext z
  simp only [halfTurnBoxTrace,markedUpperBoxTrace,Equiv.apply_symm_apply,Finset.mem_map]
  constructor
  · rintro ⟨x,⟨y,hy,rfl⟩,hyz⟩
    have hyz' : y = z := ((boxHalfTurnIso n).apply_symm_apply y).symm.trans hyz
    exact hyz' ▸ hy
  · intro hz
    exact ⟨(boxHalfTurnIso n).symm z,⟨z,hz,rfl⟩,(boxHalfTurnIso n).apply_symm_apply z⟩

/-- All actual upper excursion fields are discharged after the exact
half-turn, using the same original-box trace transport as the induction. -/
theorem markedUpperBoxTrace_has_rotated_recorded_excursion_witnesses
    {n : ℕ} (hn : 1 ≤ n) (η : ℝ) (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ)) :
    HasRecordedExcursionWitnesses n η (boxHalfTurnIso n v).val (boxHalfTurnIso n u).val
      (boxHalfTurnIso n v).property (boxHalfTurnIso n u).property
      (boxTraceOnRectangle n (halfTurnBoxTrace n (markedUpperBoxTrace n u v))) := by
  rw [halfTurnBoxTrace_markedUpperBoxTrace]
  apply markedLowerBoxTrace_has_recorded_excursion_witnesses hn η
  · change -(v.val.1) = -(n : ℤ)
    rw [hv]
  · change -(u.val.1) = (n : ℤ)
    rw [hu,neg_neg]

end
end PottsContinuity.Thm3.Prop4
