module

public import PottsContinuity.Thm3.Prop4.MarkedUpperBoxTrace
public import PottsContinuity.Thm3.Prop4.TraceAccessHalfTurn

/-! # Exact upper trace labels for the lower-access half-turn bridge -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section

/-- The negated original upper trace labels are exactly the actual lower
trace labels on the rotated sample at exchanged marks. -/
theorem markedUpperBoxTrace_negated_labels (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) :
    ((markedUpperBoxTrace n u v A).image Subtype.val).image (fun z => -z) =
      (markedLowerBoxTrace n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
        (configurationIso (boxHalfTurnIso n) A)).image Subtype.val := by
  classical
  ext z
  simp only [markedUpperBoxTrace,Finset.mem_image,Finset.mem_map]
  constructor
  · rintro ⟨w,⟨x,⟨y,hy,rfl⟩,rfl⟩,hz⟩
    exact ⟨y,hy,(by change -(-y.val) = z at hz; simpa only [neg_neg] using hz)⟩
  · rintro ⟨y,hy,hyz⟩
    refine ⟨-y.val,⟨(boxHalfTurnIso n).symm y,⟨y,hy,rfl⟩,rfl⟩,?_⟩
    simpa only [neg_neg] using hyz

/-- Actual absence of top access on the rotated lower trace gives absence
of bottom access on the exact original upper trace, without a fitted selector. -/
theorem markedUpperBoxTrace_no_bottom_access_of_rotated_lower
    (n : ℕ) (u v : (box n : Set LatticeVertex))
    (A : Configuration (finiteLatticeGraph (box n))) (z : LatticeVertex)
    (hno : ¬traceTopAccessible n
      ((markedLowerBoxTrace n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
        (configurationIso (boxHalfTurnIso n) A)).image Subtype.val) (-z)) :
    ¬traceBottomAccessible n ((markedUpperBoxTrace n u v A).image Subtype.val) z := by
  apply traceBottomAccessible_not_of_halfTurn
  rw [markedUpperBoxTrace_negated_labels]
  exact hno

end
end PottsContinuity.Thm3.Prop4
