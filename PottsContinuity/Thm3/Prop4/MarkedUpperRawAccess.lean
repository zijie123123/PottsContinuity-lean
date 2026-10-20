module

public import PottsContinuity.Thm3.Prop4.MarkedBoxRawAccess
public import PottsContinuity.Thm3.Prop4.MarkedJointRawReveal
public import PottsContinuity.Thm3.Prop4.MarkedUpperTraceAccess

/-! # Bottom inaccessibility for actual upper raw query endpoints -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance markedUpperRawAccessEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- Every actual upper raw query endpoint is bottom-inaccessible while
avoiding the SAME nonempty concrete upper trace on the original sample. -/
theorem markedUpperBoxRawReveal_endpoint_no_bottom_access (n : ℕ)
    (u v : (box n : Set LatticeVertex))
    (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (A : Configuration (finiteLatticeGraph (box n)))
    (hne : (markedUpperBoxTrace n u v A).Nonempty)
    (e : (finiteLatticeGraph (box n)).edgeSet)
    (he : e ∈ markedUpperBoxRawReveal n u v A)
    (x : (box n : Set LatticeVertex)) (hx : x ∈ e.val) :
    ¬traceBottomAccessible n ((markedUpperBoxTrace n u v A).image Subtype.val) x.val := by
  classical
  have hemap : configurationIsoEdgeEquiv (boxHalfTurnIso n) e ∈
      configurationIso (boxHalfTurnIso n) (markedUpperBoxRawReveal n u v A) :=
    Finset.mem_map.mpr ⟨e,he,rfl⟩
  dsimp only [markedUpperBoxRawReveal] at hemap
  erw [Equiv.apply_symm_apply] at hemap
  have hxmap : boxHalfTurnIso n x ∈ (configurationIsoEdgeEquiv (boxHalfTurnIso n) e).val := by
    change boxHalfTurnIso n x ∈ Sym2.map (boxHalfTurnIso n) e.val
    exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩
  have hnerot : (markedLowerBoxTrace n (boxHalfTurnIso n v) (boxHalfTurnIso n u)
      (configurationIso (boxHalfTurnIso n) A)).Nonempty := by
    obtain ⟨z,hz⟩ := hne
    obtain ⟨y,hy,_⟩ := Finset.mem_map.mp hz
    exact ⟨y,hy⟩
  apply markedUpperBoxTrace_no_bottom_access_of_rotated_lower
  apply markedLowerBoxRawReveal_endpoint_no_top_access n (boxHalfTurnIso n v)
    (boxHalfTurnIso n u) ?_ ?_ _ hnerot _ hemap (boxHalfTurnIso n x) hxmap
  · change -v.val.1 = -(n : ℤ)
    rw [hv]
  · change -u.val.1 = (n : ℤ)
    rw [hu,neg_neg]

end
end PottsContinuity.Thm3.Prop4
