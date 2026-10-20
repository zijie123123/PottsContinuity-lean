module

public import PottsContinuity.Thm3.Push.IntervalArmFrontierWitness
public import PottsContinuity.Thm3.Push.CommonExplorationEvents
public import PottsContinuity.BD12.TwoBlockConnectivity

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
local instance intervalRecordEdgeDecidableEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _
local instance intervalRecordRemainingFintype (N : ℕ)
    (R : Configuration (rectangleGraph (0,0) N N)) :
    Fintype (RemainingConfiguration (rectangleGraph (0,0) N N) R) := Fintype.ofFinite _

/-- The literal bottom interval in the source square. -/
def intervalArmBottomArc (N : ℕ) (l r : ℤ) : Set (RectangleVertex (0,0) N N) :=
  {v | v.val.2 = 0 ∧ l ≤ v.val.1 ∧ v.val.1 ≤ r}

/-- Actual square-confined connectivity from the source interval to the full
top side, using BD12's existing actual arc-connectivity event. -/
abbrev intervalArmEvent (N : ℕ) (l r : ℤ) :=
  BD12.arcsConnectionEvent (rectangleGraph (0,0) N N) (intervalArmBottomArc N l r)
    {v | v.val.2 = (N : ℤ)}

/-- The concrete source frontier retains an arm in the actual OPEN record,
including the complete original starting interval and target side. -/
theorem intervalArmEvent_on_left_open_record
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r) :
    A ∩ intervalArmLeftReveal N l A ∈ intervalArmEvent N l r := by
  obtain ⟨s,hs,t,ht,⟨p⟩⟩ := hA
  obtain ⟨u,v,hu,hul,hur,hv,huv⟩ := intervalArmLeftFrontier_contains_arm N l r hl hlr hr A p
    hs.1 ht hs.2.1 hs.2.2
  exact ⟨u,⟨hu,hul,hur⟩,v,hv,actualConnected_mono
    (intervalArmLeftFrontier_subset_open_record N l A) huv⟩

/-- Success persists under arbitrary edits of the unrecorded original bonds. -/
theorem intervalArmEvent_of_left_record_agreement
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A B : Configuration (rectangleGraph (0,0) N N))
    (hstates : B ∩ intervalArmLeftReveal N l A = A ∩ intervalArmLeftReveal N l A)
    (hA : A ∈ intervalArmEvent N l r) : B ∈ intervalArmEvent N l r := by
  have hrecord := intervalArmEvent_on_left_open_record N l r hl hlr hr A hA
  have hsub : A ∩ intervalArmLeftReveal N l A ⊆ B := by
    rw [← hstates]
    exact Finset.inter_subset_left
  exact BD12.arcsConnectionEvent_isUpperSet _ _ hsub hrecord

/-- Both success and failure of the ACTUAL source interval-arm event are
read from the concrete source exploration. No observability premise remains. -/
theorem intervalArmEvent_readFromLeftReveal
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ)) :
    ReadFromReveal (intervalArmLeftReveal N l) (intervalArmEvent N l r) := by
  intro A B hB
  have hreverse : A ∩ intervalArmLeftReveal N l B = B ∩ intervalArmLeftReveal N l B := by
    rw [hB.1]
    exact hB.2.symm
  exact ⟨intervalArmEvent_of_left_record_agreement N l r hl hlr hr B A hreverse,
    intervalArmEvent_of_left_record_agreement N l r hl hlr hr A B hB.2⟩

end
end PottsContinuity.Push
