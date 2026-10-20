module

public import PottsContinuity.Thm3.Push.SquareRegionLeftSideIncidence
public import PottsContinuity.Thm3.Push.IntervalArmRightAttachments

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance physicalSideEdgeEq (N : ℕ) :
    DecidableEq (rectangleGraph (0,0) N N).edgeSet := Classical.decEq _

/-- The entire physical left square side is incident to the actual filled
left reveal, including both corners. -/
theorem intervalArmFilledLeft_left_side_incident_reveal
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u : RectangleVertex (0,0) N N) (hu : u.val.1=0) :
    ∃ f ∈ intervalArmFilledLeftReveal N l r A, u ∈ f.val := by
  obtain ⟨hleft,hright⟩ := intervalArmFilled_region_seed_labels N l r hl hlr hr A hA
  apply squareRegion_left_side_vertex_incident_reveal N (by omega)
    (intervalArmRightRegion N l r A)ᶜ _ u hu
  intro z hz
  exact hleft z ((mem_intervalArmLeftDualPorts N l z).mpr (Or.inl hz))

/-- The entire physical right square side is incident to the actual filled
right reveal, with literal original bonds preserved by reflection. -/
theorem intervalArmFilledRight_right_side_incident_reveal
    (N : ℕ) (l r : ℤ) (hl : 0 < l) (hlr : l ≤ r) (hr : r < (N : ℤ))
    (A : Configuration (rectangleGraph (0,0) N N)) (hA : A ∈ intervalArmEvent N l r)
    (u : RectangleVertex (0,0) N N) (hu : u.val.1=(N : ℤ)) :
    ∃ f ∈ intervalArmFilledRightReveal N l r A, u ∈ f.val := by
  let e := squareArmReflectionIso N
  let B := (configurationIso e).symm A
  have hB : B ∈ intervalArmEvent N ((N : ℤ)-r) ((N : ℤ)-l) := by
    apply (intervalArmEvent_reflection_iff N ((N : ℤ)-r) ((N : ℤ)-l) _).mp
    simpa only [B,e,Equiv.apply_symm_apply,sub_sub_cancel] using hA
  have hu' : (e.symm u).val.1=0 := by
    change (N : ℤ)-u.val.1=0
    omega
  obtain ⟨g,hg,hug⟩ := intervalArmFilledLeft_left_side_incident_reveal
    N ((N : ℤ)-r) ((N : ℤ)-l) (by omega) (by omega) (by omega) B hB (e.symm u) hu'
  refine ⟨configurationIsoEdgeEquiv e g,Finset.mem_map.mpr ⟨g,hg,rfl⟩,?_⟩
  change u ∈ Sym2.map e g.val
  exact Sym2.mem_map.mpr ⟨e.symm u,hug,e.apply_symm_apply u⟩

end
end PottsContinuity.Push
