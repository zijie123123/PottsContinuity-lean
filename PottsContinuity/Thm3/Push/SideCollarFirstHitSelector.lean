module

public import PottsContinuity.Thm3.Push.SideCollarPathSelector
public import PottsContinuity.Thm3.Push.FirstContactPrefix

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 Exploration PlanarMixed.FiniteSlit
noncomputable section

/-- Original queried set and only the chronological prefix ending at the
first original left-side hit. The discarded path suffix is not stored. -/
abbrev SideCollarFirstHitRecord (w h : ℕ) :=
  Configuration (rectangleGraph (0,0) w h) × List (RectangleVertex (0,0) w h)

/-- Retain the first-left-hit prefix of the actual selected side arm.
The query set is the original full collar-derived stopping set. -/
def sideCollarFirstHitSelector (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) : Option (SideCollarFirstHitRecord w h) :=
  (sideCollarArmPathSelector w h l r C).bind fun rec =>
    (firstContactTrace {v | v.val.1 = 0} (rec.2.2.drop 2)).map fun trace => (rec.1,trace)

/-- A successful full path always supplies a genuine first-hit prefix. -/
theorem sideCollarFirstHitSelector_isSome_of_pathRecord (w h : ℕ) (l r : ℤ)
    (C : Configuration (rectangleGraph (0,0) w h)) (rec : SideCollarArmPathRecord w h)
    (hrec : sideCollarArmPathSelector w h l r C = some rec) :
    (sideCollarFirstHitSelector w h l r C).isSome := by
  obtain ⟨_,_,a,_,_,_,b,hb,p,hcode⟩ := sideCollarArmPathSelector_spec w h l r C rec hrec
  have htrace : rec.2.2.drop 2 = p.val.support := by
    rw [← hcode]
    rfl
  obtain ⟨k,_,hk⟩ := firstContactTrace_exists_prefix p.val {v | v.val.1 = 0} hb
  simp only [sideCollarFirstHitSelector,hrec,Option.bind_some,htrace,hk,Option.map_some,Option.isSome_some]

/-- The first-hit selector has the exact same success event as the actual
confined original side arm. -/
theorem sideCollarFirstHitSelector_isSome_iff (w h : ℕ) (l r : ℤ)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ (w:ℤ))
    (C : Configuration (rectangleGraph (0,0) w h)) :
    (sideCollarFirstHitSelector w h l r C).isSome ↔
      C ∈ arcsConnectionEvent (rectangleGraph (0,0) w h)
        {a | a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r} {b | b.val.1 = 0} := by
  rw [← sideCollarArmPathSelector_isSome_iff w h l r hl hlr hr C]
  cases heq : sideCollarArmPathSelector w h l r C with
  | none => simp only [sideCollarFirstHitSelector,heq,Option.bind_none,Option.isSome_none]
  | some rec =>
    simp only [Option.isSome_some,iff_true]
    exact sideCollarFirstHitSelector_isSome_of_pathRecord w h l r C rec heq

end
end PottsContinuity.Push
