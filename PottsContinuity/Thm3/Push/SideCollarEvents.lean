module

public import PottsContinuity.Thm3.Push.SideCollarSeparation
public import PottsContinuity.Thm3.Push.IntervalArmRecord

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12
noncomputable section

/-- Original bottom intervals become strict interior bottom intervals in the
auxiliary square, including source intervals touching either original corner. -/
theorem sideCollar_interval_bounds (w h : ℕ) (l r : ℤ)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ (w:ℤ)) :
    0 < l+2 ∧ l+2 ≤ r+2 ∧ r+2 < (sideCollarSize w h:ℕ) := by
  dsimp [sideCollarSize]
  omega

/-- Exact deterministic event correspondence between an original confined
bottom-interval-to-left-side arm and its auxiliary interval-to-top arm.
The auxiliary configuration has no independently asserted probability law. -/
theorem sideCollar_interval_top_iff_source_left
    (w h : ℕ) (l r : ℤ) (hl : 0 ≤ l) (_hlr : l ≤ r) (hr : r ≤ (w:ℤ))
    (C : Configuration (rectangleGraph (0,0) w h)) :
    sideCollarExtension w h C ∈ intervalArmEvent (sideCollarSize w h) (l+2) (r+2) ↔
      C ∈ arcsConnectionEvent (rectangleGraph (0,0) w h)
        {a | a.val.2 = 0 ∧ l ≤ a.val.1 ∧ a.val.1 ≤ r} {b | b.val.1 = 0} := by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    let a₀ : RectangleVertex (0,0) w h := ⟨(a.val.1-2,0),by
      rw [mem_latticeRectangle]
      dsimp
      have hal := ha.2.1
      have har := ha.2.2
      constructor <;> constructor <;> omega⟩
    have ha₀ : sideCollarEmbedding w h a₀ = a := by
      apply Subtype.ext
      apply Prod.ext
      · change a.val.1-2+2=a.val.1
        omega
      · change (0:ℤ)=a.val.2
        exact ha.1.symm
    obtain ⟨c,hc,hac⟩ := sideCollar_outside_connection_implies_left w h C a₀ b
      (sideCollar_top_not_source w h b hb) (by rw [ha₀]; exact hab)
    refine ⟨a₀,?_,c,hc,hac⟩
    change (0:ℤ)=0 ∧ l ≤ a.val.1-2 ∧ a.val.1-2 ≤ r
    have hal := ha.2.1
    have har := ha.2.2
    omega
  · rintro ⟨a,ha,b,hb,hab⟩
    refine ⟨sideCollarEmbedding w h a,?_,sideCollarColumnVertex w h (Fin.last (sideCollarSize w h)),rfl,?_⟩
    · change a.val.2=0 ∧ l+2 ≤ a.val.1+2 ∧ a.val.1+2 ≤ r+2
      exact ⟨ha.1,by have h := ha.2.1; omega,by have h := ha.2.2; omega⟩
    · exact sideCollar_source_left_connection_implies_top w h C a ⟨b,hb,hab⟩

end
end PottsContinuity.Push
