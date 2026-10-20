module

public import PottsContinuity.PlanarMixed.FiniteSlit.RectangleContactExistence
public import PottsContinuity.PlanarMixed.FiniteSlit.CanonicalSourceArms
public import PottsContinuity.PlanarMixed.FiniteSlit.FixedPrefixRecord

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- Actual disjoint source arms on the original rectangle before choosing
any crop. All fields are ordinary open-walk geometry and root membership. -/
structure RectangleSourceArms (w h : ℕ)
    (C : Configuration (rectangleGraph (0,0) w h))
    (I J : Set (RectangleVertex (0,0) w h)) where
  column : ℤ
  column_pos : 1 ≤ column
  paths : SourceWalkPair (openGraph (rectangleGraph (0,0) w h) C)
  first_bottom : paths.firstStart.val.2 = 0
  second_bottom : paths.secondStart.val.2 = 0
  second_end_column : paths.secondEnd.val.1 = column
  first_start_right : column ≤ paths.firstStart.val.1
  starts_order : paths.firstStart.val.1 < paths.secondStart.val.1
  first_bounds : ∀ z ∈ paths.first.support, z.val.1 ≤ paths.firstEnd.val.1
  second_bounds : ∀ z ∈ paths.second.support,
    column ≤ z.val.1 ∧ z.val.1 ≤ paths.firstEnd.val.1
  disjoint : ∀ z ∈ paths.first.support, z ∉ paths.second.support
  first_in : paths.firstStart ∈ I
  second_in : paths.secondStart ∈ J

namespace RectangleSourceArms
variable {w h : ℕ} {C : Configuration (rectangleGraph (0,0) w h)}
    {I J : Set (RectangleVertex (0,0) w h)} (D : RectangleSourceArms w h C I J)

/-- The column bound follows from the actual endpoint's original carrier. -/
theorem column_le : D.column ≤ (w:ℤ) := by
  have hh := (mem_latticeRectangle _ _ _ _).mp D.paths.secondEnd.property
  rw [D.second_end_column] at hh
  simpa using hh.1.2

/-- Disjoint source geometry proves existence of contact; it is not a field
of the source-arm data and no simple-path assumption is needed. -/
theorem firstContact_exists :
    ∃ k, IsFirstContact D.paths.first
      {z | z.val.1 = D.column-1 ∧ D.paths.secondEnd.val.2 ≤ z.val.2} k :=
  disjoint_openSourceRectangle_firstContact_exists w h D.column D.paths.firstEnd.val.1
    D.column_pos C D.paths D.first_bottom D.second_bottom rfl D.second_end_column
    D.first_start_right D.starts_order D.first_bounds D.second_bounds D.disjoint

/-- The unique least actual LEFT-slit contact, derived from the original
arms. No value is assigned to a non-hitting source walk. -/
def cropIndex : ℕ :=
  firstContactIndex D.paths.first
    {z | z.val.1 = D.column-1 ∧ D.paths.secondEnd.val.2 ≤ z.val.2}
    (by obtain ⟨k,hk⟩ := D.firstContact_exists; exact ⟨k,hk.1,hk.2.1⟩)

end RectangleSourceArms
end
end PottsContinuity.PlanarMixed.FiniteSlit
