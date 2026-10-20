module

public import PottsContinuity.Thm3.Push.SourceSideArm
public import PottsContinuity.PlanarMixed.IntersectingCrosscuts
public import PottsContinuity.PlanarMixed.FiniteSlit.NativeSourceArms
public import PottsContinuity.PlanarMixed.FiniteSlit.IntersectingSourceRecord
public import PottsContinuity.PlanarMixed.FiniteSlit.OpenRectangleCrosscuts

@[expose] public section

namespace PottsContinuity.Push
open PD.FK BD12 PlanarMixed PlanarMixed.FiniteSlit
noncomputable section

/-- Any disjoint actual Case 2 walks have a native first-contact crop.
The full supplied walks are preserved exactly; no extremal choice or
configuration-locality premise is used. -/
theorem sourceCaseTwo_native_arms_of_disjoint_walks
    (n s : ℕ) (hs : 1 ≤ s) (hscale : 9*s ≤ 2*n)
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    {a b u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk a u)
    (q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk b v)
    (ha : a ∈ intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
    (hb : b ∈ intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ)))
    (hu : u.val.1 = 9*(s:ℤ)) (hv : v.val.1 = 4*(s:ℤ))
    (hp : ∀ z ∈ p.support, z.val.1 ≤ 9*(s:ℤ))
    (hq : ∀ z ∈ q.support, 4*(s:ℤ) ≤ z.val.1 ∧ z.val.1 ≤ 9*(s:ℤ))
    (hdis : ∀ z ∈ p.support, z ∉ q.support) :
    ∃ D : NativeSourceArms n C
      (intervalArmBottomArc (2*n) (4*(s:ℤ)) (5*(s:ℤ)))
      (intervalArmBottomArc (2*n) (6*(s:ℤ)) (7*(s:ℤ))),
      D.column = 4*(s:ℤ) ∧ D.rightColumn = 9*(s:ℤ) ∧
      D.paths = ⟨a,b,u,v,p,q⟩ := by
  obtain ⟨k,hk,_⟩ := openSourceRectangle_exists_crosscutData (2*n) (2*n)
    (4*(s:ℤ)) v.val.2 (9*(s:ℤ)) (by omega) (by omega) C p q
    ha.1 hb.1 hu ha.2.1 (by have ha' := ha.2.2; have hb' := hb.2.1; omega)
    (Prod.ext hv rfl) hp hq hdis
  refine ⟨{
    column := 4*(s:ℤ)
    rightColumn := 9*(s:ℤ)
    column_pos := by omega
    column_le := by omega
    paths := ⟨a,b,u,v,p,q⟩
    first_bottom := ha.1
    second_bottom := hb.1
    first_end_column := hu
    second_end_column := hv
    first_start_right := ha.2.1
    starts_order := by
      change a.val.1 < b.val.1
      have ha' := ha.2.2
      have hb' := hb.2.1
      omega
    first_bounds := hp
    second_bounds := hq
    disjoint := hdis
    first_in := ha
    second_in := hb
    cropIndex := k
    first_contact := hk },rfl,rfl,rfl⟩

end
end PottsContinuity.Push
