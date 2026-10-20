module

public import PottsContinuity.PlanarMixed.FiniteSlit.NativeSourceArms
public import PottsContinuity.PlanarMixed.FiniteSlit.CanonicalContactIndex

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK RSW
noncomputable section

/-- The original disjoint source walks force a first left-slit contact.
This conclusion contains only the original source walk and its coordinates. -/
theorem disjoint_openSourceSquare_firstContact_exists
    (n : ℕ) (x y B : ℤ) (hx : 1 ≤ x) (hxn : x ≤ (2*n:ℕ))
    (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    {a b u v : RectangleVertex (0,0) (2*n) (2*n)}
    (p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk a u)
    (q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk b v)
    (ha : a.val.2 = 0) (hb : b.val.2 = 0) (hu : u.val.1 = B)
    (hxa : x ≤ a.val.1) (hab : a.val.1 < b.val.1) (hv : v.val = (x,y))
    (hp : ∀ w ∈ p.support, w.val.1 ≤ B)
    (hq : ∀ w ∈ q.support, x ≤ w.val.1 ∧ w.val.1 ≤ B)
    (hdis : ∀ w ∈ p.support, w ∉ q.support) :
    ∃ k, IsFirstContact p {w | w.val.1 = x-1 ∧ y ≤ w.val.2} k := by
  let p₀ := p.mapLe (openGraph_le _ C)
  let q₀ := q.mapLe (openGraph_le _ C)
  obtain ⟨k,_,hkle,hhit,hfirst,_⟩ := sourceSquare_exists_crosscutData n x y B hx hxn
    p₀ q₀ ha hb hu hxa hab hv
    (by simpa only [p₀,SimpleGraph.Walk.support_mapLe_eq_support] using hp)
    (by simpa only [q₀,SimpleGraph.Walk.support_mapLe_eq_support] using hq)
    (by simpa only [p₀,q₀,SimpleGraph.Walk.support_mapLe_eq_support] using hdis)
  exact ⟨k,(isFirstContact_mapLe_iff (openGraph_le _ C) p _ k).mp ⟨hkle,hhit,hfirst⟩⟩

section
variable (n : ℕ) (x B : ℤ) (hx : 1 ≤ x) (hxn : x ≤ (2*n:ℕ))
  (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
  (I J : Set (RectangleVertex (0,0) (2*n) (2*n)))
  {a b u v : RectangleVertex (0,0) (2*n) (2*n)}
  (p : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk a u)
  (q : (openGraph (rectangleGraph (0,0) (2*n) (2*n)) C).Walk b v)
  (ha : a.val.2 = 0) (hb : b.val.2 = 0) (hu : u.val.1 = B)
  (hxa : x ≤ a.val.1) (hab : a.val.1 < b.val.1) (hv : v.val.1 = x)
  (hp : ∀ w ∈ p.support, w.val.1 ≤ B)
  (hq : ∀ w ∈ q.support, x ≤ w.val.1 ∧ w.val.1 ≤ B)
  (hdis : ∀ w ∈ p.support, w ∉ q.support) (haI : a ∈ I) (hbJ : b ∈ J)

/-- Canonical witness construction from original source walks. All fields
are supplied by those walks and their geometry; the crop index is the unique
least contact index, with no auxiliary path selection. -/
def nativeSourceArmsOfWalks : NativeSourceArms n C I J := by
  have hhit : ∃ k, k ≤ p.length ∧
      p.getVert k ∈ {w | w.val.1 = x-1 ∧ v.val.2 ≤ w.val.2} := by
    obtain ⟨k,hk⟩ := disjoint_openSourceSquare_firstContact_exists n x v.val.2 B hx hxn
      C p q ha hb hu hxa hab (Prod.ext hv rfl) hp hq hdis
    exact ⟨k,hk.1,hk.2.1⟩
  exact {
    column := x
    rightColumn := B
    column_pos := hx
    column_le := hxn
    paths := {
      firstStart := a
      secondStart := b
      firstEnd := u
      secondEnd := v
      first := p
      second := q }
    first_bottom := ha
    second_bottom := hb
    first_end_column := hu
    second_end_column := hv
    first_start_right := hxa
    starts_order := hab
    first_bounds := hp
    second_bounds := hq
    disjoint := hdis
    first_in := haI
    second_in := hbJ
    cropIndex := firstContactIndex p _ hhit
    first_contact := isFirstContact_firstContactIndex p _ hhit }

local notation "D" => nativeSourceArmsOfWalks n x B hx hxn C I J p q
  ha hb hu hxa hab hv hp hq hdis haI hbJ

end
end
end PottsContinuity.PlanarMixed.FiniteSlit
