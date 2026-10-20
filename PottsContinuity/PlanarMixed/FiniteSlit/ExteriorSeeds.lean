module

public import PottsContinuity.PlanarMixed.FiniteSlit.ExteriorGraphIdentity

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK
noncomputable section

/-- Source bottom-left seeds together with the separate left exterior vertex. -/
def sourceAlpha (w h : ℕ) (x : ℤ) : Set (ExteriorVertex w h) :=
  {z | match z with
    | Sum.inl u => u.val.2 = 0 ∧ u.val.1 ≤ x
    | Sum.inr s => s = false}

/-- Source marked-ray seeds together with the separate right exterior vertex. -/
def sourceBeta (w h : ℕ) (x y : ℤ) : Set (ExteriorVertex w h) :=
  {z | match z with
    | Sum.inl u => u.val.1 = x ∧ y ≤ u.val.2
    | Sum.inr s => s = true}

/-- Exact projection of the left wired arc; there is no reference-size
parameter in its source-only description. -/
theorem exteriorProjection_image_alpha (M : ℕ) (x : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M) :
    exteriorProjection M x w h '' alpha M x = sourceAlpha w h x := by
  let f := rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega)
  ext z
  cases z with
  | inl u =>
    change (∃ v, v ∈ alpha M x ∧ exteriorProjection M x w h v = Sum.inl u) ↔
      u.val.2 = 0 ∧ u.val.1 ≤ x
    constructor
    · rintro ⟨v,hv,hπ⟩
      have hc := (exteriorProjection_eq_inl_iff M x w h v u).mp hπ
      change ((v.val.2 = 0 ∧ v.val.1 ≤ x) ∨ v.val.1 = x-(M:ℤ) ∨
        (v.val.2 = (M:ℤ) ∧ v.val.1 ≤ x-1)) at hv
      rw [hc] at hv
      have hub := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
      dsimp at hub
      omega
    · intro hu
      refine ⟨f u,?_,exteriorProjection_rectangleIntoReference M x w h
        (by omega) (by omega) (by omega) (by omega) u⟩
      exact Or.inl hu
  | inr s =>
    cases s with
    | false =>
      change (∃ v, v ∈ alpha M x ∧ exteriorProjection M x w h v = Sum.inr false) ↔ false = false
      refine ⟨fun _ => rfl,fun _ => ?_⟩
      refine ⟨leftTop M x (by omega),Or.inr (Or.inl rfl),?_⟩
      apply (exteriorProjection_eq_left_iff M x w h _).mpr
      refine ⟨(outside_source_iff M x w h (by omega) _).mpr ?_,?_⟩ <;>
        dsimp [leftTop] <;> omega
    | true =>
      change (∃ v, v ∈ alpha M x ∧ exteriorProjection M x w h v = Sum.inr true) ↔ true = false
      constructor
      · rintro ⟨v,hv,hπ⟩
        exfalso
        have hc := (exteriorProjection_eq_right_iff M x w h v).mp hπ
        have hout := (outside_source_iff M x w h (by omega) v).mp hc.1
        change ((v.val.2 = 0 ∧ v.val.1 ≤ x) ∨ v.val.1 = x-(M:ℤ) ∨
          (v.val.2 = (M:ℤ) ∧ v.val.1 ≤ x-1)) at hv
        omega
      · intro he
        cases he

/-- Exact projection of the right wired arc, including the tip at height y. -/
theorem exteriorProjection_image_beta (M : ℕ) (x y : ℤ) (w h : ℕ)
    (hM : 2 ≤ M) (hx : 1 ≤ x) (_hxw : x ≤ (w:ℤ))
    (hleft : x-(M:ℤ) < 0) (hright : (w:ℤ) < x+(M:ℤ)-1) (hh : h < M) :
    exteriorProjection M x w h '' beta M x y = sourceBeta w h x y := by
  let f := rectangleIntoReference M x w h (by omega) (by omega) (by omega) (by omega)
  ext z
  cases z with
  | inl u =>
    change (∃ v, v ∈ beta M x y ∧ exteriorProjection M x w h v = Sum.inl u) ↔
      u.val.1 = x ∧ y ≤ u.val.2
    constructor
    · rintro ⟨v,hv,hπ⟩
      have hc := (exteriorProjection_eq_inl_iff M x w h v u).mp hπ
      change (v.val.1 = x+(M:ℤ)-1 ∨ (v.val.2 = (M:ℤ) ∧ x ≤ v.val.1) ∨
        (v.val.1 = x ∧ y ≤ v.val.2)) at hv
      rw [hc] at hv
      have hub := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
      dsimp at hub
      omega
    · intro hu
      refine ⟨f u,?_,exteriorProjection_rectangleIntoReference M x w h
        (by omega) (by omega) (by omega) (by omega) u⟩
      exact Or.inr (Or.inr hu)
  | inr s =>
    cases s with
    | false =>
      change (∃ v, v ∈ beta M x y ∧ exteriorProjection M x w h v = Sum.inr false) ↔ false = true
      constructor
      · rintro ⟨v,hv,hπ⟩
        exfalso
        have hc := (exteriorProjection_eq_left_iff M x w h v).mp hπ
        change (v.val.1 = x+(M:ℤ)-1 ∨ (v.val.2 = (M:ℤ) ∧ x ≤ v.val.1) ∨
          (v.val.1 = x ∧ y ≤ v.val.2)) at hv
        omega
      · intro he
        cases he
    | true =>
      change (∃ v, v ∈ beta M x y ∧ exteriorProjection M x w h v = Sum.inr true) ↔ true = true
      refine ⟨fun _ => rfl,fun _ => ?_⟩
      refine ⟨rightTop M x (by omega),Or.inl rfl,?_⟩
      apply (exteriorProjection_eq_right_iff M x w h _).mpr
      refine ⟨(outside_source_iff M x w h (by omega) _).mpr ?_,?_⟩ <;>
        dsimp [rightTop] <;> omega

end
end PottsContinuity.PlanarMixed.FiniteSlit
