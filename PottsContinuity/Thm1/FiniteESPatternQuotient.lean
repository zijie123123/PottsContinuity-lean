module

public import PottsContinuity.Thm1.FiniteConstraintCounts
public import PottsContinuity.Thm1.ClusterColoring
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm1

open Classical

noncomputable section

variable {V C : Type*}

/-- Quotient classes meeting a finite set of observed sites. -/
noncomputable def pottsESObservedComponentClasses (R : Setoid V) (S : Finset V) : Finset (Quotient R) := by
  classical
  exact S.image (Quotient.mk R)

/-- A class touched by observations has a unique prescribed color when all
observations in each class agree. -/
theorem pottsES_existsUniqueObservedComponentColor (R : Setoid V) (S : Finset V)
    (c : V → C)
    (hstable : ∀ x ∈ S, ∀ y ∈ S, R.r x y → c x = c y)
    {z : Quotient R} (hz : z ∈ pottsESObservedComponentClasses R S) :
    ∃! d : C, ∃ x ∈ S, Quotient.mk R x = z ∧ c x = d := by
  classical
  rcases Finset.mem_image.mp hz with ⟨x, hx, hxz⟩
  refine ⟨c x, ⟨x, hx, hxz, rfl⟩, ?_⟩
  intro d hd
  rcases hd with ⟨y, hy, hyz, hyd⟩
  have hyx : R.r y x := Quotient.exact (hyz.trans hxz.symm)
  exact hyd.symm.trans (hstable y hy x hx hyx)

/-- The prescribed color on a marked quotient class, with a fallback on
unmarked classes. The selected marked value is unique by the agreement premise. -/
noncomputable def pottsESObservedComponentColor (R : Setoid V) (S : Finset V)
    (c : V → C) (fallback : C)
    (hstable : ∀ x ∈ S, ∀ y ∈ S, R.r x y → c x = c y)
    (z : Quotient R) : C :=
  if hz : z ∈ pottsESObservedComponentClasses R S then
    Classical.choose (pottsES_existsUniqueObservedComponentColor R S c hstable hz).exists
  else fallback

theorem pottsESObservedComponentColor_eq (R : Setoid V) (S : Finset V) (c : V → C)
    (fallback : C)
    (hstable : ∀ x ∈ S, ∀ y ∈ S, R.r x y → c x = c y)
    {z : Quotient R} (hz : z ∈ pottsESObservedComponentClasses R S)
    {x : V} (hx : x ∈ S) (hxz : Quotient.mk R x = z) :
    pottsESObservedComponentColor R S c fallback hstable z = c x := by
  classical
  unfold pottsESObservedComponentColor
  rw [dite_eq_left hz]
  rcases Classical.choose_spec
      (pottsES_existsUniqueObservedComponentColor R S c hstable hz).exists with
    ⟨y, hy, hyz, hyd⟩
  have hyx : R.r y x := Quotient.exact (hyz.trans hxz.symm)
  have heq : c y = c x := hstable y hy x hx hyx
  calc
    Classical.choose (pottsES_existsUniqueObservedComponentColor R S c hstable hz).exists = c y := hyd.symm
    _ = c x := heq


/-- Quotient colorings matching finitely many site colors and a pinned class. -/
def pottsESQuotientPatternColorings (R : Setoid V) (g : V) (i : C)
    (S : Finset V) (c : V → C) :=
  {f : Quotient R → C // f (Quotient.mk R g) = i ∧
    ∀ x ∈ S, f (Quotient.mk R x) = c x}

theorem card_pottsESQuotientPatternColorings
    (R : Setoid V) [Finite (Quotient R)] [Finite C] (g : V) (i : C)
    (S : Finset V) (c : V → C)
    (hstable : ∀ x ∈ S, ∀ y ∈ S, R.r x y → c x = c y)
    (hghost : ∀ x ∈ S, R.r x g → c x = i) :
    Nat.card (pottsESQuotientPatternColorings R g i S c) =
      Nat.card C ^ (Nat.card (Quotient R) -
        (insert (Quotient.mk R g) (pottsESObservedComponentClasses R S)).card) := by
  classical
  let T := pottsESObservedComponentClasses R S
  let d := pottsESObservedComponentColor R S c i hstable
  let hpin : ∀ z ∈ T, z = Quotient.mk R g → d z = i := by
    intro z hz hzg
    rcases Finset.mem_image.mp hz with ⟨x, hx, hxz⟩
    have hxg : Quotient.mk R x = Quotient.mk R g := hxz.trans hzg
    have hrel : R.r x g := Quotient.exact hxg
    rw [show d = pottsESObservedComponentColor R S c i hstable from rfl]
    rw [pottsESObservedComponentColor_eq R S c i hstable hz hx hxz]
    exact hghost x hx hrel
  have hpred (f : Quotient R → C) :
      (∀ x ∈ S, f (Quotient.mk R x) = c x) ↔
      ∀ z ∈ T, f z = d z := by
    constructor
    · intro hf z hz
      rcases Finset.mem_image.mp hz with ⟨x, hx, hxz⟩
      calc
        f z = f (Quotient.mk R x) := (congrArg f hxz).symm
        _ = c x := hf x hx
        _ = d z := (pottsESObservedComponentColor_eq R S c i hstable hz hx hxz).symm
    · intro hf x hx
      have hxT : Quotient.mk R x ∈ T := by
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hd := hf (Quotient.mk R x) hxT
      have hdeq : d (Quotient.mk R x) = c x :=
        pottsESObservedComponentColor_eq R S c i hstable hxT hx rfl
      exact hd.trans hdeq
  let : Fintype (Quotient R) := Fintype.ofFinite _
  let : Fintype C := Fintype.ofFinite _
  have : Finite (pottsESQuotientPatternColorings R g i S c) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Fintype (pottsESQuotientPatternColorings R g i S c) := Fintype.ofFinite _
  let E : pottsESQuotientPatternColorings R g i S c ≃
      {f : Quotient R → C // f (Quotient.mk R g) = i ∧
        ∀ z ∈ T, f z = d z} :=
    { toFun := fun f => ⟨f.1, f.2.1, (hpred f.1).mp f.2.2⟩
      invFun := fun f => ⟨f.1, f.2.1, (hpred f.1).mpr f.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcount : Fintype.card (pottsESQuotientPatternColorings R g i S c) =
      Fintype.card C ^ (Fintype.card (Quotient R) -
        (insert (Quotient.mk R g) T).card) := by
    calc
      Fintype.card (pottsESQuotientPatternColorings R g i S c) =
          Fintype.card {f : Quotient R → C //
            f (Quotient.mk R g) = i ∧ ∀ z ∈ T, f z = d z} := Fintype.card_congr E
      _ = Fintype.card C ^ (Fintype.card (Quotient R) -
            (insert (Quotient.mk R g) T).card) :=
        pottsES_card_functions_pinned_and_fixed
          (Quotient R) C (Quotient.mk R g) i T d hpin
  simpa only [Nat.card_eq_fintype_card, T] using hcount

end

end PottsContinuity.Thm1
