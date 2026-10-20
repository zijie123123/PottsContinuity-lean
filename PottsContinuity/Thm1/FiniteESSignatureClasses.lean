module

public import PottsContinuity.Thm1.FiniteESPatternQuotient
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm1

open Classical

noncomputable section

variable {V : Type*}

/-- A marked label represents the ghost or one observed site. -/
def pottsESMarkedVertex (S : Finset V) (g : V) : Option {x : V // x ∈ S} → V
  | none => g
  | some x => x.1

/-- The relation induced on the finite marked labels by a component relation. -/
def pottsESMarkedRelation (R : Setoid V) (S : Finset V) (g : V) :
    Setoid (Option {x : V // x ∈ S}) where
  r a b := R.r (pottsESMarkedVertex S g a) (pottsESMarkedVertex S g b)
  iseqv := {
    refl := by intro a; exact R.iseqv.refl _
    symm := by intro a b h; exact R.iseqv.symm h
    trans := by intro a b c h₁ h₂; exact R.iseqv.trans h₁ h₂ }

/-- Quotient classes met by the observed sites or the pinned ghost. -/
noncomputable def pottsESMarkedComponentClasses (R : Setoid V) (S : Finset V) (g : V) :
    Finset (Quotient R) := by
  classical
  exact insert (Quotient.mk R g) (pottsESObservedComponentClasses R S)

/-- Marked quotient classes are equivalent to the finite marked-label quotient. -/
noncomputable def pottsESMarkedQuotientEquivClasses (R : Setoid V) (S : Finset V)
    (g : V) : Quotient (pottsESMarkedRelation R S g) ≃
      {z : Quotient R // z ∈ pottsESMarkedComponentClasses R S g} := by
  classical
  let M := Option {x : V // x ∈ S}
  let φ : M → Quotient R := fun a => Quotient.mk R (pottsESMarkedVertex S g a)
  have hφ : ∀ a b, (pottsESMarkedRelation R S g).r a b → φ a = φ b := by
    intro a b hab
    exact Quotient.sound hab
  have hφ' : ∀ a b, (pottsESMarkedRelation R S g).r a b →
      (⟨φ a, by
        cases a with
        | none => exact Finset.mem_insert_self _ _
        | some x =>
          apply Finset.mem_insert_of_mem
          apply Finset.mem_image.mpr
          exact ⟨x.1, x.2, rfl⟩⟩ :
        {z : Quotient R // z ∈ pottsESMarkedComponentClasses R S g}) =
      ⟨φ b, by
        cases b with
        | none => exact Finset.mem_insert_self _ _
        | some x =>
          apply Finset.mem_insert_of_mem
          apply Finset.mem_image.mpr
          exact ⟨x.1, x.2, rfl⟩⟩ := by
    intro a b hab
    apply Subtype.ext
    exact hφ a b hab
  let f : Quotient (pottsESMarkedRelation R S g) →
      {z : Quotient R // z ∈ pottsESMarkedComponentClasses R S g} :=
    Quotient.lift (fun a => ⟨φ a, by
      cases a with
      | none => exact Finset.mem_insert_self _ _
      | some x =>
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        exact ⟨x.1, x.2, rfl⟩⟩) hφ'
  have hinj : Function.Injective f := by
    intro qa qb heq
    revert heq
    refine Quotient.inductionOn₂ qa qb ?_
    intro a b hab
    apply Quotient.sound
    have hval := congrArg Subtype.val hab
    change Quotient.mk R (pottsESMarkedVertex S g a) =
      Quotient.mk R (pottsESMarkedVertex S g b) at hval
    change R.r (pottsESMarkedVertex S g a) (pottsESMarkedVertex S g b)
    exact Quotient.exact hval
  have hsurj : Function.Surjective f := by
    intro z
    rcases Finset.mem_insert.mp z.2 with hzg | hz
    · refine ⟨Quotient.mk (pottsESMarkedRelation R S g) none, ?_⟩
      apply Subtype.ext
      change Quotient.mk R g = z.1
      exact hzg.symm
    · rcases Finset.mem_image.mp hz with ⟨x, hx, hxz⟩
      refine ⟨Quotient.mk (pottsESMarkedRelation R S g) (some ⟨x, hx⟩), ?_⟩
      apply Subtype.ext
      change Quotient.mk R x = z.1
      exact hxz
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩

theorem pottsESMarkedComponentClasses_card_eq_quotient (R : Setoid V)
    [Finite V] (S : Finset V) (g : V) :
    (pottsESMarkedComponentClasses R S g).card =
      Nat.card (Quotient (pottsESMarkedRelation R S g)) := by
  classical
  let : Fintype V := Fintype.ofFinite _
  let : Fintype (Quotient R) := Fintype.ofFinite _
  let : Fintype (Quotient (pottsESMarkedRelation R S g)) := Fintype.ofFinite _
  calc
    (pottsESMarkedComponentClasses R S g).card =
        Fintype.card {z : Quotient R //
          z ∈ pottsESMarkedComponentClasses R S g} := (Fintype.card_coe _).symm
    _ = Fintype.card (Quotient (pottsESMarkedRelation R S g)) :=
      Fintype.card_congr (pottsESMarkedQuotientEquivClasses R S g).symm
    _ = Nat.card (Quotient (pottsESMarkedRelation R S g)) :=
      (Nat.card_eq_fintype_card).symm

end

end PottsContinuity.Thm1
