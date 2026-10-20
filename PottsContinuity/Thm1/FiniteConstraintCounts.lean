module

public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm1

open Classical

/-- Counting functions with prescribed values on a finite set of coordinates. -/
theorem pottsES_card_functions_fixed_on_finset (V C : Type*) [Fintype V]
    [DecidableEq V] [Fintype C] [DecidableEq C] (S : Finset V) (c : V → C) :
    Fintype.card {f : V → C // ∀ x ∈ S, f x = c x} =
      Fintype.card C ^ (Fintype.card V - S.card) := by
  classical
  let allowed : V → Finset C := fun x => if x ∈ S then {c x} else Finset.univ
  have hpi : Fintype.piFinset allowed =
      {f ∈ (Finset.univ : Finset (V → C)) | ∀ x ∈ S, f x = c x} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Fintype.mem_piFinset]
    constructor
    · intro h x hx
      simpa [allowed, hx] using h x
    · intro h x
      by_cases hx : x ∈ S
      · simpa [allowed, hx] using h x hx
      · simp [allowed, hx]
  calc
    Fintype.card {f : V → C // ∀ x ∈ S, f x = c x} =
        (Fintype.piFinset allowed).card := by
      rw [Fintype.card_subtype, hpi]
    _ = ∏ x, (allowed x).card := Fintype.card_piFinset allowed
    _ = ∏ x, (if x ∈ S then 1 else Fintype.card C) := by
      apply Finset.prod_congr rfl
      intro x hx
      by_cases hs : x ∈ S <;> simp [allowed, hs]
    _ = Fintype.card C ^ (Fintype.card V - S.card) := by
      have hprod :
          (∏ x ∈ S, (if x ∈ S then 1 else Fintype.card C)) *
            (∏ x ∈ Sᶜ, (if x ∈ S then 1 else Fintype.card C)) =
          ∏ x, (if x ∈ S then 1 else Fintype.card C) :=
        Finset.prod_mul_prod_compl S (fun x => if x ∈ S then 1 else Fintype.card C)
      rw [← hprod]
      have hS : ∏ x ∈ S, (if x ∈ S then 1 else Fintype.card C) = 1 := by
        apply Finset.prod_eq_one
        intro x hx
        simp [hx]
      have hSc : ∏ x ∈ Sᶜ, (if x ∈ S then 1 else Fintype.card C) =
          Fintype.card C ^ Sᶜ.card := by
        calc
          _ = ∏ x ∈ Sᶜ, Fintype.card C := by
            apply Finset.prod_congr rfl
            intro x hx
            have hn : x ∉ S := Finset.mem_compl.mp hx
            simp [hn]
          _ = _ := by rw [Finset.prod_const]
      rw [hS, one_mul, hSc, Finset.card_compl]

/-- Counting functions pinned at one distinguished coordinate and prescribed
on a finite set that is compatible with that pin. -/
theorem pottsES_card_functions_pinned_and_fixed (V C : Type*) [Fintype V]
    [DecidableEq V] [Fintype C] [DecidableEq C] (g : V) (i : C) (S : Finset V)
    (c : V → C) (hCompatible : ∀ x ∈ S, x = g → c x = i) :
    Fintype.card {f : V → C // f g = i ∧ ∀ x ∈ S, f x = c x} =
      Fintype.card C ^ (Fintype.card V - (insert g S).card) := by
  classical
  let prescribed : V → C := fun x => if x = g then i else c x
  let coloringEquiv :
      {f : V → C // f g = i ∧ ∀ x ∈ S, f x = c x} ≃
        {f : V → C // ∀ x ∈ insert g S, f x = prescribed x} := {
    toFun := fun f => ⟨f.1, by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxg | hxS
      · subst x
        simpa [prescribed] using f.2.1
      · by_cases hxg : x = g
        · subst x
          simpa [prescribed, hCompatible g hxS rfl] using f.2.1
        · simpa [prescribed, hxg] using f.2.2 x hxS⟩
    invFun := fun f => ⟨f.1, by
      constructor
      · have h := f.2 g (Finset.mem_insert_self g S)
        simpa [prescribed] using h
      · intro x hx
        have h := f.2 x (Finset.mem_insert_of_mem hx)
        by_cases hxg : x = g
        · subst x
          have hp : prescribed g = i := by simp [prescribed]
          rw [hp] at h
          exact h.trans (hCompatible g hx rfl).symm
        · simpa [prescribed, hxg] using h⟩
    left_inv := by intro f; apply Subtype.ext; rfl
    right_inv := by intro f; apply Subtype.ext; rfl }
  rw [Fintype.card_congr coloringEquiv]
  exact pottsES_card_functions_fixed_on_finset V C (insert g S) prescribed

end PottsContinuity.Thm1
