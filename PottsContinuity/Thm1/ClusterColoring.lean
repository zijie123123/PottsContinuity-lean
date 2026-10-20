module

public import Mathlib.Tactic

/-!
# Finite colourings of connected components

This is the elementary finite counting layer for the ghost-vertex coupling.
It is adapted to `Fin q` colours and to a distinguished pinned component.
-/

@[expose] public section

namespace PottsContinuity.Thm1

noncomputable section

open Classical

variable {V C : Type*}

/-- Vertex colorings taking one value on each class of an equivalence relation. -/
abbrev PottsClusterColoring (R : Setoid V) (C : Type*) :=
  {σ : V → C // R ≤ Setoid.ker σ}

/-- Assigning a color to each quotient class is equivalent to a coloring
with one value on each class. -/
def pottsClusterColoringEquiv (R : Setoid V) :
    PottsClusterColoring R C ≃ (Quotient R → C) :=
  Setoid.liftEquiv R

/-- Colourings with a specified vertex assigned its pinned colour. -/
abbrev PinnedPottsClusterColoring (R : Setoid V) (g : V) (i : C) :=
  {σ : PottsClusterColoring R C // σ.val g = i}

/-- Pinning a vertex is the same as pinning its quotient class. -/
def pinnedPottsClusterColoringEquiv (R : Setoid V) (g : V) (i : C) :
    PinnedPottsClusterColoring R g i ≃
      {f : Quotient R → C // f (Quotient.mk R g) = i} :=
  (pottsClusterColoringEquiv R).subtypeEquiv (fun _ => Iff.rfl)

theorem card_pinned_functions [Finite V] [Finite C] (g : V) (i : C) :
    Nat.card {f : V → C // f g = i} = Nat.card C ^ (Nat.card V - 1) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite C
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa only [Fintype.piFinset_univ, Finset.card_univ] using
    Fintype.card_filter_piFinset_const_eq_of_mem (Finset.univ : Finset C) g
      (Finset.mem_univ i)

theorem card_two_pinned_functions [Finite V] [Finite C] [DecidableEq V]
    (a b : V) (hab : a ≠ b) (i j : C) :
    Nat.card {f : V → C // f a = i ∧ f b = j} =
      Nat.card C ^ (Nat.card V - 2) := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite C
  let s : V → Finset C := Function.update (fun _ => Finset.univ) b {j}
  have hs : Fintype.piFinset s =
      {f ∈ (Finset.univ : Finset (V → C)) | f b = j} := by
    ext f
    rw [Fintype.mem_piFinset]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hf
      have hfb := hf b
      simpa [s] using hfb
    · intro hfb x
      by_cases hxb : x = b
      · subst x
        simpa [s] using hfb
      · simp [s, hxb]
  have hcard : Fintype.card {f : V → C // f a = i ∧ f b = j} =
      ((Fintype.piFinset s).filter (fun f : V → C => f a = i)).card := by
    rw [Fintype.card_subtype, hs]
    simp [Finset.filter_filter, and_comm]
  have ha : i ∈ s a := by simp [s, hab]
  have hb : b ∈ (Finset.univ : Finset V).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have hs_card : (fun x => (s x).card) =
      Function.update (fun _ : V => Fintype.card C) b 1 := by
    funext x
    by_cases hxb : x = b
    · subst x
      simp [s]
    · simp [s, hxb]
  have hcard_rem : ((Finset.univ : Finset V).erase a \ {b}).card =
      Fintype.card V - 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hb,
      Finset.card_erase_of_mem (Finset.mem_univ a)]
    simp only [Finset.card_univ]
    omega
  have hprod : ∏ x ∈ (Finset.univ : Finset V).erase a, (s x).card =
      Fintype.card C ^ (Fintype.card V - 2) := by
    rw [hs_card, Finset.prod_update_of_mem hb]
    rw [Finset.prod_const, hcard_rem]
    simp
  calc
    Nat.card {f : V → C // f a = i ∧ f b = j} =
        Fintype.card {f : V → C // f a = i ∧ f b = j} := by simp
    _ = ((Fintype.piFinset s).filter (fun f : V → C => f a = i)).card := hcard
    _ = ∏ x ∈ (Finset.univ : Finset V).erase a, (s x).card :=
      Fintype.card_filter_piFinset_eq_of_mem s a ha
    _ = Fintype.card C ^ (Fintype.card V - 2) := hprod
    _ = Nat.card C ^ (Nat.card V - 2) := by simp

def twoPinnedPottsClusterColoringEquiv (R : Setoid V) (a b : V)
    (i j : C) :
    {σ : PottsClusterColoring R C // σ.val a = i ∧ σ.val b = j} ≃
      {f : Quotient R → C // f (Quotient.mk R a) = i ∧
        f (Quotient.mk R b) = j} :=
  (pottsClusterColoringEquiv R).subtypeEquiv (fun _ => Iff.rfl)

theorem card_two_pinnedPottsClusterColoring [Finite V] [Finite C]
    (R : Setoid V) (a b : V) (hab : ¬ R.r a b) (i j : C) :
    Nat.card {σ : PottsClusterColoring R C // σ.val a = i ∧ σ.val b = j} =
      Nat.card C ^ (Nat.card (Quotient R) - 2) := by
  have hclasses : Quotient.mk R a ≠ Quotient.mk R b := by
    intro h
    exact hab (Quotient.exact h)
  rw [Nat.card_congr (twoPinnedPottsClusterColoringEquiv R a b i j)]
  exact card_two_pinned_functions (Quotient.mk R a) (Quotient.mk R b)
    hclasses i j

theorem card_pinnedPottsClusterColoring [Finite V] [Finite C]
    (R : Setoid V) (g : V) (i : C) :
    Nat.card (PinnedPottsClusterColoring R g i) =
      Nat.card C ^ (Nat.card (Quotient R) - 1) := by
  rw [Nat.card_congr (pinnedPottsClusterColoringEquiv R g i), card_pinned_functions]

end

end PottsContinuity.Thm1
