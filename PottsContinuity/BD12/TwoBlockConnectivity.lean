module

public import PottsContinuity.BD12.TwoBlockBoundaryMerge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-!
# Actual connection between separately wired arcs

For BD12 Lemma self-duality, boundary identifications are used in the weight,
whereas the crossing event requires an actual open path. The equivalence below
justifies testing the two component classes without replacing that event by a
connection in an already joined boundary condition.
-/

@[expose] public section

namespace PottsContinuity.BD12

open PD.FK

variable {V : Type*} {G : SimpleGraph V}

/-- The event of an actual open path between the two specified vertex sets.
This definition applies also to empty or intersecting sets. -/
def arcsConnectionEvent (G : SimpleGraph V) (A B : Set V) : Set (Configuration G) :=
  {ω | ∃ a ∈ A, ∃ b ∈ B, ActualConnected G ω a b}

theorem arcsConnectionEvent_isUpperSet (A B : Set V) :
    IsUpperSet (arcsConnectionEvent G A B) := by
  rintro ω ω' hω ⟨a, ha, b, hb, hab⟩
  exact ⟨a, ha, b, hb, actualConnected_mono hω hab⟩

/-- The two separately wired component classes coincide exactly when some
actual open path joins the two arcs. The designated representatives need not
be the endpoints of that path. -/
theorem twoBlockBoundary_connected_iff [Finite V] (A B : Set V)
    (hAB : Disjoint A B) (ω : Configuration G) {u v : V}
    (hu : u ∈ A) (hv : v ∈ B) :
    (componentSetoid G (twoBlockBoundary A B hAB) ω).r u v ↔
      ω ∈ arcsConnectionEvent G A B := by
  let ξ := twoBlockBoundary A B hAB
  let S := componentSetoid G ξ ω
  constructor
  · intro huv
    by_contra hno
    let f : V → Prop := fun x => ∃ a ∈ A, ActualConnected G ω a x
    have hfA {a : V} (ha : a ∈ A) : f a := ⟨a, ha, .refl a⟩
    have hfB {b : V} (hb : b ∈ B) : ¬ f b := by
      rintro ⟨a, ha, hab⟩
      exact hno ⟨a, ha, b, hb, hab⟩
    have hle : S ≤ Setoid.ker f := by
      apply componentSetoid_le
      · intro x y hxy
        apply propext
        constructor
        · rintro ⟨a, ha, hax⟩
          exact ⟨a, ha, hax.trans hxy⟩
        · rintro ⟨a, ha, hay⟩
          exact ⟨a, ha, hay.trans hxy.symm⟩
      · intro x y hxy
        rcases (twoBlockBoundary_partition_rel A B hAB x y).mp hxy with h | h | h
        · subst y
          rfl
        · exact propext ⟨fun _ => hfA h.2, fun _ => hfA h.1⟩
        · exact propext ⟨fun hx => (hfB h.1 hx).elim, fun hy => (hfB h.2 hy).elim⟩
    have heq : f u = f v := hle huv
    exact hfB hv (heq ▸ hfA hu)
  · rintro ⟨a, ha, b, hb, hab⟩
    have hua : S.r u a := boundary_component G ξ ω
      ((twoBlockBoundary_partition_rel A B hAB u a).mpr (Or.inr (Or.inl ⟨hu, ha⟩)))
    have hbv : S.r b v := boundary_component G ξ ω
      ((twoBlockBoundary_partition_rel A B hAB b v).mpr (Or.inr (Or.inr ⟨hb, hv⟩)))
    exact S.trans hua (S.trans (actualConnected_component G ξ ω hab) hbv)

end PottsContinuity.BD12
