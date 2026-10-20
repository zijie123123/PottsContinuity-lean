module

public import PottsContinuity.Thm3.Prop4.TwoMarkedOddFrontier
public import PottsContinuity.PD.Duality.LatticeCellBoundaryParity
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # An even frontier with exactly two exterior ports joins their marks -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
noncomputable section

/-- Restriction of an even-degree graph to a finite carrier joins its two
prescribed marks when those are its only exterior neighbors, one at each. -/
theorem reachable_induce_of_even_degrees_and_two_exterior_ports
    {V : Type*} (H : SimpleGraph V) (X : Set V) [Finite X]
    (u v : X) (hne : u ≠ v) (uo vo : V) (huo : uo ∉ X) (_hvo : vo ∉ X)
    (heven : ∀ z, Even (H.neighborSet z).ncard)
    (hports : ∀ z : X, ∀ t : V, (H.Adj z.val t ∧ t ∉ X) ↔
      (z = u ∧ t = uo) ∨ (z = v ∧ t = vo)) :
    (H.induce X).Reachable u v := by
  classical
  let twoExteriorPortFintype : Fintype X := Fintype.ofFinite _
  let D := H.induce X
  have himage (z : X) (t : V) :
      t ∈ Subtype.val '' D.neighborSet z ↔ H.Adj z.val t ∧ t ∈ X := by
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨hx,x.property⟩
    · rintro ⟨ht,hX⟩
      exact ⟨⟨t,hX⟩,ht,rfl⟩
  have huEq : H.neighborSet u.val = insert uo (Subtype.val '' D.neighborSet u) := by
    ext t
    constructor
    · intro ht
      by_cases htX : t ∈ X
      · exact Or.inr ((himage u t).mpr ⟨ht,htX⟩)
      · rcases (hports u t).mp ⟨ht,htX⟩ with ⟨_,rfl⟩ | ⟨heq,_⟩
        · exact Or.inl rfl
        · exact (hne heq).elim
    · rintro (htEq | ht)
      · subst t
        exact ((hports u uo).mpr (Or.inl ⟨rfl,rfl⟩)).1
      · exact ((himage u t).mp ht).1
  have huOdd : Odd (D.degree u) := by
    have he := heven u.val
    rw [huEq,Set.ncard_insert_of_notMem (by
      intro ht
      exact huo ((himage u uo).mp ht).2)
      ((Set.toFinite (D.neighborSet u)).image Subtype.val),
      Set.ncard_image_of_injective _ Subtype.val_injective,SimpleGraph.ncard_neighborSet] at he
    obtain ⟨k,hk⟩ := he
    exact ⟨k-1,by omega⟩
  apply reachable_of_two_marked_odd_vertices D u v huOdd
  intro z hzOdd
  by_contra hn
  have hzu : z ≠ u := fun h => hn (Or.inl h)
  have hzv : z ≠ v := fun h => hn (Or.inr h)
  have hzEq : H.neighborSet z.val = Subtype.val '' D.neighborSet z := by
    ext t
    constructor
    · intro ht
      apply (himage z t).mpr
      refine ⟨ht,?_⟩
      by_contra htX
      rcases (hports z t).mp ⟨ht,htX⟩ with ⟨h,_⟩ | ⟨h,_⟩
      · exact hzu h
      · exact hzv h
    · exact fun ht => ((himage z t).mp ht).1
  have he := heven z.val
  rw [hzEq,Set.ncard_image_of_injective _ Subtype.val_injective,SimpleGraph.ncard_neighborSet] at he
  obtain ⟨k,hk⟩ := he
  obtain ⟨l,hl⟩ := hzOdd
  omega

end
end PottsContinuity.Thm3.Prop4
