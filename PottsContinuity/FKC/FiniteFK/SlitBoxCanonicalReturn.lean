-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCanonicalReturn.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxExteriorReturnSimple
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

 theorem slitBoxCanonicalReturn_horizontal_bound
    (n : ℕ) (u : SlitBoxVertex n) (huX : 0 ≤ u.val.1) :
    u.val.1.toNat ≤ n := by
  have huBox := u.property
  rw [mem_latticeRectangle] at huBox
  have hx := huBox.1.2
  have hmax : -(n : ℤ) + (2 * n : ℕ) = (n : ℤ) := by
    push_cast
    omega
  rw [hmax] at hx
  have hxInt : (u.val.1.toNat : ℤ) ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg huX]
    exact hx
  exact_mod_cast hxInt

 theorem slitBoxCanonicalReturn_vertical_bound
    (n : ℕ) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    t.val.2.toNat ≤ n := by
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  have htInt : (t.val.2.toNat : ℤ) ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg htArc.2.1]
    exact htArc.2.2
  exact_mod_cast htInt

 theorem slitBoxCanonicalReturn_start_eq
    (n : ℕ) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    ((0 : ℤ), (t.val.2.toNat : ℤ)) = t.val := by
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  apply Prod.ext
  · exact htArc.1.symm
  · exact Int.toNat_of_nonneg htArc.2.1

 theorem slitBoxCanonicalReturn_end_eq
    (n : ℕ) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) :
    ((u.val.1.toNat : ℤ), -(n : ℤ)) = u.val := by
  apply Prod.ext
  · exact Int.toNat_of_nonneg huX
  · exact huY.symm

/-- The fixed, explicit exterior return walk for the actual slit arc vertex
and bottom vertex. It is the canonical Nat route with its endpoints copied to
the supplied geometric vertices; no existential choice is involved. -/
def slitBoxCanonicalReturnWalk
    (n : ℕ) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    squareLattice.Walk t.val u.val := by
  let a := u.val.1.toNat
  let k := t.val.2.toNat
  have ha : a ≤ n := slitBoxCanonicalReturn_horizontal_bound n u huX
  have hk : k ≤ n := slitBoxCanonicalReturn_vertical_bound n t ht
  exact (slitBoxExteriorReturnWalkNat n a k ha hk).val.copy
    (slitBoxCanonicalReturn_start_eq n t ht)
    (slitBoxCanonicalReturn_end_eq n u huY huX)

theorem slitBoxCanonicalReturnWalk_isPath
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    (slitBoxCanonicalReturnWalk n u huY huX t ht).IsPath := by
  simp only [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.isPath_copy]
  exact slitBoxExteriorReturnWalkNat_isPath n u.val.1.toNat t.val.2.toNat hn
    (slitBoxCanonicalReturn_horizontal_bound n u huX)
    (slitBoxCanonicalReturn_vertical_bound n t ht)

theorem slitBoxCanonicalReturnWalk_corner
    (n : ℕ) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    ((n + 1 : ℤ), (n + 1 : ℤ)) ∈
      (slitBoxCanonicalReturnWalk n u huY huX t ht).support := by
  have ha := slitBoxCanonicalReturn_horizontal_bound n u huX
  have hk := slitBoxCanonicalReturn_vertical_bound n t ht
  simpa [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.support_copy] using
    (slitBoxExteriorReturnWalkNat n u.val.1.toNat t.val.2.toNat ha hk).property

theorem slitBoxCanonicalReturnWalk_outside_box
    (n : ℕ) :
    ((n + 1 : ℤ), (n + 1 : ℤ)) ∉
      latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) := by
  rw [mem_latticeRectangle]
  push_cast
  omega

theorem slitBoxCanonicalReturnWalk_support_in_box
    (n : ℕ) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n)
    {z : LatticeVertex}
    (hz : z ∈ (slitBoxCanonicalReturnWalk n u huY huX t ht).support)
    (hzBox : z ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n)) :
    z = u.val ∨ (z.1 = 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ (n : ℤ)) := by
  have ha := slitBoxCanonicalReturn_horizontal_bound n u huX
  have hk := slitBoxCanonicalReturn_vertical_bound n t ht
  have hz' : z ∈ (slitBoxExteriorReturnWalkNat n u.val.1.toNat t.val.2.toNat ha hk).val.support := by
    simpa [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.support_copy] using hz
  rcases slitBoxExteriorReturnWalkNat_support_in_box n u.val.1.toNat t.val.2.toNat
      ha hk hz' hzBox with heq | harc
  · left
    have hend := slitBoxCanonicalReturn_end_eq n u huY huX
    exact heq.trans hend
  · exact Or.inr harc

end PottsContinuity.FKC.FiniteFK
