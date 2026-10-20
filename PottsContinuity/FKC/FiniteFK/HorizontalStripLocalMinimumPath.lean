-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripLocalMinimumPath.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripLocalMinimumGeometry

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

private theorem stripVertex_y_toNat_bound
    (n : ℕ) (v : horizontalStripVertex n) : v.val.2.toNat ≤ 2 * n := by
  have hcast : (v.val.2.toNat : ℤ) = v.val.2 := Int.toNat_of_nonneg v.property.1
  have hbound : (v.val.2.toNat : ℤ) ≤ 2 * (n : ℤ) := by
    rw [hcast]
    exact v.property.2
  exact_mod_cast hbound

private theorem stripVertex_eq_nat
    (n : ℕ) (v : horizontalStripVertex n) :
    horizontalStripVertexOfNat n v.val.1 v.val.2.toNat
      (stripVertex_y_toNat_bound n v) = v := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact Int.toNat_of_nonneg v.property.1

private theorem horizontalStripPath_vertex_height_lower
    (n m : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    (hk : horizontalStripHeight n ω k ≤ 2 * n)
    (hlocal : ∀ l : ℤ, (l - k).natAbs ≤ m →
      horizontalStripHeight n ω k ≤ horizontalStripHeight n ω l)
    {v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n ω).Walk
      (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) hk) v)
    (j : ℕ)
    (hnear : ((p.getVert j).val.1 - k).natAbs ≤ m) :
    horizontalStripHeight n ω k ≤ (p.getVert j).val.2.toNat := by
  have hy := stripVertex_y_toNat_bound n (p.getVert j)
  have hv := stripVertex_eq_nat n (p.getVert j)
  have hpath : (horizontalStripOpenGraph n ω).Reachable
      (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) hk)
      (horizontalStripVertexOfNat n (p.getVert j).val.1
        (p.getVert j).val.2.toNat hy) := by
    refine ⟨(p.take j).copy rfl hv.symm⟩
  exact horizontalStripHeight_le_of_local_minimum_radius
    n m ω k (p.getVert j).val.1 (p.getVert j).val.2.toNat
    hk hy hnear hlocal hpath

/-- For a given strip walk leaving the open local-minimum window, its first
exit prefix stays in the closed rectangle and ends on one of its three wired
sides. The index refers to the given walk, so every later path argument can
use this actual first hit. -/
theorem horizontalStripLocalMinimum_walk_firstExit
    (n m : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    (hn : 0 < n) (hm : 0 < m)
    (hk : horizontalStripHeight n ω k ≤ n)
    (hlocal : ∀ l : ℤ, (l - k).natAbs ≤ m →
      horizontalStripHeight n ω k ≤ horizontalStripHeight n ω l)
    {v : horizontalStripVertex n}
    (p : (horizontalStripOpenGraph n ω).Walk
      (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k)
        (Nat.le_trans hk (by omega))) v)
    (houtside : ¬ ((v.val.1 - k).natAbs < m ∧
      v.val.2 < (horizontalStripHeight n ω k + n : ℕ))) :
    ∃ i ≤ p.length,
      (∀ z ∈ (p.take i).support,
        (z.val.1 - k).natAbs ≤ m ∧
        (horizontalStripHeight n ω k : ℤ) ≤ z.val.2 ∧
        z.val.2 ≤ (horizontalStripHeight n ω k + n : ℕ)) ∧
      ((p.getVert i).val.1 = k - m ∨
        (p.getVert i).val.1 = k + m ∨
        (p.getVert i).val.2 = (horizontalStripHeight n ω k + n : ℕ)) := by
  classical
  let h := horizontalStripHeight n ω k
  have hk2 : h ≤ 2 * n := by omega
  have hkStrip : h ≤ 2 * n := by omega
  let inside : horizontalStripVertex n → Prop := fun z =>
    (z.val.1 - k).natAbs < m ∧ z.val.2 < (h + n : ℕ)
  have hstart : inside (horizontalStripVertexOfNat n k h hkStrip) := by
    change (k - k).natAbs < m ∧ (h : ℤ) < ((h + n : ℕ) : ℤ)
    constructor
    · simpa using hm
    · exact_mod_cast (by omega : h < h + n)
  have hendbad : ¬ inside (p.getVert p.length) := by
    rw [p.getVert_length]
    simpa [inside] using houtside
  have hexit : ∃ j : ℕ, ¬ inside (p.getVert j) := ⟨p.length, hendbad⟩
  let i := Nat.find hexit
  have hiBad : ¬ inside (p.getVert i) := Nat.find_spec hexit
  have hiLe : i ≤ p.length := Nat.find_min' hexit hendbad
  have hiPos : 0 < i := by
    by_contra hnot
    have hi0 : i = 0 := by omega
    subst i
    have hzero : inside (p.getVert 0) := by
      simpa only [p.getVert_zero] using hstart
    rw [hi0] at hiBad
    exact hiBad hzero
  have hprevInside : inside (p.getVert (i - 1)) :=
    not_not.mp (Nat.find_min hexit (m := i - 1) (by omega))
  have hstep : (horizontalStripOpenGraph n ω).Adj
      (p.getVert (i - 1)) (p.getVert i) := by
    have hidx : i - 1 < p.length := by omega
    have hadj := p.adj_getVert_succ hidx
    convert hadj using 1; congr 1; omega
  have hbase : (wholePlaneOpenPrimalGraph ω).Adj
      (p.getVert (i - 1)).val (p.getVert i).val := by
    exact hstep
  have hcoord := (PottsContinuity.FKC.squareLattice_adj_iff _ _).mp hbase.choose
  have hprevXabs : |(p.getVert (i - 1)).val.1 - k| < (m : ℤ) := by
    have := hprevInside.1
    rw [← Int.natCast_natAbs]
    exact_mod_cast this
  have hcurrXabs : |(p.getVert i).val.1 - k| ≤ (m : ℤ) := by
    rcases hcoord with ⟨horiz, hy⟩ | ⟨hx, vert⟩
    · have hxstep : |(p.getVert i).val.1 - (p.getVert (i - 1)).val.1| ≤ 1 := by
        rcases horiz with hx | hx <;> rw [← hx] <;> simp
      have hprev := abs_lt.mp hprevXabs
      have := abs_add_le ((p.getVert i).val.1 - (p.getVert (i - 1)).val.1)
        ((p.getVert (i - 1)).val.1 - k)
      have heq : (p.getVert i).val.1 - k =
          ((p.getVert i).val.1 - (p.getVert (i - 1)).val.1) +
          ((p.getVert (i - 1)).val.1 - k) := by ring
      rw [heq]
      nlinarith
    · rw [← hx]
      exact le_of_lt hprevXabs
  have hcurrYupper : (p.getVert i).val.2 ≤ (h + n : ℕ) := by
    rcases hcoord with ⟨horiz, hy⟩ | ⟨hx, vert⟩
    · rw [← hy]
      exact le_of_lt hprevInside.2
    · have hstepY : |(p.getVert i).val.2 - (p.getVert (i - 1)).val.2| ≤ 1 := by
        rcases vert with hy | hy <;> rw [← hy] <;> simp
      have hprevU : (p.getVert (i - 1)).val.2 < (h + n : ℤ) := by
        exact_mod_cast hprevInside.2
      have heq : (p.getVert i).val.2 =
          ((p.getVert i).val.2 - (p.getVert (i - 1)).val.2) +
          (p.getVert (i - 1)).val.2 := by ring
      rw [heq]
      have habs := abs_le.mp hstepY
      omega
  have hcurrXnat : ((p.getVert i).val.1 - k).natAbs ≤ m := by
    have hcast : ((((p.getVert i).val.1 - k).natAbs : ℕ) : ℤ) ≤ (m : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hcurrXabs
    exact_mod_cast hcast
  have hcurrYlower : (h : ℤ) ≤ (p.getVert i).val.2 := by
    have hlow := horizontalStripPath_vertex_height_lower
      n m ω k hk2 hlocal p i hcurrXnat
    have hcast : ((p.getVert i).val.2.toNat : ℤ) = (p.getVert i).val.2 :=
      Int.toNat_of_nonneg (p.getVert i).property.1
    rw [← hcast]
    exact_mod_cast hlow
  have hboundary :
      (p.getVert i).val.1 = k - m ∨
      (p.getVert i).val.1 = k + m ∨
      (p.getVert i).val.2 = (h + n : ℕ) := by
    by_contra hnot
    have hxstrict : ((p.getVert i).val.1 - k).natAbs < m := by
      have hleft : (-(m : ℤ)) < (p.getVert i).val.1 - k := by
        have hne : (p.getVert i).val.1 - k ≠ -(m : ℤ) := by
          intro heq
          apply hnot
          exact Or.inl (by omega)
        have hbounds := abs_le.mp hcurrXabs
        omega
      have hright : (p.getVert i).val.1 - k < (m : ℤ) := by
        have hne : (p.getVert i).val.1 - k ≠ (m : ℤ) := by
          intro heq
          apply hnot
          exact Or.inr (Or.inl (by omega))
        have hbounds := abs_le.mp hcurrXabs
        omega
      have habs : |(p.getVert i).val.1 - k| < (m : ℤ) := abs_lt.mpr ⟨hleft, hright⟩
      have hcast : ((((p.getVert i).val.1 - k).natAbs : ℕ) : ℤ) < (m : ℤ) := by
        rw [Int.natCast_natAbs]
        exact habs
      exact_mod_cast hcast
    have hys : (p.getVert i).val.2 < (h + n : ℤ) := by
      have hne : (p.getVert i).val.2 ≠ (h + n : ℕ) := by
        intro heq
        exact hnot (Or.inr (Or.inr heq))
      omega
    exact hiBad ⟨hxstrict, hys⟩
  refine ⟨i, hiLe, ⟨?_, hboundary⟩⟩
  intro z hz
  change z ∈ (p.take i).support at hz
  rw [SimpleGraph.Walk.support_take] at hz
  have hzmem : z ∈ p.support := List.mem_of_mem_take hz
  obtain ⟨j, hjlt, hzTake⟩ := List.mem_iff_getElem.mp hz
  have hjle : j ≤ i := by
    rw [List.length_take] at hjlt
    omega
  have hzElem : p.support[j]'(by rw [p.length_support]; omega) = z := by
    simpa using hzTake
  have hzget : p.getVert j = z := by
    rw [p.getVert_eq_support_getElem (le_trans hjle hiLe)]
    exact hzElem
  have hxbound : ((p.getVert j).val.1 - k).natAbs ≤ m := by
    by_cases hji : j = i
    · simpa [hji] using hcurrXnat
    · have hji' : j < i := by omega
      have hinterior := Nat.find_min hexit hji'
      have hinside : inside (p.getVert j) := by
        simpa [inside] using hinterior
      exact Nat.le_of_lt hinside.1
  have hylowerNat : horizontalStripHeight n ω k ≤ (p.getVert j).val.2.toNat :=
    horizontalStripPath_vertex_height_lower n m ω k hk2 hlocal p j hxbound
  have hylower : (horizontalStripHeight n ω k : ℤ) ≤ (p.getVert j).val.2 := by
    have hcast : (((p.getVert j).val.2.toNat : ℕ) : ℤ) = (p.getVert j).val.2 :=
      Int.toNat_of_nonneg (p.getVert j).property.1
    rw [← hcast]
    exact_mod_cast hylowerNat
  have hyupper : (p.getVert j).val.2 ≤ (horizontalStripHeight n ω k + n : ℕ) := by
    by_cases hji : j = i
    · simpa [hji] using hcurrYupper
    · have hinside : inside (p.getVert j) :=
        not_not.mp (Nat.find_min hexit (by omega : j < i))
      have hstrict : (p.getVert j).val.2 <
          (horizontalStripHeight n ω k + n : ℤ) := hinside.2
      exact le_of_lt hstrict
  rw [← hzget]
  exact ⟨hxbound, hylower, hyupper⟩


/-- At a local minimum column, a genuine strip path to the top has a first
hit of the upper or vertical boundary of the source rectangle. Every vertex
of the retained walk lies in that rectangle. -/
theorem horizontalStripLocalMinimum_firstExit
    (n m : ℕ) (ω : LatticeConfiguration) (k : ℤ)
    (hn : 0 < n) (hm : 0 < m)
    (hk : horizontalStripHeight n ω k ≤ n)
    (hlocal : ∀ l : ℤ, (l - k).natAbs ≤ m →
      horizontalStripHeight n ω k ≤ horizontalStripHeight n ω l) :
    ∃ (v : horizontalStripVertex n)
      (p : (horizontalStripOpenGraph n ω).Walk
        (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k)
          (Nat.le_trans hk (by omega))) v),
      (∀ z ∈ p.support,
        (z.val.1 - k).natAbs ≤ m ∧
        (horizontalStripHeight n ω k : ℤ) ≤ z.val.2 ∧
        z.val.2 ≤ (horizontalStripHeight n ω k + n : ℕ)) ∧
      (v.val.1 = k - m ∨ v.val.1 = k + m ∨
        v.val.2 = (horizontalStripHeight n ω k + n : ℕ)) := by
  classical
  obtain ⟨hkStrip, htop⟩ := horizontalStripHeight_spec n ω k
  obtain ⟨x, hwitness⟩ := htop
  obtain ⟨p⟩ := hwitness
  have houtside : ¬ ((x - k).natAbs < m ∧
      (2 * n : ℤ) < (horizontalStripHeight n ω k + n : ℤ)) := by
    intro hh
    have hcast : (2 * n : ℤ) < (horizontalStripHeight n ω k + n : ℤ) := hh.2
    omega
  have hexit := horizontalStripLocalMinimum_walk_firstExit
    n m ω k hn hm hk hlocal p houtside
  obtain ⟨i, hi, hsupport, hboundary⟩ := hexit
  refine ⟨p.getVert i, p.take i, ?_, ?_⟩
  · simpa using hsupport
  · exact hboundary

end PottsContinuity.FKC.Medial
