-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCanonicalReturnArcSplit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCommonExteriorReturn
public import PottsContinuity.FKC.FiniteFK.SimplePathEdgeSetUniqueness
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The recursive vertical walk splits at its intermediate lattice height. -/
theorem slitReturnVerticalUpWalk_split (x y : ℤ) (d : ℕ) :
    (slitReturnVerticalUpWalk x y (d + 1)).copy (by simp) (by
      congr 1
      push_cast
      ring) =
      (slitReturnVerticalUpWalk x y d).append
        (slitReturnVerticalUpWalk x (y + (d : ℤ)) 1) := by
  apply SimpleGraph.Walk.ext_support
  simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_append]
  induction d generalizing y with
  | zero => simp [slitReturnVerticalUpWalk]
  | succ d ih =>
      have hleft : (slitReturnVerticalUpWalk x y (d + 2)).support =
          (x, y) :: (slitReturnVerticalUpWalk x (y + 1) (d + 1)).support := by
        simp [slitReturnVerticalUpWalk]
      have hpref : (slitReturnVerticalUpWalk x y (d + 1)).support =
          (x, y) :: (slitReturnVerticalUpWalk x (y + 1) d).support := by
        simp [slitReturnVerticalUpWalk]
      have hlast : (slitReturnVerticalUpWalk x (y + 1 + (d : ℤ)) 1).support.tail =
          [(x, y + (d : ℤ) + 2)] := by
        simp only [slitReturnVerticalUpWalk, SimpleGraph.Walk.support_copy,
          SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
        congr 1
        ring_nf
      rw [hleft, hpref]
      rw [ih (y + 1)]
      have hy : y + ((d + 1 : ℕ) : ℤ) = y + 1 + (d : ℤ) := by
        push_cast
        ring
      rw [hy, hlast]
      rfl

/-- The literal upward path along the wired arc from `t` to its top endpoint. -/
def slitBoxArcVerticalWalk (n : ℕ) (t : SlitBoxVertex n)
    (ht : t ∈ slitBoxWiredArc n) :
    squareLattice.Walk t.val (slitBoxTopArcVertex n).val := by
  let k := t.val.2.toNat
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  have hk : k ≤ n := by
    have hk' : (k : ℤ) ≤ (n : ℤ) := by
      rw [Int.toNat_of_nonneg htArc.2.1]
      exact htArc.2.2
    exact_mod_cast hk'
  have hstart : ((0 : ℤ), (k : ℤ)) = t.val := by
    apply Prod.ext
    · exact htArc.1.symm
    · exact Int.toNat_of_nonneg htArc.2.1
  have htop : ((0 : ℤ), (k : ℤ) + ((n - k : ℕ) : ℤ)) =
      (slitBoxTopArcVertex n).val := by
    apply Prod.ext
    · rfl
    · simp only [slitBoxTopArcVertex]
      rw [Nat.cast_sub hk]
      omega
  exact (slitReturnVerticalUpWalk 0 (k : ℤ) (n-k)).copy hstart htop

theorem slitBoxArcVerticalWalk_isPath (n : ℕ) (t : SlitBoxVertex n)
    (ht : t ∈ slitBoxWiredArc n) :
    (slitBoxArcVerticalWalk n t ht).IsPath := by
  simp only [slitBoxArcVerticalWalk, SimpleGraph.Walk.isPath_copy]
  exact slitReturnVerticalUpWalk_isPath 0 (t.val.2.toNat : ℤ)
    (n - t.val.2.toNat)

theorem slitBoxArcVerticalWalk_support_in_wiredArc (n : ℕ)
    (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    ∀ x ∈ (slitBoxArcVerticalWalk n t ht).support,
      ∃ v : SlitBoxVertex n, v ∈ slitBoxWiredArc n ∧ v.val = x := by
  intro x hx
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  have hx' : x ∈ (slitReturnVerticalUpWalk 0 (t.val.2.toNat : ℤ)
      (n - t.val.2.toNat)).support := by
    simpa only [slitBoxArcVerticalWalk, SimpleGraph.Walk.support_copy] using hx
  obtain ⟨hx0, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds 0
    (t.val.2.toNat : ℤ) (n - t.val.2.toNat) hx'
  have hxlo : 0 ≤ x.2 := by
    rw [Int.toNat_of_nonneg htArc.2.1] at hlo
    exact le_trans (by omega) hlo
  have hxn : x.2 ≤ (n : ℤ) := by
    rw [Int.toNat_of_nonneg htArc.2.1] at hhi
    have hk : t.val.2.toNat ≤ n := by
      have hi : (t.val.2.toNat : ℤ) ≤ n := by
        rw [Int.toNat_of_nonneg htArc.2.1]
        exact htArc.2.2
      exact_mod_cast hi
    have hcast : ((n - t.val.2.toNat : ℕ) : ℤ) =
        (n : ℤ) - (t.val.2.toNat : ℤ) := by rw [Nat.cast_sub hk]
    rw [hcast] at hhi
    omega
  let v : SlitBoxVertex n := ⟨x, by
    rw [mem_latticeRectangle]
    push_cast
    constructor
    · constructor <;> omega
    · constructor <;> omega⟩
  refine ⟨v, ?_, rfl⟩
  rw [mem_slitBoxWiredArc_iff]
  exact ⟨hx0, hxlo, hxn⟩

/-- The canonical return first follows the literal wired-arc vertical segment,
then follows the same canonical top return. -/
theorem slitBoxCanonicalReturnWalk_eq_arcVertical_append_topReturn
    (n : ℕ) (u : SlitBoxVertex n) (huY : u.val.2 = -(n : ℤ))
    (huX : 0 ≤ u.val.1) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n) :
    slitBoxCanonicalReturnWalk n u huY huX t ht =
      (slitBoxArcVerticalWalk n t ht).append
        (slitBoxCanonicalReturnWalk n u huY huX
          (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)) := by
  have htArc := (mem_slitBoxWiredArc_iff n t).mp ht
  let k := t.val.2.toNat
  have hk : k ≤ n := by
    have hki : (k : ℤ) ≤ n := by
      dsimp [k]
      rw [Int.toNat_of_nonneg htArc.2.1]
      exact htArc.2.2
    exact_mod_cast hki
  have hmid : (k : ℤ) + ((n-k : ℕ) : ℤ) = n := by
    rw [Nat.cast_sub hk]
    dsimp [k]
    rw [Int.toNat_of_nonneg htArc.2.1]
    omega
  have hlen : n + 1 - k = (n-k) + 1 := by omega
  have hmidTail : (slitReturnVerticalUpWalk 0 (k + ((n-k : ℕ) : ℤ)) 1).support.tail =
      [((0 : ℤ), (n+1 : ℤ))] := by
    simp only [slitReturnVerticalUpWalk, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.tail_cons]
    simp [hmid]
  have hsplitSupport :
      (slitReturnVerticalUpWalk 0 (k : ℤ) (n+1-k)).support =
        (slitReturnVerticalUpWalk 0 (k : ℤ) (n-k)).support ++
          [((0 : ℤ), (n+1 : ℤ))] := by
    rw [hlen]
    have h := congrArg SimpleGraph.Walk.support
      (slitReturnVerticalUpWalk_split 0 (k : ℤ) (n-k))
    have h' : (slitReturnVerticalUpWalk 0 (k : ℤ) (n-k+1)).support =
        (slitReturnVerticalUpWalk 0 (k : ℤ) (n-k)).support ++
          (slitReturnVerticalUpWalk 0 (k + ((n-k : ℕ) : ℤ)) 1).support.tail := by
      simpa only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_append] using h
    rw [hmidTail] at h'
    exact h'
  have htopLen : n + 1 - n = 1 := by omega
  have htopSupport : (slitReturnVerticalUpWalk 0 (n : ℤ) 1).support =
      [((0 : ℤ), (n : ℤ)), ((0 : ℤ), (n+1 : ℤ))] := by
    simp only [slitReturnVerticalUpWalk, SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]
  apply SimpleGraph.Walk.ext_support
  simp only [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_copy,
    slitBoxCanonicalReturnWalk, slitBoxArcVerticalWalk]
  unfold slitBoxExteriorReturnWalkNat
  dsimp only
  simp only [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_append]
  rw [hsplitSupport]
  simp only [slitBoxTopArcVertex, Int.toNat_natCast]
  rw [htopLen, htopSupport]
  simp [List.append_assoc, k]

end PottsContinuity.FKC.FiniteFK
