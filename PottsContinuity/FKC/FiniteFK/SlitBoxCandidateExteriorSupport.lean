-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxCandidateExteriorSupport.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxCandidateExteriorNeighbors
public import PottsContinuity.FKC.FiniteFK.SlitBoxCommonExteriorReturn
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The support of a canonical return outside the literal slit box lies on
its common top return, independently of the chosen arc endpoint. -/
theorem slitBoxCanonicalReturnWalk_outside_support_subset_top
    (n : ℕ) (u : SlitBoxVertex n) (huY : u.val.2 = -(n : ℤ))
    (huX : 0 ≤ u.val.1) (t : SlitBoxVertex n) (ht : t ∈ slitBoxWiredArc n)
    {z : LatticeVertex}
    (hz : z ∈ (slitBoxCanonicalReturnWalk n u huY huX t ht).support)
    (hzOut : z ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) :
    z ∈ (slitBoxCanonicalReturnWalk n u huY huX (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).support := by
  have ha : u.val.1.toNat ≤ n := by
    have hbox := u.property
    rw [mem_latticeRectangle] at hbox
    have hmax : -(n : ℤ) + (2*n : ℕ) = (n : ℤ) := by push_cast; omega
    have hcast : (u.val.1.toNat : ℤ) ≤ (n : ℤ) := by
      rw [Int.toNat_of_nonneg huX]
      rw [hmax] at hbox
      exact hbox.1.2
    exact_mod_cast hcast
  have hk : t.val.2.toNat ≤ n := by
    have harc := (mem_slitBoxWiredArc_iff n t).mp ht
    have hcast : (t.val.2.toNat : ℤ) ≤ (n : ℤ) := by
      rw [Int.toNat_of_nonneg harc.2.1]
      exact harc.2.2
    exact_mod_cast hcast
  have hzNat : z ∈ (slitBoxExteriorReturnWalkNat n u.val.1.toNat t.val.2.toNat ha hk).val.support := by
    simpa [slitBoxCanonicalReturnWalk, SimpleGraph.Walk.support_copy] using hz
  have htop : z ∈ (slitBoxExteriorReturnWalkNat n u.val.1.toNat n ha (by omega)).val.support := by
    unfold slitBoxExteriorReturnWalkNat at hzNat ⊢
    dsimp only at hzNat ⊢
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hzNat ⊢
    rcases hzNat with h1 | hrest
    · obtain ⟨hx, hlo, hhi⟩ := slitReturnVerticalUpWalk_support_bounds 0
        (t.val.2.toNat : ℤ) (n + 1 - t.val.2.toNat) (by
          simpa [SimpleGraph.Walk.support_copy] using h1)
      have hzY : z.2 = (n + 1 : ℤ) := by
        by_contra hneq
        apply hzOut
        rw [mem_latticeRectangle]
        push_cast
        constructor
        · constructor <;> omega
        · constructor <;> omega
      have hlen : n + 1 - n = 1 := by omega
      have htopMem : ((0 : ℤ), (n + 1 : ℤ)) ∈
          (slitReturnVerticalUpWalk 0 (n : ℤ) (n + 1 - n)).support := by
        have hend := (slitReturnVerticalUpWalk 0 (n : ℤ) (n + 1 - n)).end_mem_support
        simpa [hlen] using hend
      have hzEq : z = ((0 : ℤ), (n + 1 : ℤ)) := Prod.ext hx hzY
      rw [hzEq]
      exact Or.inl (by simpa [SimpleGraph.Walk.support_copy] using htopMem)
    · rcases hrest with h2 | hrest
      · exact Or.inr (Or.inl (by simpa [SimpleGraph.Walk.support_copy] using h2))
      · rcases hrest with h3 | hrest
        · exact Or.inr (Or.inr (Or.inl (by
            simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using h3)))
        · rcases hrest with h4 | h5
          · exact Or.inr (Or.inr (Or.inr (Or.inl (by
              simpa [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_copy] using h4))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (by
              simpa [SimpleGraph.Walk.support_copy] using h5))))
  change z ∈ ((slitBoxExteriorReturnWalkNat n u.val.1.toNat n ha (by omega)).val.copy
    (by change ((0 : ℤ), (n : ℤ)) = ((0 : ℤ), (n : ℤ)); rfl) (by
      apply Prod.ext
      · exact Int.toNat_of_nonneg huX
      · exact huY.symm)).support
  have hcopy := SimpleGraph.Walk.support_copy
    (slitBoxExteriorReturnWalkNat n u.val.1.toNat n ha (by omega)).val
    (by change ((0 : ℤ), (n : ℤ)) = ((0 : ℤ), (n : ℤ)); rfl)
    (by
      apply Prod.ext
      · exact Int.toNat_of_nonneg huX
      · exact huY.symm)
  exact hcopy.symm ▸ htop

/-- Every candidate-cycle vertex outside the literal box lies on the common
top return for the same bottom vertex. -/
theorem slitBoxFirstHitCandidateCycle_outside_support_subset_top
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1)
    (p : SlitBoxFirstHitBaseCandidates n u) {z : LatticeVertex}
    (hz : z ∈ (slitBoxFirstHitCandidateCycle n hn u huY huX p).support)
    (hzOut : z ∉ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n)) :
    z ∈ (slitBoxCanonicalReturnWalk n u huY huX (slitBoxTopArcVertex n) (slitBoxTopArcVertex_mem_wiredArc n)).support := by
  classical
  let : Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
  let A : Configuration (slitBoxGraph n) := Finset.univ
  have hA : A = Finset.univ := rfl
  let f : slitBoxGraph n →g openGraph (slitBoxGraph n) A := {
    toFun := id
    map_rel' := by
      intro x y hxy
      apply (openGraph_adj (slitBoxGraph n) A x y).2
      change s(x, y) ∈ Subtype.val '' (↑A : Set (slitBoxGraph n).edgeSet)
      rw [hA]
      refine ⟨⟨s(x, y), (slitBoxGraph n).mem_edgeSet.mpr hxy⟩, ?_, rfl⟩
      exact Finset.mem_univ _ }
  let preWalk := ((p.val.2 : (slitBoxGraph n).Walk u p.val.1).map f).map
    (slitBoxOpenGraphToSquareLatticeHom n A)
  let ret := slitBoxCanonicalReturnWalk n u huY huX p.val.1 p.property.1
  have hcycle : slitBoxFirstHitCandidateCycle n hn u huY huX p = preWalk.append ret := by
    rfl
  have hprefixBox : ∀ x ∈ preWalk.support,
      x ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2*n) (2*n) := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    rcases List.mem_map.mp hx with ⟨v, hv, rfl⟩
    rw [SimpleGraph.Walk.support_map] at hv
    rcases List.mem_map.mp hv with ⟨w, hw, rfl⟩
    simp
  have hz' : z ∈ preWalk.support ∨ z ∈ ret.support := by
    rw [hcycle] at hz
    have hsupp := SimpleGraph.Walk.support_append preWalk ret
    have hzMem : z ∈ preWalk.support ++ ret.support.tail := hsupp ▸ hz
    rw [List.mem_append] at hzMem
    rcases hzMem with hpref | htail
    · exact Or.inl hpref
    · exact Or.inr (List.mem_of_mem_tail htail)
  rcases hz' with hpref | hret
  · exact (hzOut (hprefixBox z hpref)).elim
  · exact slitBoxCanonicalReturnWalk_outside_support_subset_top n u huY huX
      p.val.1 p.property.1 hret hzOut

end PottsContinuity.FKC.FiniteFK
