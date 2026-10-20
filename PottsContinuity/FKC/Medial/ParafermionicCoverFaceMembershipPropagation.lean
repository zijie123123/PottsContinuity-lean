-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverFaceMembershipPropagation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverFaceCoefficientMembership
public import PottsContinuity.FKC.Medial.ParafermionicCoverSimpleCycleFilling
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC

private theorem coverFace_leftCorner_eq_up (x y k : ℤ)
    (hnot : (x,y) ≠ (0,-1)) :
    parafermionicCoverFaceRightUpLeftLift x y k = ((x,y+1),k) := by
  have hnet : (if x = 0 ∧ y < 0 then (1 : ℤ) else 0) +
      (if x = 0 ∧ y+1 < 0 then (-1 : ℤ) else 0) = 0 := by
    by_cases hx : x = 0
    · by_cases hy : y < 0
      · have hne : y ≠ -1 := by
          intro h
          apply hnot
          simp [hx, h]
        have hy' : y+1 < 0 := by omega
        simp [hx, hy, hy']
      · simp [hx, hy]; omega
    · simp [hx]
  rw [parafermionicCoverFaceRightUpLeftLift_formula]
  apply congrArg (fun t : ℤ => ((x,y+1),t))
  calc
    k + (if x = 0 ∧ y < 0 then 1 else 0) +
        (if x = 0 ∧ y+1 < 0 then -1 else 0) =
        k + ((if x = 0 ∧ y < 0 then 1 else 0) +
          (if x = 0 ∧ y+1 < 0 then -1 else 0)) := by ring
    _ = k := by rw [hnet]; simp

private theorem coverFace_verticalRight_shift_eq (x y : ℤ)
    (hnot : (x,y) ≠ (0,-1)) :
    (if x = 0 ∧ y < 0 then (1 : ℤ) else 0) =
      (if x = 0 ∧ y+1 < 0 then (1 : ℤ) else 0) := by
  by_cases hx : x = 0
  · by_cases hy : y < 0
    · have hne : y ≠ -1 := by
        intro h
        apply hnot
        simp [hx, h]
      have hy' : y+1 < 0 := by omega
      simp [hx, hy, hy']
    · simp [hx, hy]; omega
  · simp [hx]

/- Neighboring lower-left vertices of retained ordinary faces identify an
actual common lifted side. -/
theorem parafermionicCoverFiniteFaces_adjacent_base_share_darts {n : ℕ}
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : parafermionicCoverGraph.Adj i.1 j.1) :
    ∃ a b : ParafermionicCoverVertex,
      (a,b) ∈ parafermionicCoverFiniteFaceDarts i.1 ∧
      (b,a) ∈ parafermionicCoverFiniteFaceDarts j.1 ∧
      (a = i.1 ∨ b = i.1 ∨ a = j.1 ∨ b = j.1) := by
  rcases i with ⟨⟨⟨x,y⟩,k⟩, hi⟩
  rcases j with ⟨⟨⟨x',y'⟩,k'⟩, hj⟩
  have hnot_i : (x,y) ≠ (0,-1) := by
    rcases (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hi with
      ⟨_,_,_,_,_,_, hnot, _⟩
    exact hnot
  have hnot_j : (x',y') ≠ (0,-1) := by
    rcases (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x',y'),k')).mp hj with
      ⟨_,_,_,_,_,_, hnot, _⟩
    exact hnot
  have hc := (parafermionicCoverGraph_adj_iff_cases _ _).mp hij
  simp only [parafermionicCoverAdjCases] at hc
  rcases hc with h | h | h | h | h | h | h | h
  · rcases h with ⟨rfl, hy, rfl⟩
    subst y'
    have hleft := coverFace_leftCorner_eq_up x y k hnot_i
    have hshift := coverFace_verticalRight_shift_eq x y hnot_i
    refine ⟨parafermionicCoverFaceRightUpLift x y k,
      parafermionicCoverFaceRightUpLeftLift x y k, ?_, ?_, ?_⟩
    · simp [parafermionicCoverFiniteFaceDarts]
    · simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
        Finset.mem_singleton]
      left
      change (parafermionicCoverFaceRightUpLeftLift x y k,
          parafermionicCoverFaceRightUpLift x y k) =
        (((x,y+1),k), parafermionicCoverFaceRightLift x (y+1) k)
      rw [hleft, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula]
      exact congrArg (fun t : ℤ => (((x,y+1),k), ((x+1,y+1),k+t))) hshift
    · rw [hleft]
      exact Or.inr (Or.inr (Or.inr rfl))
  · rcases h with ⟨rfl, hy, rfl⟩
    have hleft := coverFace_leftCorner_eq_up x y' k hnot_j
    have hshift := coverFace_verticalRight_shift_eq x y' hnot_j
    refine ⟨((x,y),k), parafermionicCoverFaceRightLift x y k, ?_, ?_, ?_⟩
    · simp [parafermionicCoverFiniteFaceDarts]
    · simp only [parafermionicCoverFiniteFaceDarts, Finset.mem_insert,
        Finset.mem_singleton]
      right
      right
      left
      change (parafermionicCoverFaceRightLift x y k, ((x,y),k)) =
        (parafermionicCoverFaceRightUpLift x y' k,
          parafermionicCoverFaceRightUpLeftLift x y' k)
      rw [hleft, hy, parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula]
      simp [hshift, hy]
    · exact Or.inl rfl
  · rcases h with ⟨hy, hk, hx, hx0⟩
    subst y'; subst k'; subst x'
    refine ⟨parafermionicCoverFaceRightLift x y k,
      parafermionicCoverFaceRightUpLift x y k, ?_, ?_, ?_⟩ <;>
      simp_all [parafermionicCoverFiniteFaceDarts,
        parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula,
        parafermionicCoverFaceRightUpLeftLift_formula]; omega
  · rcases h with ⟨hy, hk, hx, hx0⟩
    refine ⟨parafermionicCoverFaceRightUpLeftLift x y k,
      ((x,y),k), ?_, ?_, ?_⟩ <;>
      simp_all [parafermionicCoverFiniteFaceDarts,
        parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula,
        parafermionicCoverFaceRightUpLeftLift_formula]; omega
  · rcases h with ⟨hx, hx', hy, hy0, hk⟩
    subst x; subst x'; subst y'; subst k'
    refine ⟨parafermionicCoverFaceRightLift 0 y k,
      parafermionicCoverFaceRightUpLift 0 y k, ?_, ?_, ?_⟩ <;>
      simp_all [parafermionicCoverFiniteFaceDarts,
        parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula,
        parafermionicCoverFaceRightUpLeftLift_formula]
  · rcases h with ⟨hx, hx', hy, hy0, hk⟩
    refine ⟨parafermionicCoverFaceRightUpLeftLift x y k,
      ((x,y),k), ?_, ?_, ?_⟩ <;>
      simp_all [parafermionicCoverFiniteFaceDarts,
        parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula,
        parafermionicCoverFaceRightUpLeftLift_formula]
  · rcases h with ⟨hx, hx', hy, hyneg, hsheet⟩
    subst x; subst x'; subst y'
    refine ⟨parafermionicCoverFaceRightLift 0 y k,
      parafermionicCoverFaceRightUpLift 0 y k, ?_, ?_, ?_⟩ <;>
      simp_all [parafermionicCoverFiniteFaceDarts,
        parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula,
        parafermionicCoverFaceRightUpLeftLift_formula]
  · rcases h with ⟨hx, hx', hy, hyneg, hsheet⟩
    refine ⟨parafermionicCoverFaceRightUpLeftLift x y k,
      ((x,y),k), ?_, ?_, ?_⟩ <;>
      simp_all [parafermionicCoverFiniteFaceDarts,
        parafermionicCoverFaceRightLift_formula,
        parafermionicCoverFaceRightUpLift_formula,
        parafermionicCoverFaceRightUpLeftLift_formula]

/-- If neither lower-left face vertex lies on a simple cycle, adjacent retained
ordinary faces have the same membership in its actual finite filling. -/
theorem parafermionicCoverSimpleCycleFillingSet_mem_iff_of_adjacent_base_absent
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
    (i j : ParafermionicCoverFiniteFaceTopIndex n)
    (hij : parafermionicCoverGraph.Adj i.1 j.1)
    (habs_i : ∀ v ∈ p.support, v.1 ≠ i.1)
    (habs_j : ∀ v ∈ p.support, v.1 ≠ j.1) :
    (i ∈ parafermionicCoverSimpleCycleFillingSet hn p hp ↔
      j ∈ parafermionicCoverSimpleCycleFillingSet hn p hp) := by
  classical
  obtain ⟨a,b, hforward, hbackward, hendpoint⟩ :=
    parafermionicCoverFiniteFaces_adjacent_base_share_darts i j hij
  have hend := parafermionicCoverFiniteFaceDart_endpoints_mem n i.1 i.2 hforward
  let va : ParafermionicCoverBoxVertex n := ⟨a,hend.1⟩
  let vb : ParafermionicCoverBoxVertex n := ⟨b,hend.2⟩
  have hforward' : (va.1,vb.1) ∈ parafermionicCoverFiniteFaceDarts i.1 := by
    simpa [va,vb] using hforward
  have hbackward' : (vb.1,va.1) ∈ parafermionicCoverFiniteFaceDarts j.1 := by
    simpa [va,vb] using hbackward
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  have hspec := parafermionicCoverSimpleCycleFillingSet_spec hn p hp
  have hnotedge : s(va,vb) ∉ p.edges := by
    intro hedge
    have hfst := p.fst_mem_support_of_mem_edges hedge
    have hsnd := p.snd_mem_support_of_mem_edges hedge
    rcases hendpoint with hia | hib | hja | hjb
    · exact (habs_i va hfst) (by simpa [va] using hia)
    · exact (habs_i vb hsnd) (by simpa [vb] using hib)
    · exact (habs_j va hfst) (by simpa [va] using hja)
    · exact (habs_j vb hsnd) (by simpa [vb] using hjb)
  have hzero : parafermionicCoverFaceBoundaryCoefficient S va vb = 0 := by
    by_contra hne
    have hnonzero : parafermionicCoverFaceBoundaryCoefficient S va vb ≠ 0 := by
      intro heq
      exact hne heq
    exact hnotedge ((hspec.2.2 va vb).mp hnonzero)
  have hmem := parafermionicCoverFaceBoundaryCoefficient_eq_zero_iff_owner_mem_iff
    S i j va vb hforward' hbackward'
  simpa [S] using hmem.mp hzero

end PottsContinuity.FKC.Medial
