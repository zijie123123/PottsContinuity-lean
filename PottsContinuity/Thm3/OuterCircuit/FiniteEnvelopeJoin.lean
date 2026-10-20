module

public import PottsContinuity.Thm3.OuterCircuit.JoinedEnvelopeCode

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK

noncomputable section

local instance outerCircuitSelectorVertexDecidableEq {n : ℕ} :
    DecidableEq (OuterCircuitHostVertex n) :=
  PottsContinuity.Exploration.envelopeMaxIndexDecidableEq

def outerCircuitSelectorShape {n : ℕ} (i : OuterCircuitSelectorIndex n) : Prop :=
  match i with
  | .inl p => outerCircuitCandidateShape p
  | .inr _ => False

def outerCircuitSelectorJoinGood {n : ℕ}
    (i j k : OuterCircuitSelectorIndex n) : Prop :=
  outerCircuitSelectorShape k ∧
    outerCircuitSelectorInside i ∪ outerCircuitSelectorInside j ⊆
      outerCircuitSelectorInside k ∧
    outerCircuitSelectorSupport k ⊆
      outerCircuitSelectorSupport i ∪ outerCircuitSelectorSupport j ∧
    outerCircuitSelectorSupport k ⊆
      outerCircuitOutside (outerCircuitSelectorInside i)

noncomputable def outerCircuitSelectorJoinSet {n : ℕ}
    (i j : OuterCircuitSelectorIndex n) : Finset (OuterCircuitSelectorIndex n) := by
  classical
  exact Finset.univ.filter (outerCircuitSelectorJoinGood i j)

theorem outerCircuitSelectorJoinSet_nonempty {n : ℕ}
    (i j : OuterCircuitSelectorIndex n)
    (hi : outerCircuitSelectorShape i) (hj : outerCircuitSelectorShape j) :
    (outerCircuitSelectorJoinSet i j).Nonempty := by
  classical
  cases i with
  | inl p =>
    cases j with
    | inl q =>
      obtain ⟨r, hrShape, hrInside, hrSupport⟩ :=
        outerCircuitEnvelopeCode_exists p q hi hj
      have hrOutside := outerCircuitCandidateSupport_subset_outside_of_region_subset
        p r (Finset.subset_union_left.trans hrInside)
      refine ⟨.inl r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      refine ⟨hrShape, ?_, ?_, ?_⟩
      · simpa [outerCircuitSelectorInside] using hrInside
      · simpa [outerCircuitSelectorSupport] using hrSupport
      · simpa [outerCircuitSelectorInside, outerCircuitSelectorSupport] using hrOutside
    | inr S => exact False.elim hj
  | inr S => exact False.elim hi

noncomputable def outerCircuitSelectorJoin {n : ℕ}
    (i j : OuterCircuitSelectorIndex n) : OuterCircuitSelectorIndex n := by
  classical
  exact if h : outerCircuitSelectorShape i ∧ outerCircuitSelectorShape j then
    (outerCircuitSelectorJoinSet i j).min'
      (outerCircuitSelectorJoinSet_nonempty i j h.1 h.2)
  else .inr (outerCircuitSelectorInside i ∪ outerCircuitSelectorInside j)

theorem outerCircuitSelectorJoin_good_of_shapes {n : ℕ}
    (i j : OuterCircuitSelectorIndex n)
    (hi : outerCircuitSelectorShape i) (hj : outerCircuitSelectorShape j) :
    outerCircuitSelectorJoinGood i j (outerCircuitSelectorJoin i j) := by
  classical
  unfold outerCircuitSelectorJoin
  split
  · next h =>
      let S := outerCircuitSelectorJoinSet i j
      have hS := outerCircuitSelectorJoinSet_nonempty i j h.1 h.2
      have hmem : S.min' hS ∈ S := Finset.min'_mem S hS
      have hgood : outerCircuitSelectorJoinGood i j (S.min' hS) := by
        have hmem' : S.min' hS ∈ outerCircuitSelectorJoinSet i j := by
          simpa [S] using hmem
        exact (Finset.mem_filter.mp hmem').2
      simpa [S] using hgood
  · next h => exact False.elim (h ⟨hi, hj⟩)

theorem outerCircuitSelectorJoin_inside {n : ℕ}
    (i j : OuterCircuitSelectorIndex n) :
    outerCircuitSelectorInside i ∪ outerCircuitSelectorInside j ⊆
      outerCircuitSelectorInside (outerCircuitSelectorJoin i j) := by
  classical
  by_cases h : outerCircuitSelectorShape i ∧ outerCircuitSelectorShape j
  · exact (outerCircuitSelectorJoin_good_of_shapes i j h.1 h.2).2.1
  · simp [outerCircuitSelectorJoin, h, outerCircuitSelectorInside]

theorem outerCircuitSelectorJoin_support_outside {n : ℕ}
    (i j : OuterCircuitSelectorIndex n) :
    outerCircuitSelectorSupport (outerCircuitSelectorJoin i j) ⊆
      outerCircuitOutside (outerCircuitSelectorInside i) := by
  classical
  by_cases h : outerCircuitSelectorShape i ∧ outerCircuitSelectorShape j
  · exact (outerCircuitSelectorJoin_good_of_shapes i j h.1 h.2).2.2.2
  · simp [outerCircuitSelectorJoin, h, outerCircuitSelectorSupport]

end
end PottsContinuity.OuterCircuit
