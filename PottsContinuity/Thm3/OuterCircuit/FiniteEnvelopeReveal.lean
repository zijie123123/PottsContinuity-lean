module

public import PottsContinuity.Thm3.OuterCircuit.FiniteEnvelopeJoin
public import PottsContinuity.Exploration.FiniteEnvelopeMaxSelector

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Exploration

noncomputable section

theorem outerCircuitCandidateSupport_open_of_valid {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (i : OuterCircuitPolygonCode n)
    (hvalid : outerCircuitCandidateValid C i)
    {e : (lemma4AmbientGraph n).edgeSet}
    (he : e ∈ outerCircuitCandidateSupport i) : e ∈ C := by
  have hindex : ∃ j : ZMod (i.1.val + 3), e = outerCircuitBoundaryEdge i j := by
    simpa [outerCircuitCandidateSupport] using he
  rcases hindex with ⟨j, rfl⟩
  exact hvalid.2.2 j

theorem outerCircuitSelectorJoin_valid_of_valid {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n))
    (i j : OuterCircuitSelectorIndex n)
    (hi : outerCircuitSelectorValid C i)
    (hj : outerCircuitSelectorValid C j) :
    outerCircuitSelectorValid C (outerCircuitSelectorJoin i j) := by
  cases i with
  | inl p =>
    cases j with
    | inl q =>
      have hpShape : outerCircuitCandidateShape p :=
        outerCircuitCandidateValid_shape C p hi
      have hqShape : outerCircuitCandidateShape q :=
        outerCircuitCandidateValid_shape C q hj
      have hgood := outerCircuitSelectorJoin_good_of_shapes
        (.inl p) (.inl q) hpShape hqShape
      cases hjoin : outerCircuitSelectorJoin (.inl p) (.inl q) with
      | inl r =>
        rw [hjoin] at hgood
        have hrShape : outerCircuitCandidateShape r := by
          simpa [outerCircuitSelectorShape] using hgood.1
        have hsupport : outerCircuitCandidateSupport r ⊆
            outerCircuitCandidateSupport p ∪ outerCircuitCandidateSupport q := by
          simpa [outerCircuitSelectorSupport] using hgood.2.2.1
        refine ⟨hrShape.1, ⟨hrShape.2, ?_⟩⟩
        intro t
        have hedge : outerCircuitBoundaryEdge r t ∈ outerCircuitCandidateSupport r :=
          outerCircuitBoundaryEdge_mem_support r t
        have hinput := hsupport hedge
        rcases Finset.mem_union.mp hinput with hleft | hright
        · exact outerCircuitCandidateSupport_open_of_valid C p hi hleft
        · exact outerCircuitCandidateSupport_open_of_valid C q hj hright
      | inr S =>
        rw [hjoin] at hgood
        exact False.elim (by simpa [outerCircuitSelectorShape] using hgood.1)
    | inr S => exact False.elim hj
  | inr S => exact False.elim hi

def outerCircuitSelectorReveal {n : ℕ} :
    RevealMap (G := lemma4AmbientGraph n) :=
  envelopeMaxRevealMap outerCircuitSelectorValid outerCircuitSelectorInside
    outerCircuitOutside

theorem outerCircuitSelectorReveal_stable {n : ℕ} :
    ∀ C C', C' ∩ outerCircuitSelectorReveal (n := n) C =
      C ∩ outerCircuitSelectorReveal (n := n) C →
      outerCircuitSelectorReveal (n := n) C' = outerCircuitSelectorReveal (n := n) C := by
  exact envelopeMaxRevealMap_stable outerCircuitSelectorValid
    outerCircuitSelectorInside outerCircuitSelectorSupport outerCircuitOutside
    outerCircuitSelectorJoin
    (by
      intro C C' i hagree
      cases i with
      | inl p => exact outerCircuitCandidateValid_eq_of_support_agreement C C' p hagree
      | inr S => exact Iff.rfl)
    (by
      intro i
      cases i with
      | inl p =>
        simpa [outerCircuitSelectorSupport, outerCircuitSelectorInside] using
          outerCircuitCandidateSupport_subset_outside p
      | inr S => simp [outerCircuitSelectorSupport])
    outerCircuitSelectorJoin_valid_of_valid
    (by
      let : DecidableEq (OuterCircuitHostVertex n) :=
        outerCircuitSelectorVertexDecidableEq
      intro i j x hx
      have hx' : x ∈ outerCircuitSelectorInside i ∨
          x ∈ outerCircuitSelectorInside j := by
        simpa only [Finset.mem_union] using hx
      have hsource : x ∈ outerCircuitSelectorInside i ∪
          outerCircuitSelectorInside j := by
        simpa only [Finset.mem_union] using hx'
      exact outerCircuitSelectorJoin_inside i j hsource)
    outerCircuitSelectorJoin_support_outside

end
end PottsContinuity.OuterCircuit
