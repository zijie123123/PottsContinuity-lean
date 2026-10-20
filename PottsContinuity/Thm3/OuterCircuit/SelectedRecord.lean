module

public import PottsContinuity.Thm3.OuterCircuit.SourceEventEquivalence
public import PottsContinuity.Thm3.RSW.StoppingAverage

@[expose] public section

namespace PottsContinuity.OuterCircuit

open PottsContinuity.PD.FK
open PottsContinuity.RSW
open PottsContinuity.Exploration

noncomputable section

local instance outerCircuitSelectedRecordEdgeFintype (n : ℕ) :
    Fintype (lemma4AmbientGraph n).edgeSet := Fintype.ofFinite _

local instance outerCircuitSelectedRecordEdgeDecidableEq (n : ℕ) :
    DecidableEq (lemma4AmbientGraph n).edgeSet := Classical.decEq _

def outerCircuitMaximumCandidate {n : ℕ}
    (C : Configuration (lemma4AmbientGraph n)) :
    Option (OuterCircuitSelectorIndex n) :=
  envelopeMaxCandidate outerCircuitSelectorValid outerCircuitSelectorInside C

def outerCircuitSelectedObservationSet {n : ℕ} :
    Set (StoppingObservationRange (outerCircuitSelectorReveal (n := n))) :=
  {b | ∃ C : Configuration (lemma4AmbientGraph n),
    stoppingObservationMap (outerCircuitSelectorReveal (n := n)) C = b ∧
      C ∈ lemma4OuterAnnulusEvent n}

theorem lemma4OuterAnnulusEvent_observation_preimage {n : ℕ} :
    (stoppingObservationMap (outerCircuitSelectorReveal (n := n))) ⁻¹'
      outerCircuitSelectedObservationSet (n := n) = lemma4OuterAnnulusEvent n := by
  ext C
  change stoppingObservationMap (outerCircuitSelectorReveal (n := n)) C ∈
      outerCircuitSelectedObservationSet (n := n) ↔
    C ∈ lemma4OuterAnnulusEvent n
  constructor
  · rintro ⟨C', hmap, hC'⟩
    have hobs : stoppingObservation (outerCircuitSelectorReveal (n := n)) C' =
        stoppingObservation (outerCircuitSelectorReveal (n := n)) C :=
      congrArg Subtype.val hmap
    rcases Prod.mk.inj hobs with ⟨hreveal, hstates⟩
    obtain ⟨p, hp⟩ :=
      (lemma4OuterAnnulusEvent_iff_candidate_exists C').mp hC'
    have hindex : ∃ i : OuterCircuitSelectorIndex n,
        outerCircuitSelectorValid C' i := ⟨.inl p, hp⟩
    obtain ⟨i, hselect⟩ :=
      (envelopeMaxCandidate_exists_iff outerCircuitSelectorValid
        outerCircuitSelectorInside C').2 hindex
    have hselected := (envelopeMaxCandidate_spec outerCircuitSelectorValid
      outerCircuitSelectorInside C' i hselect).1
    cases i with
    | inl q =>
      have hq : outerCircuitCandidateValid C' q := hselected
      have hsupport : outerCircuitCandidateSupport q ⊆
          outerCircuitSelectorReveal (n := n) C' := by
        intro e he
        change e ∈ outerCircuitCandidateSupport q at he
        change e ∈ envelopeMaxRevealMap outerCircuitSelectorValid
          outerCircuitSelectorInside outerCircuitOutside C'
        simp only [envelopeMaxRevealMap, hselect, outerCircuitSelectorInside]
        exact outerCircuitCandidateSupport_subset_outside q he
      have hagree : candidateStatesAgree C' C
          (outerCircuitCandidateSupport q) := by
        intro e he
        have heR' := hsupport he
        have heR : e ∈ outerCircuitSelectorReveal (n := n) C := by
          simpa only [hreveal] using heR'
        have heq := congrArg
          (fun S : Finset (lemma4AmbientGraph n).edgeSet => e ∈ S) hstates
        have hiff : (e ∈ C' ∧ e ∈ outerCircuitSelectorReveal (n := n) C') ↔
            (e ∈ C ∧ e ∈ outerCircuitSelectorReveal (n := n) C) :=
          Iff.of_eq (by simpa only [Finset.mem_inter] using heq)
        exact ⟨fun hC' => (hiff.mp ⟨hC', heR'⟩).1,
          fun hC => (hiff.mpr ⟨hC, heR⟩).1⟩
      have hqC : outerCircuitCandidateValid C q :=
        (outerCircuitCandidateValid_eq_of_support_agreement C' C q hagree).mp hq
      exact (lemma4OuterAnnulusEvent_iff_candidate_exists C).2 ⟨q, hqC⟩
    | inr S => exact False.elim hselected
  · intro hC
    exact ⟨C, rfl, hC⟩

end
end PottsContinuity.OuterCircuit
