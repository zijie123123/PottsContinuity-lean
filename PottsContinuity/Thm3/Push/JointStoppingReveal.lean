module

public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance jointRevealEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance jointRevealRemainingFintype (R : Configuration G) :
    Fintype (RemainingConfiguration G R) := Fintype.ofFinite _

/-- The common exploration records the original states read by either reveal. -/
def jointReveal (r t : RevealMap (G := G)) : RevealMap (G := G) :=
  fun A => r A ∪ t A

omit [Finite V] in
/-- Agreement on a larger set of original bonds implies agreement on each
smaller recorded set, including its closed states. -/
theorem recorded_agreement_of_subset (A B R S : Configuration G) (hRS : R ⊆ S)
    (h : B ∩ S = A ∩ S) : B ∩ R = A ∩ R := by
  ext e
  have he := Finset.ext_iff.mp h e
  simp only [Finset.mem_inter] at he ⊢
  constructor
  · rintro ⟨hb, hr⟩
    exact ⟨(he.mp ⟨hb, hRS hr⟩).1, hr⟩
  · rintro ⟨ha, hr⟩
    exact ⟨(he.mpr ⟨ha, hRS hr⟩).1, hr⟩

omit [Finite V] in
/-- Two stable explorations, possibly overlapping, form one stable exploration. -/
theorem jointReveal_stable (r t : RevealMap (G := G))
    (hr : ∀ A B, B ∩ r A = A ∩ r A → r B = r A)
    (ht : ∀ A B, B ∩ t A = A ∩ t A → t B = t A)
    (A B : Configuration G)
    (h : B ∩ jointReveal r t A = A ∩ jointReveal r t A) :
    jointReveal r t B = jointReveal r t A := by
  have hR := hr A B (recorded_agreement_of_subset A B (r A) _ Finset.subset_union_left h)
  have hT := ht A B (recorded_agreement_of_subset A B (t A) _ Finset.subset_union_right h)
  simp only [jointReveal, hR, hT]

omit [Finite V] in
/-- Conditioning on the common record is exactly conditioning on BOTH
individual records. Disjointness of the revealed sets is unnecessary. -/
theorem jointReveal_recordEvent (r t : RevealMap (G := G))
    (hr : ∀ A B, B ∩ r A = A ∩ r A → r B = r A)
    (ht : ∀ A B, B ∩ t A = A ∩ t A → t B = t A)
    (A : Configuration G) :
    revealRecordEvent (jointReveal r t) A =
      revealRecordEvent r A ∩ revealRecordEvent t A := by
  ext B
  constructor
  · intro h
    have hR := recorded_agreement_of_subset A B (r A) _ Finset.subset_union_left h.2
    have hT := recorded_agreement_of_subset A B (t A) _ Finset.subset_union_right h.2
    exact ⟨⟨hr A B hR, hR⟩, ⟨ht A B hT, hT⟩⟩
  · rintro ⟨hR, hT⟩
    refine ⟨?_, ?_⟩
    · simp only [jointReveal, hR.1, hT.1]
    · change B ∩ (r A ∪ t A) = A ∩ (r A ∪ t A)
      rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left, hR.2, hT.2]

end
end PottsContinuity.Push
