-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteEnvelopeRevealConsistency.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- A least fill remains least when two configurations agree on the chosen
candidate's reveal cut (so they differ only outside it), provided common
subfills are available in the new configuration and their supports are
covered by that cut. -/
theorem fill_least_stable_under_reveal_agreement
    {I V E : Type*} [DecidableEq V] [DecidableEq E]
    (fill : I → Finset V) (supp cut : I → Finset E)
    (hcovered : ∀ r p, fill r ⊆ fill p → supp r ⊆ cut p)
    (hcommon : ∀ C : Finset E, ∀ p q,
      supp p ⊆ C → supp q ⊆ C →
        ∃ r, supp r ⊆ C ∧ fill r ⊆ fill p ∩ fill q)
    (A B : Finset E) (p : I)
    (hpA : supp p ⊆ A)
    (hleastA : ∀ q, supp q ⊆ A → fill p ⊆ fill q)
    (hagree : B ∩ cut p = A ∩ cut p) :
    supp p ⊆ B ∧ ∀ q, supp q ⊆ B → fill p ⊆ fill q := by
  have hpCut : supp p ⊆ cut p := hcovered p p (Finset.Subset.rfl)
  have hpB : supp p ⊆ B := by
    intro e he
    have heA : e ∈ A := hpA he
    have heCut : e ∈ cut p := hpCut he
    have heAcut : e ∈ A ∩ cut p := Finset.mem_inter.mpr ⟨heA, heCut⟩
    have heBcut : e ∈ B ∩ cut p := by rw [hagree]; exact heAcut
    exact (Finset.mem_inter.mp heBcut).1
  refine ⟨hpB, ?_⟩
  intro q hqB
  obtain ⟨r, hrB, hrFill⟩ := hcommon B p q hpB hqB
  have hrP : fill r ⊆ fill p := hrFill.trans Finset.inter_subset_left
  have hrCut : supp r ⊆ cut p := hcovered r p hrP
  have hrA : supp r ⊆ A := by
    intro e he
    have heB : e ∈ B := hrB he
    have heCut : e ∈ cut p := hrCut he
    have heBcut : e ∈ B ∩ cut p := Finset.mem_inter.mpr ⟨heB, heCut⟩
    have heAcut : e ∈ A ∩ cut p := by rw [← hagree]; exact heBcut
    exact (Finset.mem_inter.mp heAcut).1
  have hpR : fill p ⊆ fill r := hleastA r hrA
  have hrQ : fill r ⊆ fill q := hrFill.trans Finset.inter_subset_right
  exact hpR.trans hrQ

end PottsContinuity.FKC.FiniteFK
