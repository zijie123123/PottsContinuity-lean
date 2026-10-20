-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteEnvelopeLeast.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

/-- On a nonempty finite family, pairwise common subfills force a unique
inclusion-least fill, provided the fill map is injective. The least-cardinality
argument is upgraded to inclusion using the common subfill hypothesis. -/
theorem existsUnique_least_fill_of_pairwise_common_subfill
    {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (fill : I → Finset V) (hinj : Function.Injective fill)
    (S : Set I) (hS : S.Nonempty)
    (hcommon : ∀ p, p ∈ S → ∀ q, q ∈ S →
      ∃ r, r ∈ S ∧ fill r ⊆ fill p ∩ fill q) :
    ∃! p, p ∈ S ∧ ∀ q, q ∈ S → fill p ⊆ fill q := by
  classical
  let candidates : Finset I := Finset.univ.filter fun i => i ∈ S
  have hcandidates : candidates.Nonempty := by
    obtain ⟨i, hi⟩ := hS
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  obtain ⟨p, hpCandidates, hmin⟩ :=
    candidates.exists_min_image (fun i => (fill i).card) hcandidates
  have hpS : p ∈ S := (Finset.mem_filter.mp hpCandidates).2
  have hleast : ∀ q, q ∈ S → fill p ⊆ fill q := by
    intro q hq
    obtain ⟨r, hr, hsub⟩ := hcommon p hpS q hq
    have hrCandidates : r ∈ candidates :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
    have hminr : (fill p).card ≤ (fill r).card := hmin r hrCandidates
    have hrp : fill r ⊆ fill p := hsub.trans Finset.inter_subset_left
    have hcardrp : (fill r).card ≤ (fill p).card := Finset.card_le_card hrp
    have hcardEq : (fill r).card = (fill p).card := Nat.le_antisymm hcardrp hminr
    have hfillEq : fill r = fill p :=
      Finset.eq_of_subset_of_card_le hrp (by rw [hcardEq])
    have hrq : fill r ⊆ fill q := hsub.trans Finset.inter_subset_right
    simpa [hfillEq] using hrq
  refine ⟨p, ⟨hpS, hleast⟩, ?_⟩
  intro q hq
  apply hinj
  exact Finset.Subset.antisymm (hq.2 p hpS) (hleast q hq.1)

end PottsContinuity.FKC.FiniteFK
