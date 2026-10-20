module

public import PottsContinuity.Exploration.FiniteOutermostSelectorDMP
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace PottsContinuity.Exploration

open PottsContinuity.PD.FK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}
variable {I : Type*} [Fintype I]

local instance envelopeMaxEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance envelopeMaxEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance envelopeMaxIndexDecidableEq : DecidableEq I := Classical.decEq _

/-- Indices of the candidates valid in one configuration. -/
def envelopeCandidateSet (valid : Configuration G → I → Prop)
    (C : Configuration G) : Finset I := by
  classical
  exact Finset.univ.filter (valid C)

/-- Choose a valid candidate with a largest finite region. -/
noncomputable def envelopeMaxCandidate (valid : Configuration G → I → Prop)
    (inside : I → Finset V) (C : Configuration G) : Option I := by
  classical
  let S := envelopeCandidateSet valid C
  exact if hS : S.Nonempty then
    some (Classical.choose (S.exists_max_image (fun i => (inside i).card) hS))
  else none

omit [Finite V] in
/-- A selected candidate is valid and has maximal region cardinality. -/
theorem envelopeMaxCandidate_spec (valid : Configuration G → I → Prop)
    (inside : I → Finset V) (C : Configuration G) (i : I)
    (hi : envelopeMaxCandidate valid inside C = some i) :
    valid C i ∧ ∀ j, valid C j → (inside j).card ≤ (inside i).card := by
  classical
  let S := envelopeCandidateSet valid C
  have hS : S.Nonempty := by
    by_contra hn
    simp [envelopeMaxCandidate, S, hn] at hi
  have hchosen := Classical.choose_spec
    (S.exists_max_image (fun j => (inside j).card) hS)
  have himem : i ∈ S := by
    have h : some (Classical.choose
        (S.exists_max_image (fun j => (inside j).card) hS)) = some i := by
      simpa [envelopeMaxCandidate, S, hS] using hi
    have heq := Option.some.inj h
    rw [← heq]
    exact hchosen.1
  refine ⟨(Finset.mem_filter.mp himem).2, ?_⟩
  intro j hj
  have hmaxj := hchosen.2 j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  have h : some (Classical.choose
      (S.exists_max_image (fun t => (inside t).card) hS)) = some i := by
    simpa [envelopeMaxCandidate, S, hS] using hi
  simpa [Option.some.inj h] using hmaxj

omit [Finite V] in
/-- A maximum selector is attained exactly when its candidate family is
nonempty. -/
theorem envelopeMaxCandidate_exists_iff (valid : Configuration G → I → Prop)
    (inside : I → Finset V) (C : Configuration G) :
    (∃ i, envelopeMaxCandidate valid inside C = some i) ↔
      ∃ i, valid C i := by
  classical
  let S := envelopeCandidateSet valid C
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (envelopeMaxCandidate_spec valid inside C i hi).1⟩
  · rintro ⟨i, hi⟩
    have hS : S.Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    let j := Classical.choose (S.exists_max_image (fun t => (inside t).card) hS)
    refine ⟨j, ?_⟩
    simp [envelopeMaxCandidate, S, hS, j]

/-- The reveal is the prescribed outside set for the selected candidate.
When no candidate is valid, expose the whole finite graph. -/
def envelopeMaxRevealMap (valid : Configuration G → I → Prop)
    (inside : I → Finset V) (outside : Finset V → Finset G.edgeSet) :
    RevealMap (G := G) := fun C =>
      match envelopeMaxCandidate valid inside C with
      | none => Finset.univ
      | some i => outside (inside i)

/-- If pairwise envelopes stay valid and contain both regions, an
area-maximizing candidate's outside record is stable. The premise that an
envelope's recognition bonds lie outside the first region is the geometric
input needed for a concrete circuit application. -/
theorem envelopeMaxRevealMap_stable
    (valid : Configuration G → I → Prop)
    (inside : I → Finset V) (support : I → Finset G.edgeSet)
    (outside : Finset V → Finset G.edgeSet)
    (join : I → I → I)
    (hlocal : ∀ C C' i, candidateStatesAgree C C' (support i) →
      (valid C i ↔ valid C' i))
    (hself : ∀ i, support i ⊆ outside (inside i))
    (henvelopeValid : ∀ C i j, valid C i → valid C j → valid C (join i j))
    (henvelopeInside : ∀ i j,
      inside i ∪ inside j ⊆ inside (join i j))
    (henvelopeOutside : ∀ i j,
      support (join i j) ⊆ outside (inside i)) :
    ∀ C C', C' ∩ envelopeMaxRevealMap valid inside outside C =
      C ∩ envelopeMaxRevealMap valid inside outside C →
        envelopeMaxRevealMap valid inside outside C' =
          envelopeMaxRevealMap valid inside outside C := by
  classical
  intro C C' hrecord
  cases hi : envelopeMaxCandidate valid inside C with
  | none =>
      have hconfig : C' = C := by
        apply Finset.ext
        intro e
        have hmem := congrArg (fun s : Finset G.edgeSet => e ∈ s) hrecord
        have hstates : (e ∈ C') = (e ∈ C) := by
          simpa [envelopeMaxRevealMap, hi, Finset.mem_inter] using hmem
        exact Iff.of_eq hstates
      subst C'
      rfl
  | some i =>
      have hagree : candidateStatesAgree C C' (outside (inside i)) := by
        intro e he
        have hmem := congrArg (fun s : Finset G.edgeSet => e ∈ s) hrecord
        have hstates : (e ∈ C') = (e ∈ C) := by
          simpa [envelopeMaxRevealMap, hi, Finset.mem_inter, he] using hmem
        exact Iff.of_eq hstates.symm
      have hmaxC := envelopeMaxCandidate_spec valid inside C i hi
      have hiC' : valid C' i := by
        apply (hlocal C C' i _).mp hmaxC.1
        intro e he
        exact hagree e (hself i he)
      have hdominated : ∀ j, valid C' j → inside j ⊆ inside i := by
        intro j hj
        by_contra hnot
        let k := join i j
        have hkC' : valid C' k := henvelopeValid C' i j hiC' hj
        have hkC : valid C k := by
          apply (hlocal C C' k _).mpr hkC'
          intro e he
          exact hagree e (henvelopeOutside i j he)
        have hmaxk := hmaxC.2 k hkC
        have hstrict : inside i ⊂ inside i ∪ inside j :=
          Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, by
            intro heq
            apply hnot
            rw [heq]
            exact Finset.subset_union_right⟩
        have hlt : (inside i).card < (inside i ∪ inside j).card :=
          Finset.card_lt_card hstrict
        have hle : (inside i ∪ inside j).card ≤ (inside k).card :=
          Finset.card_le_card (henvelopeInside i j)
        omega
      have hselected' : ∃ j, envelopeMaxCandidate valid inside C' = some j := by
        let S := envelopeCandidateSet valid C'
        have hS : S.Nonempty := by
          refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiC'⟩⟩
        let j := Classical.choose (S.exists_max_image (fun t => (inside t).card) hS)
        refine ⟨j, ?_⟩
        simp [envelopeMaxCandidate, S, hS, j]
      obtain ⟨j, hjselect⟩ := hselected'
      have hjmax := envelopeMaxCandidate_spec valid inside C' j hjselect
      have hji : inside j ⊆ inside i := hdominated j hjmax.1
      have hcard : (inside i).card ≤ (inside j).card := hjmax.2 i hiC'
      have hregions : inside j = inside i :=
        Finset.eq_of_subset_of_card_le hji hcard
      simp [envelopeMaxRevealMap, hi, hjselect, hregions]

end

end PottsContinuity.Exploration
