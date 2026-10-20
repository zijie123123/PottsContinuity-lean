-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedReveal.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxLeastCandidateReveal
public import PottsContinuity.FKC.FiniteFK.SlitBoxHorizontalReflection
public import PottsContinuity.FKC.FiniteFK.AdaptiveDomainMarkov

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open FiniteProbability

noncomputable section

local instance slitBoxPairedEdgeFintype (n : ℕ) : Fintype (slitBoxGraph n).edgeSet :=
  Fintype.ofFinite _
local instance slitBoxPairedEdgeDecidableEq (n : ℕ) : DecidableEq (slitBoxGraph n).edgeSet :=
  Classical.decEq _
def slitBoxReflectionConfigIso (n : ℕ) :
    Configuration (slitBoxGraph n) ≃ Configuration (slitBoxGraph n) :=
  configurationIso (slitBoxGraphHorizontalReflectionIso n)

def slitBoxRightReveal (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (A : Configuration (slitBoxGraph n)) : Configuration (slitBoxGraph n) :=
  slitBoxLeastCandidateReveal n hn u huY huX δ A

/-- The reflected right-side reveal, transported back by the full graph
isomorphism on configurations. -/
def slitBoxLeftReveal (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (A : Configuration (slitBoxGraph n)) : Configuration (slitBoxGraph n) :=
  (slitBoxReflectionConfigIso n).symm
    (slitBoxRightReveal n hn u huY huX δ ((slitBoxReflectionConfigIso n) A))

/-- The actual paired stopping cut is the union of the two total reveals. -/
def slitBoxPairedReveal (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (A : Configuration (slitBoxGraph n)) : Configuration (slitBoxGraph n) :=
  slitBoxRightReveal n hn u huY huX δ A ∪ slitBoxLeftReveal n hn u huY huX δ A

private theorem configIso_inter (n : ℕ) (A B : Configuration (slitBoxGraph n)) :
    slitBoxReflectionConfigIso n (A ∩ B) =
      slitBoxReflectionConfigIso n A ∩ slitBoxReflectionConfigIso n B := by
  change Finset.map
      (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding
      (A ∩ B) =
    Finset.map (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding A ∩
      Finset.map (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding B
  exact Finset.map_inter _ _

private theorem slitBoxLeftReveal_stopping_consistency
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (A B : Configuration (slitBoxGraph n))
    (hagree : B ∩ slitBoxLeftReveal n hn u huY huX δ A =
      A ∩ slitBoxLeftReveal n hn u huY huX δ A) :
    slitBoxLeftReveal n hn u huY huX δ B = slitBoxLeftReveal n hn u huY huX δ A := by
  let e := slitBoxReflectionConfigIso n
  have htrans := congrArg e hagree
  have hstates : e B ∩ slitBoxRightReveal n hn u huY huX δ (e A) =
      e A ∩ slitBoxRightReveal n hn u huY huX δ (e A) := by
    simpa [slitBoxLeftReveal, slitBoxRightReveal, e, configIso_inter] using htrans
  have hstatesMem : ∀ x,
      (x ∈ e B ∧ x ∈ slitBoxLeastCandidateReveal n hn u huY huX δ (e A)) ↔
      (x ∈ e A ∧ x ∈ slitBoxLeastCandidateReveal n hn u huY huX δ (e A)) := by
    intro x
    have hx := Finset.ext_iff.mp (by simpa [slitBoxRightReveal] using hstates) x
    simpa only [Finset.mem_inter] using hx
  have hstable := by
    letI : DecidableEq (slitBoxGraph n).edgeSet := Subtype.instDecidableEq
    have hstates' : e B ∩ slitBoxLeastCandidateReveal n hn u huY huX δ (e A) =
        e A ∩ slitBoxLeastCandidateReveal n hn u huY huX δ (e A) := by
      ext x
      simpa only [Finset.mem_inter] using hstatesMem x
    exact slitBoxLeastCandidateReveal_stopping_consistency
      n hn u huY huX δ (e A) (e B) hstates'
  apply e.injective
  simpa [slitBoxLeftReveal, slitBoxRightReveal, e] using hstable

/-- The union reveal remains stable when its complete revealed state is fixed. -/
theorem slitBoxPairedReveal_stopping_consistency
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (A B : Configuration (slitBoxGraph n))
    (hagree : B ∩ slitBoxPairedReveal n hn u huY huX δ A =
      A ∩ slitBoxPairedReveal n hn u huY huX δ A) :
    slitBoxPairedReveal n hn u huY huX δ B = slitBoxPairedReveal n hn u huY huX δ A := by
  have hright : B ∩ slitBoxRightReveal n hn u huY huX δ A =
      A ∩ slitBoxRightReveal n hn u huY huX δ A := by
    apply Finset.ext
    intro e
    have h := Finset.ext_iff.mp hagree e
    simp only [slitBoxPairedReveal, Finset.mem_inter, Finset.mem_union] at h ⊢
    tauto
  have hrightMem : ∀ x,
      (x ∈ B ∧ x ∈ slitBoxLeastCandidateReveal n hn u huY huX δ A) ↔
      (x ∈ A ∧ x ∈ slitBoxLeastCandidateReveal n hn u huY huX δ A) := by
    intro x
    have hx := Finset.ext_iff.mp (by simpa [slitBoxRightReveal] using hright) x
    simpa only [Finset.mem_inter] using hx
  have hleft : B ∩ slitBoxLeftReveal n hn u huY huX δ A =
      A ∩ slitBoxLeftReveal n hn u huY huX δ A := by
    apply Finset.ext
    intro e
    have h := Finset.ext_iff.mp hagree e
    simp only [slitBoxPairedReveal, Finset.mem_inter, Finset.mem_union] at h ⊢
    tauto
  have hr := by
    letI : DecidableEq (slitBoxGraph n).edgeSet := Subtype.instDecidableEq
    have hright' : B ∩ slitBoxLeastCandidateReveal n hn u huY huX δ A =
        A ∩ slitBoxLeastCandidateReveal n hn u huY huX δ A := by
      ext x
      simpa only [Finset.mem_inter] using hrightMem x
    exact slitBoxLeastCandidateReveal_stopping_consistency
      n hn u huY huX δ A B hright'
  have hl := slitBoxLeftReveal_stopping_consistency
    n hn u huY huX δ A B hleft
  simp [slitBoxPairedReveal, slitBoxRightReveal, hr, hl]

/-- Filtering the genuine finite FK law on the actual paired reveal record and
reading the complementary coordinates gives the law with the boundary frozen
by that same record. -/
theorem slitBoxPairedReveal_law_filter_map_remaining
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (q : ClusterWeight) (A : Configuration (slitBoxGraph n)) :
    ((law (slitBoxGraph n) q (slitBoxBoundary n)).filter
      (revealRecordEvent (slitBoxGraph n)
        (slitBoxPairedReveal n hn u huY huX δ) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent (slitBoxGraph n)
          (slitBoxPairedReveal n hn u huY huX δ)
          (slitBoxPairedReveal_stopping_consistency n hn u huY huX δ) A]
        exact frozenStateEvent_support q (slitBoxBoundary n)
          (slitBoxPairedReveal n hn u huY huX δ A)
          (revealRecordConfiguration (slitBoxGraph n)
            (slitBoxPairedReveal n hn u huY huX δ) A))).map
        (fun C => (configurationSplitEquiv (slitBoxGraph n)
          (slitBoxPairedReveal n hn u huY huX δ A) C).1) =
      remainingLaw (slitBoxGraph n) q
        (frozenBoundary (slitBoxBoundary n)
          (revealRecordConfiguration (slitBoxGraph n)
            (slitBoxPairedReveal n hn u huY huX δ) A).val)
        (slitBoxPairedReveal n hn u huY huX δ A) := by
  let hstable : ∀ C C' : Configuration (slitBoxGraph n),
      C' ∩ slitBoxPairedReveal n hn u huY huX δ C =
        C ∩ slitBoxPairedReveal n hn u huY huX δ C →
      slitBoxPairedReveal n hn u huY huX δ C' =
        slitBoxPairedReveal n hn u huY huX δ C := by
    intro C C' h
    have h' : C' ∩ slitBoxPairedReveal n hn u huY huX δ C =
        C ∩ slitBoxPairedReveal n hn u huY huX δ C := by
      ext e
      exact Finset.ext_iff.mp h e
    exact slitBoxPairedReveal_stopping_consistency n hn u huY huX δ C C' h'
  exact law_filter_revealRecord_map_remaining (slitBoxGraph n) q
    (slitBoxBoundary n) (slitBoxPairedReveal n hn u huY huX δ)
    hstable A

end

end PottsContinuity.FKC.FiniteFK

