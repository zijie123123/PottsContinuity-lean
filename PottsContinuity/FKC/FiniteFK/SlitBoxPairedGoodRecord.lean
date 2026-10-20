-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxPairedGoodRecord.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxPairedReveal
public import PottsContinuity.FKC.FiniteFK.SlitBoxOpenCandidateExistence
public import PottsContinuity.FKC.FiniteFK.RevealRecordDisintegration
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

local instance slitBoxGoodRecordEdgeFintype (n : ℕ) :
    Fintype (slitBoxGraph n).edgeSet := Fintype.ofFinite _
local instance slitBoxGoodRecordEdgeDecidableEq (n : ℕ) :
    DecidableEq (slitBoxGraph n).edgeSet := Classical.decEq _

def slitBoxGoodRecordConfigIso (n : ℕ) :
    Configuration (slitBoxGraph n) ≃ Configuration (slitBoxGraph n) :=
  configurationIso (slitBoxGraphHorizontalReflectionIso n)

private theorem slitBoxGoodRecordConfigIso_inter (n : ℕ)
    (A B : Configuration (slitBoxGraph n)) :
    slitBoxGoodRecordConfigIso n (A ∩ B) =
      slitBoxGoodRecordConfigIso n A ∩ slitBoxGoodRecordConfigIso n B := by
  change Finset.map
      (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding
      (A ∩ B) =
    Finset.map (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding A ∩
      Finset.map (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding B
  exact Finset.map_inter _ _

private theorem slitBoxGoodRecordConfigIso_subset_iff (n : ℕ)
    (A B : Configuration (slitBoxGraph n)) :
    slitBoxGoodRecordConfigIso n A ⊆ slitBoxGoodRecordConfigIso n B ↔ A ⊆ B := by
  change Finset.map
      (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding A ⊆
    Finset.map (configurationIsoEdgeEquiv (slitBoxGraphHorizontalReflectionIso n)).toEmbedding B ↔
      A ⊆ B
  exact Finset.map_subset_map

private theorem slitBoxActualArcConnection_iff_of_covering_cut
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (A B : Configuration (slitBoxGraph n))
    (P : Configuration (slitBoxGraph n))
    (hcutA : slitBoxLeastCandidateReveal n hn u huY huX δ A ⊆ P)
    (hcutB : slitBoxLeastCandidateReveal n hn u huY huX δ B ⊆ P)
    (hstate : B ∩ P = A ∩ P) :
    (A ∈ slitBoxWiredArcConnectionEvent n u) ↔
      (B ∈ slitBoxWiredArcConnectionEvent n u) := by
  constructor
  · intro hA
    let p := slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ A hA
    have hp := slitBoxLeastOpenCandidateOnEvent_characterization
      n hn u huY huX δ A hA
    have hpCut := slitBoxLeastCandidateReveal_support_subset_of_hit
      n hn u huY huX δ A hA
    have hpB : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ B := by
      intro e he
      have heA := hp.1 he
      have heCut := hcutA (hpCut he)
      have hmem := Finset.ext_iff.mp hstate e
      simp only [Finset.mem_inter] at hmem
      exact (hmem.mpr ⟨heA, heCut⟩).1
    apply (slitBoxFirstHitCandidate_exists_open_iff_actualConnected n u B).mp
    exact ⟨p, hpB⟩
  · intro hB
    let p := slitBoxLeastOpenCandidateOnEvent n hn u huY huX δ B hB
    have hp := slitBoxLeastOpenCandidateOnEvent_characterization
      n hn u huY huX δ B hB
    have hpCut := slitBoxLeastCandidateReveal_support_subset_of_hit
      n hn u huY huX δ B hB
    have hpA : slitBoxCandidateOriginalPathEdgeSupport n u p ⊆ A := by
      intro e he
      have heB := hp.1 he
      have heCut := hcutB (hpCut he)
      have hmem := Finset.ext_iff.mp hstate e
      simp only [Finset.mem_inter] at hmem
      exact (hmem.mp ⟨heB, heCut⟩).1
    apply (slitBoxFirstHitCandidate_exists_open_iff_actualConnected n u A).mp
    exact ⟨p, hpA⟩

/-- The genuine paired-hit event is stable on every attained paired reveal
record. Its clauses are actual wired-arc connection events at `u` in the
original and fully reflected configurations. -/
theorem slitBoxPairedGoodEvent_stable_under_record
    (n : ℕ) (hn : 1 ≤ n) (u : SlitBoxVertex n)
    (huY : u.val.2 = -(n : ℤ)) (huX : 0 ≤ u.val.1) (δ : PositiveMesh)
    (A B : Configuration (slitBoxGraph n))
    (hrecord : revealRecordStatistic
        (slitBoxPairedReveal n hn u huY huX δ) A =
      revealRecordStatistic (slitBoxPairedReveal n hn u huY huX δ) B) :
    (A ∈ slitBoxWiredArcConnectionEvent n u ∧
      slitBoxGoodRecordConfigIso n A ∈ slitBoxWiredArcConnectionEvent n u) ↔
    (B ∈ slitBoxWiredArcConnectionEvent n u ∧
      slitBoxGoodRecordConfigIso n B ∈ slitBoxWiredArcConnectionEvent n u) := by
  classical
  let e := slitBoxGoodRecordConfigIso n
  have hcut := congrArg Prod.fst hrecord
  have hstate0 := congrArg Prod.snd hrecord
  change slitBoxPairedReveal n hn u huY huX δ A =
      slitBoxPairedReveal n hn u huY huX δ B at hcut
  change A ∩ slitBoxPairedReveal n hn u huY huX δ A =
      B ∩ slitBoxPairedReveal n hn u huY huX δ B at hstate0
  have hstate : B ∩ slitBoxPairedReveal n hn u huY huX δ A =
      A ∩ slitBoxPairedReveal n hn u huY huX δ A := by
    rw [← hcut] at hstate0
    exact hstate0.symm
  have hrightA : slitBoxLeastCandidateReveal n hn u huY huX δ A ⊆
      slitBoxPairedReveal n hn u huY huX δ A := Finset.subset_union_left
  have hrightB : slitBoxLeastCandidateReveal n hn u huY huX δ B ⊆
      slitBoxPairedReveal n hn u huY huX δ A := by
    calc
      slitBoxLeastCandidateReveal n hn u huY huX δ B ⊆
          slitBoxPairedReveal n hn u huY huX δ B := Finset.subset_union_left
      _ = slitBoxPairedReveal n hn u huY huX δ A := hcut.symm
  have hRight := slitBoxActualArcConnection_iff_of_covering_cut
    n hn u huY huX δ A B (slitBoxPairedReveal n hn u huY huX δ A)
    hrightA hrightB hstate
  have hstateLeft : e B ∩ e (slitBoxPairedReveal n hn u huY huX δ A) =
      e A ∩ e (slitBoxPairedReveal n hn u huY huX δ A) := by
    have hmap := congrArg e hstate
    simpa [e, slitBoxGoodRecordConfigIso_inter] using hmap
  have hleftA : slitBoxLeastCandidateReveal n hn u huY huX δ (e A) ⊆
      e (slitBoxPairedReveal n hn u huY huX δ A) := by
    have heq : slitBoxLeastCandidateReveal n hn u huY huX δ (e A) =
        e (slitBoxLeftReveal n hn u huY huX δ A) := by
      change slitBoxLeastCandidateReveal n hn u huY huX δ
          (configurationIso (slitBoxGraphHorizontalReflectionIso n) A) =
        configurationIso (slitBoxGraphHorizontalReflectionIso n)
          ((configurationIso (slitBoxGraphHorizontalReflectionIso n)).symm
            (slitBoxLeastCandidateReveal n hn u huY huX δ
              (configurationIso (slitBoxGraphHorizontalReflectionIso n) A)))
      exact ((configurationIso (slitBoxGraphHorizontalReflectionIso n)).apply_symm_apply _).symm
    rw [heq]
    apply (slitBoxGoodRecordConfigIso_subset_iff n _ _).2
    exact Finset.subset_union_right
  have hleftB : slitBoxLeastCandidateReveal n hn u huY huX δ (e B) ⊆
      e (slitBoxPairedReveal n hn u huY huX δ A) := by
    have heq : slitBoxLeastCandidateReveal n hn u huY huX δ (e B) =
        e (slitBoxLeftReveal n hn u huY huX δ B) := by
      change slitBoxLeastCandidateReveal n hn u huY huX δ
          (configurationIso (slitBoxGraphHorizontalReflectionIso n) B) =
        configurationIso (slitBoxGraphHorizontalReflectionIso n)
          ((configurationIso (slitBoxGraphHorizontalReflectionIso n)).symm
            (slitBoxLeastCandidateReveal n hn u huY huX δ
              (configurationIso (slitBoxGraphHorizontalReflectionIso n) B)))
      exact ((configurationIso (slitBoxGraphHorizontalReflectionIso n)).apply_symm_apply _).symm
    rw [heq]
    apply (slitBoxGoodRecordConfigIso_subset_iff n _ _).2
    calc
      slitBoxLeftReveal n hn u huY huX δ B ⊆
          slitBoxPairedReveal n hn u huY huX δ B := Finset.subset_union_right
      _ = slitBoxPairedReveal n hn u huY huX δ A := hcut.symm
  have hLeft := slitBoxActualArcConnection_iff_of_covering_cut
    n hn u huY huX δ (e A) (e B)
    (e (slitBoxPairedReveal n hn u huY huX δ A)) hleftA hleftB hstateLeft
  exact and_congr hRight hLeft

end

end PottsContinuity.FKC.FiniteFK

