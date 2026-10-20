-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripCandidateProbability.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripHeightEvents
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

open Set Topology MeasureTheory
open scoped BigOperators
namespace PottsContinuity.FKC.Medial
noncomputable section

@[instance_reducible]
def horizontalStripGoodCandidateFintype (n m : ℕ) :
    Fintype (horizontalStripGoodCandidate n m) :=
  Fintype.ofFinset (PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m) (by
    intro x
    constructor
    · intro hmem
      refine ⟨hmem, ?_⟩
      have hmem' := hmem
      simp only [PottsContinuity.FKC.FiniteFK.stripHeightCandidates,
        Finset.mem_product] at hmem'
      exact (Finset.mem_Icc.mp hmem'.2).2
    · intro hmem
      exact hmem.1)

@[instance_reducible]
def stripHeightCandidatesSubtypeFintype (n m : ℕ) :
    Fintype {x : ℤ × ℕ // x ∈ PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m} :=
  Fintype.ofFinset (PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m) (by
    intro x
    rfl)

def horizontalStripGoodCandidateEquiv (n m : ℕ) :
    horizontalStripGoodCandidate n m ≃
      {x : ℤ × ℕ // x ∈ PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m} where
  toFun x := ⟨x.1, x.2.1⟩
  invFun x := by
    have hy : x.1.2 ≤ n := by
      have hmem := x.2
      simp only [PottsContinuity.FKC.FiniteFK.stripHeightCandidates,
        Finset.mem_product] at hmem
      exact (Finset.mem_Icc.mp hmem.2).2
    exact ⟨x.1, x.2, hy⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem horizontalStripGoodCandidate_card (n m : ℕ) :
    Nat.card (horizontalStripGoodCandidate n m) =
      (2 * (n * m) + 1) * (n + 1) := by
  classical
  let candidateFintype : Fintype (horizontalStripGoodCandidate n m) :=
    horizontalStripGoodCandidateFintype n m
  let stripCandidateFintype :
      Fintype {x : ℤ × ℕ // x ∈ PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m} :=
    stripHeightCandidatesSubtypeFintype n m
  calc
    Nat.card (horizontalStripGoodCandidate n m) =
        Fintype.card (horizontalStripGoodCandidate n m) := Nat.card_eq_fintype_card
    _ = Fintype.card
        {x : ℤ × ℕ // x ∈ PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m} :=
      Fintype.card_congr (horizontalStripGoodCandidateEquiv n m)
    _ = (PottsContinuity.FKC.FiniteFK.stripHeightCandidates n m).card := Fintype.card_coe _
    _ = (2 * (n * m) + 1) * (n + 1) :=
      PottsContinuity.FKC.FiniteFK.stripHeightCandidates_card n m

theorem horizontalStripGoodCandidate_nonempty (n m : ℕ) :
    Nonempty (horizontalStripGoodCandidate n m) := by
  refine ⟨⟨(0, 0), ?_, Nat.zero_le _⟩⟩
  rw [PottsContinuity.FKC.FiniteFK.stripHeightCandidates, Finset.mem_product]
  constructor
  · rw [PottsContinuity.FKC.FiniteFK.stripHeightWindow, Finset.mem_Icc]
    constructor
    · exact neg_nonpos.mpr (Int.natCast_nonneg _)
    · exact Int.natCast_nonneg _
  · simp

/-- In any probability measure on the configuration space, one of the finite
local-minimum candidates has good-event probability at least the origin
height-sublevel probability divided by the exact candidate count. This is a
finite-cover averaging statement and makes no claim about a particular strip
law or a median estimate. -/
theorem exists_horizontalStripGoodCandidate_measure_lower_bound
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m)
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ] :
    ∃ x : horizontalStripGoodCandidate n m,
      (μ (horizontalStripGoodEvent n m x.1.1 x.1.2 x.2.2)).toReal ≥
        (μ {ω | horizontalStripHeight n ω 0 ≤ n}).toReal /
          ((2 * (n * m) + 1) * (n + 1)) := by
  classical
  let C := horizontalStripGoodCandidate n m
  let candidateFintype : Fintype C := horizontalStripGoodCandidateFintype n m
  have hnonempty : Nonempty C := by
    exact horizontalStripGoodCandidate_nonempty n m
  let : Nonempty C := hnonempty
  let H : Set LatticeConfiguration := {ω | horizontalStripHeight n ω 0 ≤ n}
  let G : C → Set LatticeConfiguration := fun x =>
    horizontalStripGoodEvent n m x.1.1 x.1.2 x.2.2
  have hcover : H ⊆ ⋃ x : C, G x := by
    simpa [C, H, G] using
      (horizontalStripHeightLE_at_zero_subset_goodEvents n m hn hm)
  have hsum : μ H ≤ ∑ x : C, μ (G x) := by
    calc
      μ H ≤ μ (⋃ x : C, G x) := measure_mono hcover
      _ ≤ ∑' x : C, μ (G x) := measure_iUnion_le _
      _ = ∑ x : C, μ (G x) := by simp
  have hcardpos : 0 < Fintype.card C := by
    exact Fintype.card_pos
  have hcardeq : Fintype.card C = (2 * (n * m) + 1) * (n + 1) := by
    simpa only [Nat.card_eq_fintype_card] using horizontalStripGoodCandidate_card n m
  let N : ENNReal := (Fintype.card C : ENNReal)
  have hNzero : N ≠ 0 := by
    simp [N, hcardpos.ne']
  have hNtop : N ≠ ⊤ := by
    simp [N]
  have hconst : ∑ x : C, μ H / N = μ H := by
    rw [Finset.sum_const, nsmul_eq_mul]
    change N * (μ H / N) = μ H
    rw [mul_comm]
    exact ENNReal.div_mul_cancel hNzero hNtop
  have hsum' : ∑ x : C, μ H / N ≤ ∑ x : C, μ (G x) := by
    rw [hconst]
    exact hsum
  obtain ⟨x, hxmem, hx⟩ := ENNReal.exists_le_of_sum_le
    (s := Finset.univ) (f := fun _ => μ H / N) (g := fun x => μ (G x))
    (Finset.univ_nonempty_iff.mpr hnonempty) (by simpa using hsum')
  have hxreal : (μ H / N).toReal ≤ (μ (G x)).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) hx
  have hNreal : N.toReal = Fintype.card C := by
    simp [N]
  have hreal : (μ H / N).toReal = (μ H).toReal / Fintype.card C := by
    rw [ENNReal.toReal_div, hNreal]
  refine ⟨x, ?_⟩
  have hxreal' : (μ H).toReal / Fintype.card C ≤ (μ (G x)).toReal := by
    simpa [hreal] using hxreal
  have hxreal'' : (μ H).toReal / ((2 * (n * m) + 1) * (n + 1)) ≤
      (μ (G x)).toReal := by
    simpa [hcardeq] using hxreal'
  simpa [H, G, C] using hxreal''

end
end PottsContinuity.FKC.Medial
