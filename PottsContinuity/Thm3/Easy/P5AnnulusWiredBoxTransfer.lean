module

public import PottsContinuity.Thm3.Easy.P5ToP1OfAnnulusTransfer
public import PottsContinuity.Thm3.Easy.P5AnnulusCandidateBoundaryPartition
public import PottsContinuity.Thm3.Easy.P5AnnulusWiredBoxNoCrossing
public import PottsContinuity.DualityExt.PositiveP5aAnnulusDualMapBridge
public import PottsContinuity.DualityExt.AnnulusBoundaryIdentification

@[expose] public section

namespace PottsContinuity.Thm3.Easy

open MeasureTheory
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite
open PottsContinuity.DualityExt

noncomputable section

private theorem p5AnnulusInnerWitness (N : ℕ) (hN : 2 ≤ N) :
    ∃ u : {x : LatticeVertex // x ∈ annulusVertexSet N},
      u ∈ annulusPrimalInnerBoundaryClass N (by omega) := by
  let u : {x : LatticeVertex // x ∈ annulusVertexSet N} := ⟨(N, 0), by
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [mem_latticeBox]
      simp only [zero_sub, zero_add]
      constructor <;> constructor <;> omega
    · intro h
      have h' := (mem_latticeBox (0, 0) (N, 0) (N - 1)).mp h
      simp only [zero_sub, zero_add] at h'
      omega⟩
  refine ⟨u, ?_⟩
  change annulusSourceEmbedding N u ∈ annulusHostPrimalInnerClass N
  change (annulusSourceEmbedding N u).1 ∈ latticeBox (0, 0) (N - 1) ∨
    ∃ y, y ∈ latticeBox (0, 0) (N - 1) ∧
      squareLattice.Adj y (annulusSourceEmbedding N u).1
  right
  refine ⟨(N - 1, 0), ?_, ?_⟩
  · rw [mem_latticeBox]
    simp only [zero_sub, zero_add]
    constructor <;> constructor <;> omega
  · have hadj : squareLattice.Adj (N, 0) (N - 1, 0) := by
      change PottsContinuity.PD.FK.squareLattice.Adj (N, 0) (N - 1, 0)
      rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
      exact Or.inl ⟨Or.inr (by omega), rfl⟩
    change squareLattice.Adj (N - 1, 0) (N, 0)
    exact hadj.symm

private theorem p5AnnulusOuterWitness (N : ℕ) (hN : 2 ≤ N) :
    ∃ v : {x : LatticeVertex // x ∈ annulusVertexSet N},
      v ∈ annulusPrimalOuterBoundaryClass N (by omega) := by
  let v : {x : LatticeVertex // x ∈ annulusVertexSet N} := ⟨(2 * N, 0), by
    apply Finset.mem_sdiff.mpr
    constructor
    · rw [mem_latticeBox]
      simp only [zero_sub, zero_add]
      constructor <;> constructor <;> omega
    · intro h
      have h' := (mem_latticeBox (0, 0) (2 * N, 0) (N - 1)).mp h
      simp only [zero_sub, zero_add] at h'
      omega⟩
  refine ⟨v, ?_⟩
  change annulusSourceEmbedding N v ∈ annulusHostPrimalOuterClass N
  change (annulusSourceEmbedding N v).1 ∈ PottsContinuity.PD.vertexBoundary
    (PottsContinuity.PD.FK.latticeRectangle (annulusHostAnchor N) (4 * N) (4 * N))
  have hcoord : (annulusSourceEmbedding N v).1 = (2 * (N : ℤ), 0) := rfl
  rw [hcoord]
  rw [PottsContinuity.PD.vertexBoundary]
  refine ⟨?_, (2 * N + 1, 0), ?_, ?_⟩
  · rw [mem_latticeRectangle]
    simp only [annulusHostAnchor]
    constructor <;> constructor <;> omega
  · have hadj : squareLattice.Adj (2 * N, 0) (2 * N + 1, 0) := by
      change PottsContinuity.PD.FK.squareLattice.Adj
        (2 * N, 0) (2 * N + 1, 0)
      rw [PottsContinuity.PD.FK.squareLattice_adj_iff]
      exact Or.inl ⟨Or.inl rfl, rfl⟩
    change squareLattice.Adj (2 * N, 0) (2 * N + 1, 0)
    exact hadj
  · intro hout
    rw [PottsContinuity.PD.FK.mem_latticeRectangle] at hout
    simp only [annulusHostAnchor] at hout
    omega

/-- The source P5a circuit estimate yields the exact wired-box annulus
transfer through the finite double-dual identification of `DualityExt`. -/
theorem p5a_wiredBoxAnnulusTransfer :
    ∀ (q : Set.Ici (1 : ℝ)) (j : ℕ) (c : ℝ), 3 ≤ j → 0 < c →
      c ≤ p5aAnnulusProbability (criticalParameters q) (2 ^ (j - 1) - 1) →
      (boxMeasure (criticalParameters q) 1 (0, 0) (2 ^ j) :
        Measure LatticeConfiguration).real
        {ω | annulusOpenCrossing (2 ^ (j - 1)) ω} ≤ 1 - c / (q : ℝ) := by
  intro q j c hj hc hP5a
  let N := 2 ^ (j - 1)
  let M := 2 ^ j
  have hjm : 2 ≤ j - 1 := by omega
  have hN4 : 4 ≤ N := by
    dsimp [N]
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j - 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hjm
  have hN : 1 ≤ N := by omega
  have hpow : M = 2 * N := by
    dsimp [M, N]
    calc
      2 ^ j = 2 ^ (j - 1 + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ j)]
      _ = 2 ^ (j - 1) * 2 := by rw [Nat.pow_succ]
      _ = 2 * 2 ^ (j - 1) := by omega
  have hK := annulusExpandedHostDualCandidateGraph_le_rectangle N
  let e := annulusCandidateDoubleDualActiveVertexEquiv N (by omega)
  have hgraph := annulusCandidateDoubleDualActiveGraph_map_eq N (by omega)
  have hpartition := p5aAnnulusCandidate_wiredBoundary_partition N (by omega)
  let f := annulusExpandedHostCarrierEquiv N
  have hIso := annulusExpandedHostDualCandidateGraph_map_eq N
  have hmap := annulusCandidateDoubleDualConfigurationMap_eq N (by omega)
  obtain ⟨u, hu⟩ := p5AnnulusInnerWitness N (by omega)
  obtain ⟨v, hv⟩ := p5AnnulusOuterWitness N (by omega)
  have hdual := annulus_jointWired_p5a_noFullBoxCrossing_ge_div_at_fullVertexBoundary_of_actualDualMapEq
    N hN hN4 hK e hgraph hpartition q c u v hu hv f hIso hmap (by simpa [N] using hP5a)
  have hcompare := annulus_wired_noCrossing_le_wiredBox_noCrossing_at_touchingBoundary
    (criticalParameters q) N M hN (by omega)
  have hbox : c / (q : ℝ) ≤
      (boxMeasure (criticalParameters q) 1 (0, 0) M :
        Measure LatticeConfiguration).real
        ({ω | annulusOpenCrossing N ω}ᶜ) := hdual.trans hcompare
  have hsum :
      (boxMeasure (criticalParameters q) 1 (0, 0) M :
        Measure LatticeConfiguration).real {ω | annulusOpenCrossing N ω} +
      (boxMeasure (criticalParameters q) 1 (0, 0) M :
        Measure LatticeConfiguration).real
          ({ω | annulusOpenCrossing N ω}ᶜ) = 1 := by
    simpa [Measure.real_def] using measureReal_add_measureReal_compl
      (μ := (boxMeasure (criticalParameters q) 1 (0, 0) M :
        Measure LatticeConfiguration))
      (annulusOpenCrossing_isCylinder N).measurableSet
  have hbox' : c / (q : ℝ) ≤
      (boxMeasure (criticalParameters q) 1 (0, 0) (2 ^ j) :
        Measure LatticeConfiguration).real
        ({ω | annulusOpenCrossing (2 ^ (j - 1)) ω}ᶜ) := by
    simpa [M, N] using hbox
  have hsum' :
      (boxMeasure (criticalParameters q) 1 (0, 0) (2 ^ j) :
        Measure LatticeConfiguration).real
          {ω | annulusOpenCrossing (2 ^ (j - 1)) ω} +
      (boxMeasure (criticalParameters q) 1 (0, 0) (2 ^ j) :
        Measure LatticeConfiguration).real
          ({ω | annulusOpenCrossing (2 ^ (j - 1)) ω}ᶜ) = 1 := by
    simpa [M, N] using hsum
  linarith

/-- P5 implies wired nonpercolation at the explicit self-dual parameter.
The statement is definitionally the P5 ⇒ P1 hypothesis `hP5toP1` of
`Assembly.theorem_3_of_links`. -/
theorem p5_implies_p1
    (q : Set.Ici (1 : ℝ))
    (p : Set.Icc (0 : ℝ) 1)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hp : (p : ℝ) = Real.sqrt (q : ℝ) / (1 + Real.sqrt (q : ℝ)))
    (hμ : IsRCInfiniteVolumeLimit p
      ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩ 1 μ)
    (hP5 : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ rcEventProb
        (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
          (-(n : ℤ)) (2 * (n : ℤ)))
        p
        ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩
        0
        (horizontalCrossing
          (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
            (-(n : ℤ)) (2 * (n : ℤ)))
          0 ⌊α * (n : ℝ)⌋ 0 n)) :
    μ {ω | {y | (PottsContinuity.rcInfiniteOpenGraph ω).Reachable
      (0, 0) y}.Infinite} = 0 := by
  let θ := criticalParameters q
  let qpos : Set.Ioi (0 : ℝ) :=
    ⟨(q : ℝ), Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos q.property)⟩
  have hpθ : p = θ.toP := by
    apply Subtype.ext
    simpa [θ, criticalParameters, Parameters.toP, edgeParameter,
      PottsContinuity.PD.rcCriticalParameter] using hp
  have hqθ : qpos = θ.toQ := by
    apply Subtype.ext
    rfl
  have hμθ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 1 μ := by
    rw [← hpθ, ← hqθ]
    exact hμ
  have hP5θ : ∀ α : ℝ, 0 < α → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c ≤ rcEventProb
        (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
          (-(n : ℤ)) (2 * (n : ℤ)))
        θ.toP θ.toQ 0
        (horizontalCrossing
          (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * (n : ℝ)⌋
            (-(n : ℤ)) (2 * (n : ℤ)))
          0 ⌊α * (n : ℝ)⌋ 0 n) := by
    intro α hα
    rw [← hpθ, ← hqθ]
    exact hP5 α hα
  have hAnnulusTransfer : ∀ j : ℕ, 3 ≤ j →
      p5aAnnulusProbability θ (2 ^ (j - 1) - 1) / (q : ℝ) ≤
        1 - (boxMeasure θ 1 (0, 0) (2 ^ j) :
          Measure LatticeConfiguration).real
            {ω | annulusOpenCrossing (2 ^ (j - 1)) ω} := by
    intro j hj
    have hjm : 2 ≤ j - 1 := by omega
    have hrad : 4 ≤ 2 ^ (j - 1) := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (j - 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hjm
    have hscale : 2 ≤ 2 ^ (j - 1) - 1 := by omega
    have hpositive := p5aAnnulusProbability_pos θ (2 ^ (j - 1) - 1) hscale
    have hbox := p5a_wiredBoxAnnulusTransfer q j
      (p5aAnnulusProbability θ (2 ^ (j - 1) - 1)) hj hpositive le_rfl
    linarith
  exact p5_implies_p1_of_annulusTransfer q μ hμθ hP5θ hAnnulusTransfer

end

end PottsContinuity.Thm3.Easy
