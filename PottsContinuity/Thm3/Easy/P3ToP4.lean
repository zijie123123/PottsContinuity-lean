module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Foundations.Bridges
public import PottsContinuity.Foundations.BoxBoundary
public import PottsContinuity.WellDefined.Uniqueness
public import PottsContinuity.PD.Defs.IsRCInfiniteVolumeLimit
public import PottsContinuity.PD.CorrLength.CorrelationRate
public import PottsContinuity.PD.CorrLength.ConnectionEvents
public import PottsContinuity.PD.CorrLength.Positivity
public import PottsContinuity.PD.Duality.ConnectionEvents
public import PottsContinuity.PD.Duality.Decay
public import PottsContinuity.PD.Duality.DiagonalComparison

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PottsContinuity.Thm3.Easy

open PottsContinuity

private theorem frozen_limit_to_pd_box_limit
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (i : Fin 2)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q i μ) :
    PottsContinuity.PD.IsRCInfiniteVolumeLimit p q i μ := by
  classical
  change IsProbabilityMeasure μ ∧ _
  refine ⟨hμ.1, ?_⟩
  intro A ξ
  have hmono : Monotone box := WellDefined.box_monotone
  have hexhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ box n := WellDefined.box_exhausts
  have hbox := hμ.2 box hmono hexhaust A ξ
  refine hbox.congr' (Eventually.of_forall fun n => ?_)
  unfold rcEventProb
  apply Fintype.sum_equiv (Equiv.refl _)
  intro ω
  split_ifs with h₁ h₂ h₂
  · exact Foundations.rcProb_eq_PD (box n) p q i ω
  · exact (h₂ h₁).elim
  · exact (h₁ h₂).elim
  · rfl

private theorem corrConnectionEvent_eq_dualityConnectionEvent (u v : ℤ × ℤ) :
    PottsContinuity.PD.CorrLength.connectionEvent u v =
      PottsContinuity.PD.Duality.connectionEvent u v := by
  ext ω
  simp only [PottsContinuity.PD.Duality.connectionEvent,
    PottsContinuity.PD.Duality.cluster, Set.mem_ofPred_eq]
  exact PottsContinuity.PD.CorrLength.connectionEvent_iff_rcInfiniteReachable u v ω

private theorem pairZero_eq_pair : (0 : ℤ × ℤ) = ((0 : ℤ), (0 : ℤ)) := by
  ext <;> rfl

private theorem frozenConnectionEvent_eq_dualityConnectionEvent (x : ℤ × ℤ) :
    {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) x} =
      PottsContinuity.PD.Duality.connectionEvent 0 x := by
  ext ω
  change (rcInfiniteOpenGraph ω).Reachable (0, 0) x ↔
    (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable 0 x
  rw [pairZero_eq_pair]
  rw [Foundations.rcInfiniteOpenGraph_eq_PD]

private theorem boxDiagonal_mem_vertexBoundary (n : ℕ) :
    ((n : ℤ), (n : ℤ)) ∈ vertexBoundary (box n) := by
  rw [Foundations.vertexBoundary_box_eq]
  simp

/-- P3 implies the frozen P4 logarithmic boundary-connection limit. The
diagonal rate is forced to vanish by the infinite susceptibility assumption;
diagonal comparison then upgrades any positive rate to full exponential decay. -/
theorem p3_implies_p4
    (p : Set.Icc (0 : ℝ) 1) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 0 μ)
    (hχ : ∑' x : ℤ × ℤ, μ {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) x} = ⊤) :
    Tendsto
      (fun n : ℕ => 1 / (n : ℝ) * Real.log
        (μ.real {ω | ∃ y ∈ vertexBoundary (box n),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y}))
      atTop (𝓝 0) := by
  cases Foundations.squareLattice_eq_PD
  let θ : PottsContinuity.PD.FK.Parameters :=
    { val := (q : ℝ)
      property := hq
      edgeProbability := ⟨(p : ℝ), hp0, hp1⟩ }
  have hμPD : PottsContinuity.PD.IsRCInfiniteVolumeLimit p q 0 μ :=
    frozen_limit_to_pd_box_limit p q 0 μ hμ
  let μPD := μ
  have hμPD' : PottsContinuity.PD.IsRCInfiniteVolumeLimit p q 0 μPD := hμPD
  let : IsProbabilityMeasure μ := hμ.1
  let : IsProbabilityMeasure μPD := hμPD'.1
  have hχPD :
      ∑' x : ℤ × ℤ,
        μPD (PottsContinuity.PD.Duality.connectionEvent 0 x) = ⊤ := by
    change ∑' x : ℤ × ℤ,
      μ (PottsContinuity.PD.Duality.connectionEvent 0 x) = ⊤
    simpa only [frozenConnectionEvent_eq_dualityConnectionEvent] using hχ
  obtain ⟨a, ha, hsiteRate⟩ :=
    PottsContinuity.PD.CorrLength.diagonalSite_correlation_rate_exists θ μPD hμPD'
  have hdiagSiteRate : Tendsto
      (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (μPD.real (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
          (PottsContinuity.PD.diagonalSite n))))
      atTop (𝓝 (a / 2)) := by
    convert hsiteRate using 1
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      field_simp [hnR];
      rfl
  have hdiagSiteRate' : Tendsto
      (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (PottsContinuity.PD.Duality.twoPoint μPD
          (PottsContinuity.PD.diagonalSite n)))
      atTop (𝓝 (a / 2)) := by
    have hprob (n : ℕ) :
        μPD.real (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
          (PottsContinuity.PD.diagonalSite n)) =
        μPD.real (PottsContinuity.PD.Duality.connectionEvent (0, 0)
          (PottsContinuity.PD.diagonalSite n)) := by
      rw [corrConnectionEvent_eq_dualityConnectionEvent]
    have heq :
        (fun n : ℕ => -Real.log
          (μPD.real (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
            (PottsContinuity.PD.diagonalSite n))) / (n : ℝ)) =
        (fun n : ℕ => -Real.log
          (μPD.real (PottsContinuity.PD.Duality.connectionEvent (0, 0)
            (PottsContinuity.PD.diagonalSite n))) / (n : ℝ)) := by
      funext n
      rw [hprob n]
    have hrateDuality : Tendsto
        (fun n : ℕ => -Real.log
          (μPD.real (PottsContinuity.PD.Duality.connectionEvent (0, 0)
            (PottsContinuity.PD.diagonalSite n))) / (n : ℝ))
        atTop (𝓝 (a / 2)) := by
      rw [← heq]
      exact hsiteRate
    have hzeroFun :
        (fun n : ℕ => -Real.log
          (μPD.real (PottsContinuity.PD.Duality.connectionEvent 0
            (PottsContinuity.PD.diagonalSite n))) / (n : ℝ)) =
        (fun n : ℕ => -Real.log
          (μPD.real (PottsContinuity.PD.Duality.connectionEvent (0, 0)
            (PottsContinuity.PD.diagonalSite n))) / (n : ℝ)) := by
      funext n
      rw [pairZero_eq_pair]
    have hrateZero : Tendsto
        (fun n : ℕ => -Real.log
          (μPD.real (PottsContinuity.PD.Duality.connectionEvent 0
            (PottsContinuity.PD.diagonalSite n))) / (n : ℝ))
        atTop (𝓝 (a / 2)) := by
      rw [hzeroFun]
      exact hrateDuality
    have htwoPointFun :
        (fun n : ℕ => -Real.log
          (μPD.real (PottsContinuity.PD.Duality.connectionEvent 0
            (PottsContinuity.PD.diagonalSite n))) / (n : ℝ)) =
        (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
          (PottsContinuity.PD.Duality.twoPoint μPD
            (PottsContinuity.PD.diagonalSite n))) := by
      funext n
      simp only [PottsContinuity.PD.Duality.twoPoint]
      by_cases hn : n = 0
      · simp [hn]
      · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        field_simp [hnR];
        rfl
    rw [← htwoPointFun]
    exact hrateZero
  have hzero : a = 0 := by
    by_contra hne
    have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm hne)
    have hL : 0 < a / 2 := by linarith
    obtain ⟨C, c, hC, hc, hdecay⟩ :=
      PottsContinuity.PD.Duality.free_exponential_decay_of_pos_diagonal_rate
        θ μPD hμPD' (a / 2) hL hdiagSiteRate'
    have hRealBound : ∀ x : ℤ × ℤ,
        μPD.real (PottsContinuity.PD.Duality.connectionEvent 0 x) ≤
          C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|)) := by
      intro x
      have h := hdecay x
      change μPD.real (PottsContinuity.PD.Duality.connectionEvent 0 x) ≤ _ at h
      exact h
    have hENNBound : ∀ x : ℤ × ℤ,
        μPD (PottsContinuity.PD.Duality.connectionEvent 0 x) ≤
          ENNReal.ofReal (C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) := by
      intro x
      rw [← MeasureTheory.ofReal_measureReal (μ := μPD)
        (s := PottsContinuity.PD.Duality.connectionEvent 0 x)
        (measure_ne_top μPD (PottsContinuity.PD.Duality.connectionEvent 0 x))]
      exact ENNReal.ofReal_le_ofReal (hRealBound x)
    have hfinite := PottsContinuity.PD.Duality.susceptibility_ne_top_of_exponential_decay
      μPD (0, 0) C c hc hENNBound
    exact hfinite hχPD
  have hsiteZero : Tendsto
      (fun n : ℕ => -(1 / (n : ℝ)) * Real.log
        (μPD.real (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
          (PottsContinuity.PD.diagonalSite n))))
      atTop (𝓝 0) := by
    simpa only [hzero, zero_div] using hdiagSiteRate
  have hdoubleAtTop : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have hdiagonalRate : Tendsto
      (fun n : ℕ => -Real.log
        (μPD.real (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
          ((n : ℤ), (n : ℤ)))) / (n : ℝ)) atTop (𝓝 0) := by
    have hcomp := hsiteZero.comp hdoubleAtTop
    have hrewritten : Tendsto
        (fun n : ℕ => 2 * (-(1 / ((2 * n : ℕ) : ℝ)) * Real.log
          (μPD.real (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
            (PottsContinuity.PD.diagonalSite (2 * n))))))
        atTop (𝓝 0) := by simpa using hcomp.const_mul 2
    refine hrewritten.congr' (Eventually.of_forall fun n => ?_)
    simp only [PottsContinuity.PD.diagonalSite]
    have hsite : (2 * n) / 2 = n := by omega
    rw [hsite]
    by_cases hn : n = 0
    · simp [hn]
    · have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hmul : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_num
      rw [hmul]
      field_simp
  have hdiagProbPos (n : ℕ) :
      0 < μPD.real (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
        ((n : ℤ), (n : ℤ))) :=
    PottsContinuity.PD.CorrLength.isRCInfiniteVolumeLimit_connection_positive
      θ μPD hμPD' (0, 0) ((n : ℤ), (n : ℤ))
  let boundaryProb : ℕ → ℝ := fun n =>
    μPD.real {ω | ∃ y ∈ vertexBoundary (box n),
      (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable (0, 0) y}
  have hboundaryProb_eq_frozen (n : ℕ) : boundaryProb n =
      μ.real {ω | ∃ y ∈ vertexBoundary (box n),
        (rcInfiniteOpenGraph ω).Reachable (0, 0) y} := by
    dsimp [boundaryProb]
    congr 1
  have hdiagLeBoundary (n : ℕ) :
      μPD.real (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
        ((n : ℤ), (n : ℤ))) ≤ boundaryProb n := by
    refine measureReal_mono ?_ (measure_ne_top μPD _)
    intro ω hω
    refine ⟨((n : ℤ), (n : ℤ)), boxDiagonal_mem_vertexBoundary n, ?_⟩
    have hreach := (PottsContinuity.PD.CorrLength.connectionEvent_iff_rcInfiniteReachable
      (0, 0) ((n : ℤ), (n : ℤ)) ω).mp hω
    exact hreach
  have hboundaryPos (n : ℕ) : 0 < boundaryProb n :=
    lt_of_lt_of_le (hdiagProbPos n) (hdiagLeBoundary n)
  have hboundaryLeOne (n : ℕ) : boundaryProb n ≤ 1 := by
    exact measureReal_le_one
  have hboundaryRate : Tendsto
      (fun n : ℕ => -Real.log (boundaryProb n) / (n : ℝ)) atTop (𝓝 0) := by
    have hbound : ∀ᶠ n : ℕ in atTop,
        0 ≤ -Real.log (boundaryProb n) / (n : ℝ) ∧
          -Real.log (boundaryProb n) / (n : ℝ) ≤
            -Real.log (μPD.real
              (PottsContinuity.PD.CorrLength.connectionEvent (0, 0)
                ((n : ℤ), (n : ℤ)))) / (n : ℝ) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
      have hlogB : Real.log (boundaryProb n) ≤ 0 := by
        rw [← Real.log_one]
        exact Real.log_le_log (hboundaryPos n) (hboundaryLeOne n)
      have hlogMono := Real.log_le_log (hdiagProbPos n) (hdiagLeBoundary n)
      constructor
      · exact div_nonneg (neg_nonneg.mpr hlogB) hnpos.le
      · apply (div_le_div_iff₀ hnpos hnpos).2
        have hlog := neg_le_neg hlogMono
        exact mul_le_mul_of_nonneg_right hlog hnpos.le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hdiagonalRate (hbound.mono fun _ h => h.1)
        (hbound.mono fun _ h => h.2)
  have hboundaryNeg : Tendsto
      (fun n : ℕ => -(-Real.log (boundaryProb n) / (n : ℝ))) atTop (𝓝 0) := by
    simpa using hboundaryRate.neg
  have hboundaryFrozen : Tendsto
      (fun n : ℕ => -Real.log
        (μ.real {ω | ∃ y ∈ vertexBoundary (box n),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y}) / (n : ℝ)) atTop (𝓝 0) := by
    have hfun : (fun n : ℕ => -Real.log (boundaryProb n) / (n : ℝ)) =
        (fun n : ℕ => -Real.log
          (μ.real {ω | ∃ y ∈ vertexBoundary (box n),
            (rcInfiniteOpenGraph ω).Reachable (0, 0) y}) / (n : ℝ)) := by
      funext n
      rw [hboundaryProb_eq_frozen]
    rw [← hfun]
    exact hboundaryRate
  have hboundaryFrozenNeg : Tendsto
      (fun n : ℕ => -(-Real.log
        (μ.real {ω | ∃ y ∈ vertexBoundary (box n),
          (rcInfiniteOpenGraph ω).Reachable (0, 0) y}) / (n : ℝ))) atTop (𝓝 0) := by
    simpa using hboundaryFrozen.neg
  exact hboundaryFrozenNeg.congr' (Eventually.of_forall fun n => by ring)

end PottsContinuity.Thm3.Easy
