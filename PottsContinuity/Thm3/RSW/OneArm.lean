module

public import PottsContinuity.Thm3.RSW.Analytic
public import PottsContinuity.Foundations.Bridges
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.PD.CorrLength.Positivity

/-!
# The exact frozen one-arm event and its logarithmic rate

The free-limit bridge specializes the frozen every-exhaustion predicate to boxes.
Strict positivity is imported from the proved PD finite-path positivity theorem,
with the event and boundary carriers explicitly transported. No identification of
an interior parameter with the critical point is used here.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.RSW

/-- The real one-arm probability appearing in frozen P4, including radius zero. -/
noncomputable def oneArmProbability
    (μ : Measure (squareLattice.edgeSet → Bool)) (n : ℕ) : ℝ :=
  μ.real {ω | ∃ y ∈ vertexBoundary (box n), (rcInfiniteOpenGraph ω).Reachable (0, 0) y}

/-- The exact finite-volume crossing probability in frozen P5, with the prescribed
floor convention for both right endpoints and an actual open crossing. -/
noncomputable def bufferedCrossingProbability (p : Set.Icc (0 : ℝ) 1)
    (q : Set.Ioi (0 : ℝ)) (α : ℝ) (n : ℕ) : ℝ :=
  rcEventProb
    (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n)) p q 0
    (horizontalCrossing
      (latticeRectangle (-(n : ℤ)) ⌊(α + 1) * n⌋ (-(n : ℤ)) (2 * n)) 0 ⌊α * n⌋ 0 n)

/-- Specializing every monotone induced exhaustion to boxes gives the PD limit
predicate. This theorem is free-only; no wired-boundary convention is suppressed. -/
theorem free_limit_to_PD (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 0 μ) :
    PD.IsRCInfiniteVolumeLimit p q 0 μ := by
  classical
  have hmono : Monotone box := by
    intro n m hnm x hx
    simp only [box, Finset.mem_product, Finset.mem_Icc] at hx ⊢
    omega
  have hexhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ box n := by
    intro x
    refine ⟨x.1.natAbs + x.2.natAbs, ?_⟩
    simp only [box, Finset.mem_product, Finset.mem_Icc, Nat.cast_add,
      Int.natCast_natAbs]
    have hx := abs_nonneg x.1
    have hy := abs_nonneg x.2
    have hx' := (abs_le.mp (le_refl |x.1|))
    have hy' := (abs_le.mp (le_refl |x.2|))
    omega
  refine ⟨hμ.1, ?_⟩
  intro A ξ
  have h := hμ.2 box hmono hexhaust A ξ
  refine h.congr' (Eventually.of_forall fun n => ?_)
  unfold rcEventProb
  apply Fintype.sum_equiv (Equiv.refl _)
  intro ω
  split_ifs with h₁ h₂ h₂
  · exact Foundations.rcProb_eq_PD (box n) p q 0 ω
  · exact (h₂ h₁).elim
  · exact (h₁ h₂).elim
  · rfl

/-- The point `(n,0)` is a boundary vertex for every radius, including zero. -/
theorem axis_mem_vertexBoundary_box (n : ℕ) :
    ((n : ℤ), 0) ∈ vertexBoundary (box n) := by
  rw [Foundations.vertexBoundary_eq_PD]
  refine ⟨?_, ((n : ℤ) + 1, 0), ?_, ?_⟩
  · simp only [box, Finset.mem_product, Finset.mem_Icc]
    omega
  · change |(n : ℤ) - ((n : ℤ) + 1)| + |(0 : ℤ) - 0| = 1
    simp only [sub_add_cancel_left, abs_neg, abs_one, sub_self, abs_zero, add_zero]
  · simp only [box, Finset.mem_product, Finset.mem_Icc]
    omega

/-- Genuine strict positivity of the frozen one-arm probability at every scale,
for any free infinite-volume limit with `q ≥ 1` and an interior edge parameter. -/
theorem oneArmProbability_pos (θ : PD.FK.Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) (n : ℕ) :
    0 < oneArmProbability μ n := by
  let : IsProbabilityMeasure μ := hμ.1
  have hpos := PD.CorrLength.isRCInfiniteVolumeLimit_connection_positive θ μ
    (free_limit_to_PD θ.toP θ.toQ μ hμ) (0, 0) ((n : ℤ), 0)
  have hsub : PD.CorrLength.connectionEvent (0, 0) ((n : ℤ), 0) ⊆
      {ω | ∃ y ∈ vertexBoundary (box n), (rcInfiniteOpenGraph ω).Reachable (0, 0) y} := by
    intro ω hω
    refine ⟨((n : ℤ), 0), axis_mem_vertexBoundary_box n, ?_⟩
    exact (PD.CorrLength.connectionEvent_iff_rcInfiniteReachable _ _ ω).mp hω
  exact lt_of_lt_of_le hpos (measureReal_mono hsub)

/-- Frozen P4 excludes an eventual exponential upper bound. All model positivity
is proved above; no positivity or decay-upgrade assumption is added to this result. -/
theorem oneArm_not_exponential_of_log_rate_zero (θ : PD.FK.Parameters)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (hrate : Tendsto (fun n : ℕ => 1 / (n : ℝ) * Real.log (oneArmProbability μ n))
      atTop (𝓝 0)) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      oneArmProbability μ n ≤ Real.exp (-c * (n : ℝ)) := by
  exact not_exponential_decay_of_log_rate_zero (oneArmProbability μ)
    (Eventually.of_forall (oneArmProbability_pos θ μ hμ)) hrate

end PottsContinuity.RSW
