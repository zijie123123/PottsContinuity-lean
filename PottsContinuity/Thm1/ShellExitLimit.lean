module

public import PottsContinuity.Thm1.ShellExitComparison
public import PottsContinuity.PD.RCInfinite.ClusterEvents
public import Mathlib.MeasureTheory.Measure.Continuity

@[expose] public section

namespace PottsContinuity.Thm1

open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

private theorem pottsESExit_nested_mono (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1)) : Monotone V := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
    have hm0 : m = 0 := by omega
    subst m
    exact Finset.Subset.rfl
  | succ n ih =>
    by_cases hm' : m ≤ n
    · exact (ih (by omega)).trans (hNest n)
    · have hmn : m = n + 1 := by omega
      subst m
      exact Finset.Subset.rfl

private theorem pottsESExit_finset_eventually_contained
    (V : ℕ → Finset (ℤ × ℤ)) (hMono : Monotone V)
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (F : Finset (ℤ × ℤ)) : ∃ n, F ⊆ V n := by
  induction F using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert x F hx ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨n, hn⟩ := hExhaust x
    refine ⟨max m n, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hMono (Nat.le_max_right m n) hn
    · exact hMono (Nat.le_max_left m n) (hm hy)

/-- Along every nested exhaustion, the infinite-volume probability of reaching
outside the current vertex set decreases to the origin infinite-cluster mass. -/
theorem pottsESLatticeExitProbability_tendsto_infiniteAt
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ] :
    Tendsto (fun n => μ.real (pottsESLatticeExitEvent (V n))) atTop
      (𝓝 (μ.real (infiniteAt (0, 0)))) := by
  have hMono := pottsESExit_nested_mono V hNest
  have hAntitone : Antitone (fun n => pottsESLatticeExitEvent (V n)) := by
    intro m n hmn ω hω
    obtain ⟨y, hy, hpath⟩ := hω
    exact ⟨y, fun hym => hy (hMono hmn hym), hpath⟩
  have hInter : (⋂ n, pottsESLatticeExitEvent (V n)) = infiniteAt (0, 0) := by
    ext ω
    simp only [Set.mem_iInter]
    constructor
    · intro hω
      apply (infinite_cluster_iff ω (0, 0)).2
      intro F
      obtain ⟨n, hn⟩ := pottsESExit_finset_eventually_contained V hMono hExhaust F
      obtain ⟨y, hy, hpath⟩ := hω n
      exact ⟨y, fun hyF => hy (hn hyF), hpath⟩
    · intro hω n
      have hinf : (cluster ω (0, 0)).Infinite := by
        simpa [infiniteAt] using hω
      obtain ⟨y, hy, hpath⟩ := (infinite_cluster_iff ω (0, 0)).mp hinf (V n)
      exact ⟨y, hy, hpath⟩
  have hmeas (n : ℕ) : NullMeasurableSet (pottsESLatticeExitEvent (V n)) μ := by
    by_cases h0 : (0, 0) ∈ V n
    · exact (pottsESLatticeExitEvent_isCylinder (V n) h0).measurableSet.nullMeasurableSet
    · have heq : pottsESLatticeExitEvent (V n) = Set.univ := by
        ext ω
        constructor
        · intro _
          trivial
        · intro _
          exact ⟨(0, 0), h0, SimpleGraph.Reachable.refl _⟩
      rw [heq]
      exact MeasurableSet.univ.nullMeasurableSet
  have hfinite : ∃ n, μ (pottsESLatticeExitEvent (V n)) ≠ ⊤ :=
    ⟨0, measure_ne_top μ _⟩
  have hENN : Tendsto (fun n => μ (pottsESLatticeExitEvent (V n))) atTop
      (𝓝 (μ (infiniteAt (0, 0)))) := by
    rw [← hInter]
    change Tendsto (μ ∘ fun n => pottsESLatticeExitEvent (V n)) atTop
      (𝓝 (μ (⋂ n, pottsESLatticeExitEvent (V n))))
    exact tendsto_measure_iInter_atTop hmeas hAntitone hfinite
  have hreal := (ENNReal.continuousAt_toReal (measure_ne_top μ _)).tendsto.comp hENN
  change Tendsto (fun n => (μ (pottsESLatticeExitEvent (V n))).toReal) atTop
    (𝓝 ((μ (infiniteAt (0, 0))).toReal)) at hreal
  simpa only [Measure.real_def] using hreal

end

end PottsContinuity.Thm1
