module

public import PottsContinuity.Thm3.Easy.P1ToP2
public import PottsContinuity.Infinite.ComparisonStatements
public import PottsContinuity.PD.FK.CylinderDetermination
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion
public import PottsContinuity.PD.Duality.ConnectionEvents

/-!
# Conditional closure of P1 ⇒ P2 from an outermost-circuit DMP hypothesis

The barrier family and its finite-volume random-domain DMP comparison are
explicit inputs. The barrier hypotheses state exactly the measurable,
increasing, and exhaustive properties needed to send its error probability to
zero. This is a conditional helper, not the unconditional P1 ⇒ P2 theorem.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Thm3.Easy

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

/-- The wired/free measure comparison follows from an explicit outermost-circuit
DMP inequality and exhaustion of the barrier events under P1. To use this for
P1 ⇒ P2, the caller must instantiate `barrier k M` with the event that a selected
exterior-most closed-dual circuit around `Λ_k` is contained in `Λ_M`; the
no-circuit error in the DMP premise is its complement. The type does not assert
that geometric identity. The DMP inequality and the barrier measurability,
monotonicity, and exhaustion properties are all explicit premises. -/
theorem p1_implies_p2_of_outermostCircuitDMP
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (μ₀ μ₁ : Measure (squareLattice.edgeSet → Bool))
    (hμ₀ : IsRCInfiniteVolumeLimit p q 0 μ₀)
    (hμ₁ : IsRCInfiniteVolumeLimit p q 1 μ₁)
    (hP1 : μ₁ {ω | {x | (rcInfiniteOpenGraph ω).Reachable (0, 0) x}.Infinite} = 0)
    (barrier : ℕ → ℕ → Set (squareLattice.edgeSet → Bool))
    (hbarrier_measurable : ∀ k M, MeasurableSet (barrier k M))
    (hbarrier_mono : ∀ k {M N}, M ≤ N → barrier k M ⊆ barrier k N)
    (hbarrier_exhausts : ∀ k ω,
      (∀ x : ℤ × ℤ, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Finite) →
        ∃ M, ω ∈ barrier k M)
    (hDMP : ∀ k M, k ≤ M →
      ∀ {A : Set LatticeConfiguration}, IsCylinder A →
        DependsOn (boxEdges (0, 0) k) A → IsUpperSet A →
          μ₁.real A ≤ μ₀.real A + μ₁.real (barrier k M)ᶜ) :
    μ₀ = μ₁ := by
  cases Foundations.squareLattice_eq_PD
  let : IsProbabilityMeasure μ₀ := hμ₀.1
  let : IsProbabilityMeasure μ₁ := hμ₁.1
  have hfinite := wired_all_clusters_finite_ae p q hq μ₁ hμ₁ hP1
  let ν₀ : ProbabilityMeasure LatticeConfiguration := ⟨μ₀, hμ₀.1⟩
  let ν₁ : ProbabilityMeasure LatticeConfiguration := ⟨μ₁, hμ₁.1⟩
  have hbarrier_error_tendsto (k : ℕ) :
      Tendsto (fun M => μ₁.real (barrier k M)ᶜ) atTop (𝓝 0) := by
    have hcover : ∀ᵐ ω ∂μ₁, ∃ M, ω ∈ barrier k M := by
      filter_upwards [hfinite] with ω hω
      exact hbarrier_exhausts k ω hω
    have hacc (M : ℕ) :
        Set.accumulate (fun n => barrier k n) M = barrier k M := by
      ext ω
      rw [Set.mem_accumulate]
      constructor
      · rintro ⟨N, hNM, hω⟩
        exact hbarrier_mono k hNM hω
      · intro hω
        exact ⟨M, le_rfl, hω⟩
    have hcoverUnion : ∀ᵐ ω ∂μ₁, ω ∈ ⋃ M, barrier k M := by
      filter_upwards [hcover] with ω hω
      exact Set.mem_iUnion.mpr hω
    have hnull : μ₁ (⋃ M, barrier k M)ᶜ = 0 := by
      have hnull' := (ae_iff).1 hcoverUnion
      change μ₁ (⋃ M, barrier k M)ᶜ = 0 at hnull'
      exact hnull'
    have hunion : μ₁ (⋃ M, barrier k M) = 1 := by
      have hadd := measure_add_measure_compl (μ := μ₁)
        (MeasurableSet.iUnion (fun M => hbarrier_measurable k M))
      rw [hnull, measure_univ] at hadd
      simpa using hadd
    have hprob : Tendsto (fun M => μ₁ (barrier k M)) atTop
        (𝓝 (μ₁ (⋃ M, barrier k M))) := by
      have h := tendsto_measure_iUnion_accumulate (μ := μ₁)
        (s := fun M => barrier k M)
      have h' : Tendsto (fun M => μ₁ (Set.accumulate (fun n => barrier k n) M))
          atTop (𝓝 (μ₁ (⋃ M, barrier k M))) := h
      refine h'.congr' ?_
      filter_upwards with M
      rw [hacc M]
    have hprobOne : Tendsto (fun M => μ₁ (barrier k M)) atTop (𝓝 1) := by
      simpa [hunion] using hprob
    have hreal : Tendsto (fun M => μ₁.real (barrier k M)) atTop (𝓝 1) := by
      have h' := (ENNReal.tendsto_toReal_iff
        (fun M => measure_ne_top μ₁ (barrier k M)) ENNReal.one_ne_top).2 hprobOne
      simpa [Measure.real] using h'
    have hcompl (M : ℕ) :
        μ₁.real (barrier k M)ᶜ = 1 - μ₁.real (barrier k M) := by
      rw [measureReal_compl (hbarrier_measurable k M)]
      simp [Measure.real, hμ₁.1.measure_univ]
    rw [show (0 : ℝ) = 1 - 1 by norm_num]
    simpa only [hcompl] using tendsto_const_nhds.sub hreal
  have hwired_le_free_allOpen (F : Finset squareLattice.edgeSet) :
      μ₁.real (LatticeConfiguration.allOpen F) ≤ μ₀.real
        (LatticeConfiguration.allOpen F) := by
    obtain ⟨k, hk⟩ := exists_box_supporting_edge_finset F
    let A : Set LatticeConfiguration := LatticeConfiguration.allOpen F
    have hA : IsCylinder A := isCylinder_allOpen F
    have hdep : DependsOn (boxEdges (0, 0) k) A :=
      allOpen_dependsOn_box F (fun e he => hk e he)
    have hupper : IsUpperSet A := PottsContinuity.PD.Duality.allOpen_isUpperSet F
    have hconst : Tendsto (fun _ : ℕ => μ₀.real A) atTop (𝓝 (μ₀.real A)) :=
      tendsto_const_nhds
    have hRHS : Tendsto
        (fun M => μ₀.real A + μ₁.real (barrier k M)ᶜ) atTop (𝓝 (μ₀.real A)) := by
      simpa using hconst.add (hbarrier_error_tendsto k)
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hRHS
    filter_upwards [eventually_ge_atTop k] with M hkM
    exact hDMP k M hkM hA hdep hupper
  have hprobEq : ν₀ = ν₁ :=
    PottsContinuity.PD.FK.LatticeConfiguration.probabilityMeasure_eq_of_allOpen
      (fun F => by
        obtain ⟨k, hk⟩ := exists_box_supporting_edge_finset F
        let A : Set LatticeConfiguration := LatticeConfiguration.allOpen F
        have hA : IsCylinder A := isCylinder_allOpen F
        have hdep : DependsOn (boxEdges (0, 0) k) A :=
          allOpen_dependsOn_box F (fun e he => hk e he)
        have hupper : IsUpperSet A :=
          PottsContinuity.PD.Duality.allOpen_isUpperSet F
        have h₁₀ : μ₁.real A ≤ μ₀.real A := by
          have hconst : Tendsto (fun _ : ℕ => μ₀.real A) atTop (𝓝 (μ₀.real A)) :=
            tendsto_const_nhds
          have hRHS : Tendsto
              (fun M => μ₀.real A + μ₁.real (barrier k M)ᶜ) atTop
              (𝓝 (μ₀.real A)) := by
            simpa using hconst.add (hbarrier_error_tendsto k)
          apply le_of_tendsto_of_tendsto tendsto_const_nhds hRHS
          filter_upwards [eventually_ge_atTop k] with M hkM
          exact hDMP k M hkM hA hdep hupper
        have h₀₁ :=
          PottsContinuity.Infinite.free_infinite_le_wired_infinite_local
            p q hp0 hp1 hq μ₀ μ₁ hμ₀ hμ₁ k hA hdep hupper
        have hreal : μ₀.real A = μ₁.real A := le_antisymm h₀₁ h₁₀
        have hmeasureVal : μ₀ A = μ₁ A :=
          (MeasureTheory.measureReal_eq_measureReal_iff
            (μ := μ₀) (ν := μ₁) (s := A) (t := A)
            (measure_ne_top μ₀ A) (measure_ne_top μ₁ A)).mp hreal
        change ((μ₀ : Measure LatticeConfiguration) A).toNNReal =
          ((μ₁ : Measure LatticeConfiguration) A).toNNReal
        exact congrArg ENNReal.toNNReal hmeasureVal)
  exact congrArg Subtype.val hprobEq

end PottsContinuity.Thm3.Easy
