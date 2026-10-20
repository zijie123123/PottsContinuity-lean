module

public import PottsContinuity.Thm1.ShellExitProbabilityLimit
public import PottsContinuity.Thm1.FiniteESMagnetisation
public import PottsContinuity.PD.FK.IncreasingEvents
public import PottsContinuity.Foundations.EveryExhaustion
public import PottsContinuity.Infinite.Bridge

@[expose] public section

namespace PottsContinuity.Thm1

open Filter Topology MeasureTheory
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

local instance pottsESShellMagVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESShellMagEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESShellMagConfigurationDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

/-- The finite pinned-origin probabilities converge to the Edwards--Sokal
magnetisation determined by any wired random-cluster infinite-volume limit. -/
theorem pottsESOriginPinnedProbability_tendsto
    (q : ℕ) (hq : 2 ≤ q) (β : ℝ) (hβ : 0 < β) (i : Fin q)
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      (pottsESParameters q β (by omega) hβ).toP
      (pottsESParameters q β (by omega) hβ).toQ 1 μ) :
    Tendsto
      (fun n => pottsEventProb (V n) β i
        (fun σ => σ (0, 0) = i))
      atTop (𝓝 (1 / (q : ℝ) + (1 - 1 / (q : ℝ)) *
        μ.real (infiniteAt (0, 0)))) := by
  let θ := pottsESParameters q β (by omega) hβ
  have hOrigin : ∀ᶠ n : ℕ in atTop, (0, 0) ∈ V n := by
    obtain ⟨N, hN⟩ := hExhaust (0, 0)
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    have hSN : V N ⊆ V n := by
      induction hn with
      | refl => exact Finset.Subset.rfl
      | @step k hkn ih => exact ih.trans (hNest k)
    exact hSN hN
  have hμθ : PottsContinuity.PD.IsRCInfiniteVolumeLimit
      θ.toP θ.toQ 1 μ := by
    simpa [θ] using hμ
  have hConn := pottsESShellExitProbability_tendsto_infiniteAt
    θ V hNest hExhaust μ hμθ
  have hConnScaled := hConn.const_mul (1 - 1 / (q : ℝ))
  have hLimit : Tendsto
      (fun n => 1 / (q : ℝ) +
        (1 - 1 / (q : ℝ)) *
          (pottsESShellBondProbabilityMeasure θ (V n) :
            Measure LatticeConfiguration).real
            (pottsESLatticeExitEvent (V n)))
      atTop (𝓝 (1 / (q : ℝ) +
        (1 - 1 / (q : ℝ)) * μ.real (infiniteAt (0, 0)))) := by
    simpa using tendsto_const_nhds.add hConnScaled
  apply hLimit.congr'
  filter_upwards [hOrigin] with n h0
  rw [pottsES_finite_magnetisation_identity (V n) q hq β hβ.le i h0]
  have hprob : pottsESOriginExteriorConnectionProbability
      (V n) q (by omega) β hβ.le h0 =
      (measure (pottsESGraph (V n)) θ
        (pottsESBoundaryCondition (V n))
        {A | pottsESOriginExteriorConnected (V n) h0 A}).toReal := by
    unfold pottsESOriginExteriorConnectionProbability
    rw [dite_eq_left hβ]
    rw [measure_toReal_eq_indicator_sum]
    simp [Set.indicator, θ]
  rw [hprob]
  rw [← pottsESShellExitProbability_eq_finiteConnection θ (V n) h0]

end

end PottsContinuity.Thm1
