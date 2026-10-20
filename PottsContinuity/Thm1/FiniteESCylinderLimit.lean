module

public import PottsContinuity.Thm1.FiniteESSignatureAtomLimit

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.RCInfinite

noncomputable section

local instance pottsESCylinderLimitVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESCylinderLimitEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESCylinderLimitConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

private theorem pottsESStatusVolume_monotone
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1)) : Monotone V := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    exact Finset.Subset.rfl
  | succ n ih =>
    by_cases hmn' : m ≤ n
    · exact (ih (by omega)).trans (hNest n)
    · have hm : m = n + 1 := by omega
      subst m
      exact Finset.Subset.rfl

private theorem pottsESStatus_subset_eventually
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (observed : Finset (ℤ × ℤ)) : ∃ N, observed ⊆ V N := by
  have hMono := pottsESStatusVolume_monotone V hNest
  induction observed using Finset.induction_on with
  | empty => exact ⟨0, Finset.empty_subset _⟩
  | @insert x observed hx ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨n, hn⟩ := hExhaust x
    refine ⟨max m n, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with hyx | hyObs
    · subst y
      exact hMono (Nat.le_max_right m n) hn
    · exact hMono (Nat.le_max_left m n) (hm hyObs)

theorem pottsES_pottsCylinder_probability_tendsto
    (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin q) (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (V : ℕ → Finset (ℤ × ℤ))
    (hNest : ∀ n, V n ⊆ V (n + 1))
    (hExhaust : ∀ x : ℤ × ℤ, ∃ n, x ∈ V n)
    (μ : Measure LatticeConfiguration)
    (hμ : PD.IsRCInfiniteVolumeLimit
      (pottsESParameters q β hq hβ).toP
      (pottsESParameters q β hq hβ).toQ 1 μ) :
    Tendsto
      (fun n => pottsEventProb (V n) β i
        (fun σ => ∀ x ∈ observed, σ x = ξ x))
      atTop
      (𝓝 (∑ s : pottsESStatusSignature observed,
        μ.real (pottsESConnectionInfiniteFullSignatureEvent
          (pottsESStatusPositivePairs observed s)
          (pottsESStatusNegativePairs observed s)
          (pottsESStatusGhostPositive observed s)
          (pottsESStatusGhostNegative observed s)) *
        pottsESStatusPatternFunctional hq i ξ observed s)) := by
  classical
  let θ := pottsESParameters q β hq hβ
  have hAtom (s : pottsESStatusSignature observed) :
      Tendsto
        (fun n => ∑ A : Configuration (pottsESGraph (V n)),
          if pottsESObservedStatusSignature (V n) observed A = s then
            configurationProbability (pottsESGraph (V n)) θ
              (pottsESBoundaryCondition (V n)) A
          else 0)
        atTop
        (𝓝 (μ.real (pottsESConnectionInfiniteFullSignatureEvent
          (pottsESStatusPositivePairs observed s)
          (pottsESStatusNegativePairs observed s)
          (pottsESStatusGhostPositive observed s)
          (pottsESStatusGhostNegative observed s)))) := by
    exact pottsESFiniteStatusAtom_mass_tendsto θ V hNest hExhaust μ
      (by simpa [θ] using hμ) observed s
  have hSum : Tendsto
      (fun n => ∑ s : pottsESStatusSignature observed,
        (∑ A : Configuration (pottsESGraph (V n)),
          if pottsESObservedStatusSignature (V n) observed A = s then
            configurationProbability (pottsESGraph (V n)) θ
              (pottsESBoundaryCondition (V n)) A
          else 0) * pottsESStatusPatternFunctional hq i ξ observed s)
      atTop
      (𝓝 (∑ s : pottsESStatusSignature observed,
        μ.real (pottsESConnectionInfiniteFullSignatureEvent
          (pottsESStatusPositivePairs observed s)
          (pottsESStatusNegativePairs observed s)
          (pottsESStatusGhostPositive observed s)
          (pottsESStatusGhostNegative observed s)) *
        pottsESStatusPatternFunctional hq i ξ observed s)) := by
    refine tendsto_finsetSum Finset.univ (fun s hs => ?_)
    exact (hAtom s).mul_const (pottsESStatusPatternFunctional hq i ξ observed s)
  obtain ⟨N, hN⟩ := pottsESStatus_subset_eventually V hNest hExhaust observed
  have hFormula :
      (fun n : ℕ => pottsEventProb (V n) β i
        (fun σ => ∀ x ∈ observed, σ x = ξ x)) =ᶠ[atTop]
      (fun n => ∑ s : pottsESStatusSignature observed,
        (∑ A : Configuration (pottsESGraph (V n)),
          if pottsESObservedStatusSignature (V n) observed A = s then
            configurationProbability (pottsESGraph (V n)) θ
              (pottsESBoundaryCondition (V n)) A
          else 0) * pottsESStatusPatternFunctional hq i ξ observed s) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hObs : observed ⊆ V n := by
      intro x hx
      exact (pottsESStatusVolume_monotone V hNest) hn (hN hx)
    simpa [θ] using
      pottsES_cylinder_event_status_sum (V n) q hq β hβ i observed ξ hObs
  exact hSum.congr' hFormula.symm


end

end PottsContinuity.Thm1
