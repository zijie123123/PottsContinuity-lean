module

public import PottsContinuity.Thm1.FiniteESStatusAtoms
public import PottsContinuity.Thm1.FiniteESCylinder

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESSignatureSumsVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESSignatureSumsEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESSignatureSumsConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

theorem pottsES_sum_weighted_signature
    {α Status : Type*} [Fintype α] [Fintype Status] [DecidableEq Status]
    (w : α → ℝ) (F : Status → ℝ) (sig : α → Status) :
    (∑ a, w a * F (sig a)) =
      ∑ status, (∑ a, if sig a = status then w a else 0) * F status := by
  classical
  calc
    (∑ a, w a * F (sig a)) =
        ∑ a, ∑ s, (if sig a = s then w a else 0) * F s := by
      congr 1
      funext a
      simp
    _ = ∑ s, ∑ a, (if sig a = s then w a else 0) * F s := by
      rw [Finset.sum_comm]
    _ = ∑ status, (∑ a, if sig a = status then w a else 0) * F status := by
      congr 1
      funext status
      rw [← Finset.sum_mul]

theorem pottsES_cylinder_event_status_sum
    (V : Finset (ℤ × ℤ)) (q : ℕ) (hq : 1 ≤ q) (β : ℝ) (hβ : 0 < β)
    (i : Fin q) (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (hObs : observed ⊆ V) :
    pottsEventProb V β i (fun σ => ∀ x ∈ observed, σ x = ξ x) =
      ∑ s : pottsESStatusSignature observed,
        (∑ A : Configuration (pottsESGraph V),
          if pottsESObservedStatusSignature V observed A = s then
            configurationProbability (pottsESGraph V)
              (pottsESParameters q β hq hβ) (pottsESBoundaryCondition V) A
          else 0) * pottsESStatusPatternFunctional hq i ξ observed s := by
  classical
  rw [pottsES_cylinder_event_connectivity_pattern V q hq β hβ i observed ξ]
  simp_rw [pottsESConnectivityPatternFunctional_eq_statusSignature
    V observed hq i ξ _ hObs]
  exact pottsES_sum_weighted_signature
    (fun A => configurationProbability (pottsESGraph V)
      (pottsESParameters q β hq hβ) (pottsESBoundaryCondition V) A)
    (pottsESStatusPatternFunctional hq i ξ observed)
    (pottsESObservedStatusSignature V observed)

end

end PottsContinuity.Thm1
