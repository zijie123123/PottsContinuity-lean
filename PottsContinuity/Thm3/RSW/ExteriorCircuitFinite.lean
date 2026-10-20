module

public import PottsContinuity.Thm3.RSW.LocalizedPair

/-!
# Lemma 5: the finite free arm bound

DCST TeX lines 1488–1515. The proof uses the actual finite root-cluster cover,
exterior-seed free localization, square symmetries, and a union bound. The
nonnegative series is ENNReal-valued so a divergent sum has its intended value.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- The finite localized-pair estimate in nonnegative extended-real form. -/
theorem finite_localizedPair_measure_le (θ : Parameters) (V : Finset (ℤ × ℤ))
    {m : ℕ} (t : SquareLocalizationIndex m) :
    measure (squareLattice.induce (V : Set (ℤ × ℤ))) θ (frozenBoundaryCondition V 0)
      (finiteBoolEvent V (fun ω => ω ∈ finiteConfinedConnectionEvent V
        (localizationSquare t) t.1.val (localizationPartner t))) ≤
      ENNReal.ofReal (maxSquarePairProbability θ m) := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (maxSquarePairProbability_nonneg θ m)]
  exact finite_localizedPair_probability_le_max θ V t

/-- Finite free arm bound, with the source coefficient 72 and every k≥1.
The argument does not require the arm radius to be below the ambient radius. -/
theorem exterior_circuit_finite (θ : Parameters) (k N : ℕ) (hk : 1 ≤ k) :
    ENNReal.ofReal (finiteArmProbability θ N k) ≤
      ∑' m : {m : ℕ // k ≤ m},
        ENNReal.ofReal (72 * (m.val : ℝ)^4 * maxSquarePairProbability θ m.val) := by
  classical
  let ρ := measure (squareLattice.induce (box N : Set (ℤ × ℤ))) θ
    (frozenBoundaryCondition (box N) 0)
  let E (m : {m : ℕ // k ≤ m}) (t : SquareLocalizationIndex m.val) :=
    finiteBoolEvent (box N) (fun ω => ω ∈ finiteConfinedConnectionEvent (box N)
      (localizationSquare t) t.1.val (localizationPartner t))
  have hcover : finiteBoolEvent (box N) (fun ω => ω ∈ finiteArmEvent N k) ⊆
      ⋃ m : {m : ℕ // k ≤ m}, ⋃ t : SquareLocalizationIndex m.val, E m t := by
    intro A hA
    obtain ⟨m, hkm, t, hconn, hconf, _⟩ := finiteArmEvent_boundingSquare N k
      ((boolConfigurationEquiv _).symm A) hA
    exact Set.mem_iUnion.mpr ⟨⟨m, hkm⟩, Set.mem_iUnion.mpr ⟨t, hconn, hconf⟩⟩
  have hprob : ENNReal.ofReal (finiteArmProbability θ N k) =
      ρ (finiteBoolEvent (box N) (fun ω => ω ∈ finiteArmEvent N k)) :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [hprob]
  calc
    _ ≤ ρ (⋃ m : {m : ℕ // k ≤ m}, ⋃ t : SquareLocalizationIndex m.val, E m t) :=
      measure_mono hcover
    _ ≤ ∑' m : {m : ℕ // k ≤ m}, ρ (⋃ t : SquareLocalizationIndex m.val, E m t) :=
      measure_iUnion_le _
    _ ≤ ∑' m : {m : ℕ // k ≤ m}, ∑' t : SquareLocalizationIndex m.val, ρ (E m t) := by
      apply ENNReal.tsum_le_tsum
      intro m
      exact measure_iUnion_le _
    _ ≤ ∑' m : {m : ℕ // k ≤ m}, ∑' _t : SquareLocalizationIndex m.val,
        ENNReal.ofReal (maxSquarePairProbability θ m.val) := by
      apply ENNReal.tsum_le_tsum
      intro m
      apply ENNReal.tsum_le_tsum
      intro t
      exact finite_localizedPair_measure_le θ (box N) t
    _ ≤ ∑' m : {m : ℕ // k ≤ m},
        ENNReal.ofReal (72 * (m.val : ℝ)^4 * maxSquarePairProbability θ m.val) := by
      apply ENNReal.tsum_le_tsum
      intro m
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard := card_squareLocalizationIndex_le m.val (le_trans hk m.property)
      have hbound := mul_le_mul_of_nonneg_right hcard (maxSquarePairProbability_nonneg θ m.val)
      have h := ENNReal.ofReal_le_ofReal hbound
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at h
      exact h

end
end PottsContinuity.RSW
