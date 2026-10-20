module

public import PottsContinuity.Thm3.Push.UpperBandProduct
public import PottsContinuity.Thm3.Push.DivisibleProductEvents
public import PottsContinuity.Thm3.Push.BaseProbabilityCanonical
public import PottsContinuity.Thm3.Push.PushShiftUpperProbability

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.RCInfinite
open PottsContinuity.RSW
noncomputable section

/-- The product inequality of the induction step of Lemma 3, at divisible scales.
At the explicit self-dual parameter and every real q>=1, the exact crossing
probabilities `selfDualTopWiredCrossingProbability` obey the highest-frontier product
whenever n=3*s. All exploration, random-domain, original-bond and rounding inputs
are proved. -/
theorem selfDual_push_product_at_three_mul (q : Set.Ici (1 : ℝ))
    (k : ℝ) (hk : 0 < k) (ℓ : ℝ) (hℓ : 4/3 ≤ ℓ) (s : ℕ) (_hs : 1 ≤ s) :
    selfDualTopWiredCrossingProbability q k ℓ (3*s) *
      selfDualTopWiredCrossingProbability q k (4/3) (3*s) ≤
        selfDualTopWiredCrossingProbability q k (ℓ+1/3) (3*s) := by
  let a : LatticeVertex := (-⌊k*(3*s : ℕ)⌋,0)
  let w := (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat
  let T := topWiredRectangle k (ℓ+1/3) (3*s)
  let hV := divisible_reference_subset_next k ℓ s hk.le hℓ
  let f := finiteLatticeVertexEmbedding hV
  let hRG := finiteLatticeGraph_map_le hV
  have hsides : ∀ u v : RectangleVertex a w (4*s),
      (u.val.1=a.1 ∨ u.val.1=a.1+(w : ℤ)) →
      (v.val.1=a.1 ∨ v.val.1=a.1+(w : ℤ)) →
      (topWiredRectangleBoundary k (ℓ+1/3) (3*s)).partition.r (f u) (f v) :=
    divisible_reference_original_sides_wired k ℓ s hk.le hℓ
  have hprod := upper_band_crossing_reference_product a w (4*s) (3*s) s (by omega) (by omega)
    (finiteLatticeGraph T) f hRG (selfDualParameters q)
    (topWiredRectangleBoundary k (ℓ+1/3) (3*s)) hsides
  dsimp only at hprod
  erw [divisible_reference_bottom_event_eq k ℓ s hk.le hℓ,
    divisible_reference_upper_event_eq k ℓ s hk.le hℓ] at hprod
  have hbase := selfDual_base_probability_eq_canonical q k s hk.le
  dsimp only at hbase
  erw [← hbase] at hprod
  have hfirst := selfDual_probability_le_shifted_upper_band q k ℓ s
  calc
    selfDualTopWiredCrossingProbability q k ℓ (3*s) *
        selfDualTopWiredCrossingProbability q k (4/3) (3*s) =
      selfDualTopWiredCrossingProbability q k (4/3) (3*s) *
        selfDualTopWiredCrossingProbability q k ℓ (3*s) := mul_comm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hfirst (selfDualTopWiredCrossingProbability_nonneg q k (4/3) (3*s))
    _ ≤ _ := hprod

end
end PottsContinuity.Push
