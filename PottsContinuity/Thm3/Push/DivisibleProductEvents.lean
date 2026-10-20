module

public import PottsContinuity.Thm3.Push.UpperBandCarrier
public import PottsContinuity.Thm3.Push.DivisibleReferenceGeometry
public import PottsContinuity.Thm3.Push.FiniteIntermediateRectangleEvent

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.RCInfinite
noncomputable section

/-- The geometric product's shorter-target outer event is EXACTLY the
bottom crossing event of `RSW.topWiredRectangle` at the next real aspect ratio. -/
theorem divisible_reference_bottom_event_eq (k ℓ : ℝ) (s : ℕ) (hk : 0 ≤ k) (hℓ : 4/3 ≤ ℓ) :
    {A | DualityExt.rectangleConfigurationRestriction
      (rectangle_height_subset (-⌊k*(3*s : ℕ)⌋,0)
        (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (3*s) (4*s) (by omega))
      (embeddedConfigurationRestriction _ _
        (finiteLatticeVertexEmbedding (divisible_reference_subset_next k ℓ s hk hℓ))
        (finiteLatticeGraph_map_le (divisible_reference_subset_next k ℓ s hk hℓ)) A) ∈
      rectangleHorizontalCrossingEvent (-⌊k*(3*s : ℕ)⌋,0)
        (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (3*s)} =
    RSW.finiteBoolEvent (RSW.topWiredRectangle k (ℓ+1/3) (3*s))
      (horizontalCrossing (RSW.topWiredRectangle k (ℓ+1/3) (3*s))
        (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ 0 (3*s : ℕ)) := by
  have heq := nested_rectangle_event_eq_finiteBoolEvent (-⌊k*(3*s : ℕ)⌋,0)
    (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (4*s) (3*s) (by omega)
    (RSW.topWiredRectangle k (ℓ+1/3) (3*s)) (divisible_reference_subset_next k ℓ s hk hℓ)
  have hright := topWired_canonical_right_coordinate k (3*s) hk
  simpa only [Prod.fst,Prod.snd,zero_add,hright] using heq

/-- The geometric product's upper-band event is the unchanged actual outer
crossing of `RSW.topWiredRectangle` in [s,4*s], read on its original Boolean carrier. -/
theorem divisible_reference_upper_event_eq (k ℓ : ℝ) (s : ℕ) (hk : 0 ≤ k) (hℓ : 4/3 ≤ ℓ) :
    {A | DualityExt.rectangleConfigurationRestriction
      (rectangle_upper_band_subset (-⌊k*(3*s : ℕ)⌋,0)
        (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (4*s) s (by omega))
      (embeddedConfigurationRestriction _ _
        (finiteLatticeVertexEmbedding (divisible_reference_subset_next k ℓ s hk hℓ))
        (finiteLatticeGraph_map_le (divisible_reference_subset_next k ℓ s hk hℓ)) A) ∈
      rectangleHorizontalCrossingEvent ((-⌊k*(3*s : ℕ)⌋,0).1,(-⌊k*(3*s : ℕ)⌋,0).2+(s : ℤ))
        (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (4*s-s)} =
    RSW.finiteBoolEvent (RSW.topWiredRectangle k (ℓ+1/3) (3*s))
      (horizontalCrossing (RSW.topWiredRectangle k (ℓ+1/3) (3*s))
        (-⌊k*(3*s : ℕ)⌋) ⌊k*(3*s : ℕ)⌋ s (4*s : ℕ)) := by
  have heq := intermediate_rectangle_event_eq_finiteBoolEvent
    (rectangle_upper_band_subset (-⌊k*(3*s : ℕ)⌋,0)
      (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (4*s) s (by omega))
    (RSW.topWiredRectangle k (ℓ+1/3) (3*s)) (divisible_reference_subset_next k ℓ s hk hℓ)
  have hright := topWired_canonical_right_coordinate k (3*s) hk
  have htop : (s : ℤ)+((4*s-s : ℕ) : ℤ)=((4*s : ℕ) : ℤ) := by omega
  simpa only [Prod.fst,Prod.snd,zero_add,hright,htop] using heq

end
end PottsContinuity.Push
