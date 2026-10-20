module

public import PottsContinuity.Thm3.Push.TopWiredCanonicalRectangle
public import PottsContinuity.PD.RCInfinite.SubgraphComparison

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.PD.RCInfinite
noncomputable section

/-- The height-4*s reference rectangle is contained in the exact next-height
top-wired domain, with every horizontal and vertical floor retained. -/
theorem divisible_reference_subset_next (k ℓ : ℝ) (s : ℕ) (hk : 0 ≤ k) (hℓ : 4/3 ≤ ℓ) :
    PD.FK.latticeRectangle (-⌊k*(3*s : ℕ)⌋,0)
      (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (4*s) ⊆
      RSW.topWiredRectangle k (ℓ+1/3) (3*s) := by
  rw [topWiredRectangle_base_three_eq_canonical k s hk]
  apply topWiredRectangle_subset
  have hheight := topWired_height_floor_mono (4/3) (ℓ+1/3) (by linarith) (3*s)
  simpa only [floor_four_thirds_mul_three] using hheight

/-- The reference's actual physical sides lie in the ORIGINAL outer wired
class, not merely in a prospective explored partition. -/
theorem divisible_reference_original_sides_wired
    (k ℓ : ℝ) (s : ℕ) (hk : 0 ≤ k) (hℓ : 4/3 ≤ ℓ)
    (u v : RectangleVertex (-⌊k*(3*s : ℕ)⌋,0)
      (⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat (4*s))
    (hu : u.val.1= -⌊k*(3*s : ℕ)⌋ ∨
      u.val.1= -⌊k*(3*s : ℕ)⌋+((⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat : ℤ))
    (hv : v.val.1= -⌊k*(3*s : ℕ)⌋ ∨
      v.val.1= -⌊k*(3*s : ℕ)⌋+((⌊k*(3*s : ℕ)⌋- -⌊k*(3*s : ℕ)⌋).toNat : ℤ)) :
    (RSW.topWiredRectangleBoundary k (ℓ+1/3) (3*s)).partition.r
      (finiteLatticeVertexEmbedding (divisible_reference_subset_next k ℓ s hk hℓ) u)
      (finiteLatticeVertexEmbedding (divisible_reference_subset_next k ℓ s hk hℓ) v) := by
  rw [topWired_canonical_right_coordinate k (3*s) hk] at hu hv
  apply Or.inr
  constructor
  · rcases hu with hu | hu
    · exact Or.inl hu
    · exact Or.inr (Or.inl hu)
  · rcases hv with hv | hv
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)

end
end PottsContinuity.Push
