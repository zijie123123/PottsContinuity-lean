module

public import PottsContinuity.Thm3.Push.RectangleGeometry

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.RCInfinite
noncomputable section

/-- A rectangle with a wider horizontal span and a higher wired top encloses
the smaller domain while preserving its free bottom. -/
theorem topWiredRectangle_enclosing_subset (k ℓ K L : ℝ) (n N : ℕ)
    (hw : ⌊k*n⌋ ≤ ⌊K*N⌋) (hh : ⌊ℓ*n⌋ ≤ ⌊L*N⌋) :
    topWiredRectangle k ℓ n ⊆ topWiredRectangle K L N := by
  intro z hz
  rw [mem_topWiredRectangle_iff] at hz ⊢
  exact ⟨by omega, hz.2.1.trans hw, hz.2.2.1, hz.2.2.2.trans hh⟩

/-- No new incident edge reaches a vertex off the smaller rectangle's three
wired sides, even when both the width and the scale change. -/
theorem topWiredEnclosing_neighbor_closed (k ℓ K L : ℝ) (n N : ℕ)
    (hw : ⌊k*n⌋ ≤ ⌊K*N⌋) (hh : ⌊ℓ*n⌋ ≤ ⌊L*N⌋)
    {x : (topWiredRectangle k ℓ n : Set (ℤ × ℤ))}
    (hx : x ∉ (topWiredRectangleBoundary k ℓ n).boundary)
    {y : (topWiredRectangle K L N : Set (ℤ × ℤ))}
    (hxy : (squareLattice.induce (topWiredRectangle K L N : Set (ℤ × ℤ))).Adj
      (finiteLatticeVertexEmbedding (topWiredRectangle_enclosing_subset k ℓ K L n N hw hh) x) y) :
    ∃ z : (topWiredRectangle k ℓ n : Set (ℤ × ℤ)),
      finiteLatticeVertexEmbedding (topWiredRectangle_enclosing_subset k ℓ K L n N hw hh) z = y ∧
      (squareLattice.induce (topWiredRectangle k ℓ n : Set (ℤ × ℤ))).Adj x z := by
  have hm := (mem_topWiredRectangle_iff k ℓ n x.val).mp x.property
  have hy := (mem_topWiredRectangle_iff K L N y.val).mp y.property
  change ¬ (x.val.1 = -⌊k*n⌋ ∨ x.val.1 = ⌊k*n⌋ ∨ x.val.2 = ⌊ℓ*n⌋) at hx
  have hd : |x.val.1-y.val.1|+|x.val.2-y.val.2|=1 := hxy
  have hym : y.val ∈ topWiredRectangle k ℓ n := by
    rw [mem_topWiredRectangle_iff]
    simp only [abs_eq_max_neg] at hd
    omega
  exact ⟨⟨y.val, hym⟩, rfl, hxy⟩

theorem topWiredEnclosing_boundary_avoid (k ℓ K L : ℝ) (n N : ℕ)
    (hw : ⌊k*n⌋ ≤ ⌊K*N⌋) (hh : ⌊ℓ*n⌋ ≤ ⌊L*N⌋)
    {x : (topWiredRectangle k ℓ n : Set (ℤ × ℤ))}
    (hx : x ∉ (topWiredRectangleBoundary k ℓ n).boundary) :
    finiteLatticeVertexEmbedding (topWiredRectangle_enclosing_subset k ℓ K L n N hw hh) x ∉
      (topWiredRectangleBoundary K L N).boundary := by
  have hm := (mem_topWiredRectangle_iff k ℓ n x.val).mp x.property
  change ¬ (x.val.1 = -⌊k*n⌋ ∨ x.val.1 = ⌊k*n⌋ ∨ x.val.2 = ⌊ℓ*n⌋) at hx
  change ¬ (x.val.1 = -⌊K*N⌋ ∨ x.val.1 = ⌊K*N⌋ ∨ x.val.2 = ⌊L*N⌋)
  omega

end
end PottsContinuity.Push
