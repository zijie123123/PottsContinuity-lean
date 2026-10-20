module

public import PottsContinuity.Thm3.RSW.PushConditional
public import PottsContinuity.PD.RCInfinite.SubgraphComparison

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
noncomputable section

theorem mem_topWiredRectangle_iff (k ℓ : ℝ) (n : ℕ) (v : ℤ × ℤ) :
    v ∈ topWiredRectangle k ℓ n ↔
      -⌊k * n⌋ ≤ v.1 ∧ v.1 ≤ ⌊k * n⌋ ∧ 0 ≤ v.2 ∧ v.2 ≤ ⌊ℓ * n⌋ := by
  simp only [topWiredRectangle, PottsContinuity.latticeRectangle,
    Finset.mem_product, Finset.mem_Icc]
  tauto

theorem topWiredRectangle_subset (k ℓ L : ℝ) (n : ℕ)
    (h : ⌊ℓ * n⌋ ≤ ⌊L * n⌋) :
    topWiredRectangle k ℓ n ⊆ topWiredRectangle k L n := by
  intro v hv
  rw [mem_topWiredRectangle_iff] at hv ⊢
  exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.trans h⟩

/-- Literal coordinate-preserving inclusion of a shorter top-wired rectangle. -/
abbrev topWiredHeightEmbedding (k ℓ L : ℝ) (n : ℕ) (h : ⌊ℓ * n⌋ ≤ ⌊L * n⌋) :=
  PottsContinuity.PD.RCInfinite.finiteLatticeVertexEmbedding
    (topWiredRectangle_subset k ℓ L n h)

/-- A vertex outside the shorter top/side wiring has every taller-box neighbor
in the shorter graph. Its bottom neighbors are retained by the larger domain. -/
theorem topWiredHeightEmbedding_neighbor_closed (k ℓ L : ℝ) (n : ℕ)
    (h : ⌊ℓ * n⌋ ≤ ⌊L * n⌋)
    {x : (topWiredRectangle k ℓ n : Set (ℤ × ℤ))}
    (hx : x ∉ (topWiredRectangleBoundary k ℓ n).boundary)
    {y : (topWiredRectangle k L n : Set (ℤ × ℤ))}
    (hxy : (PottsContinuity.squareLattice.induce
      (topWiredRectangle k L n : Set (ℤ × ℤ))).Adj
        (topWiredHeightEmbedding k ℓ L n h x) y) :
    ∃ z : (topWiredRectangle k ℓ n : Set (ℤ × ℤ)),
      topWiredHeightEmbedding k ℓ L n h z = y ∧
      (PottsContinuity.squareLattice.induce
        (topWiredRectangle k ℓ n : Set (ℤ × ℤ))).Adj x z := by
  have hxmem := (mem_topWiredRectangle_iff k ℓ n x.val).mp x.property
  have hymem := (mem_topWiredRectangle_iff k L n y.val).mp y.property
  change ¬ (x.val.1 = -⌊k * n⌋ ∨ x.val.1 = ⌊k * n⌋ ∨ x.val.2 = ⌊ℓ * n⌋) at hx
  have hdist : |x.val.1 - y.val.1| + |x.val.2 - y.val.2| = 1 := hxy
  have hymem' : y.val ∈ topWiredRectangle k ℓ n := by
    rw [mem_topWiredRectangle_iff]
    simp only [abs_eq_max_neg] at hdist
    omega
  exact ⟨⟨y.val, hymem'⟩, rfl, hxy⟩

theorem topWiredHeightEmbedding_boundary_avoid (k ℓ L : ℝ) (n : ℕ)
    (h : ⌊ℓ * n⌋ ≤ ⌊L * n⌋)
    {x : (topWiredRectangle k ℓ n : Set (ℤ × ℤ))}
    (hx : x ∉ (topWiredRectangleBoundary k ℓ n).boundary) :
    topWiredHeightEmbedding k ℓ L n h x ∉ (topWiredRectangleBoundary k L n).boundary := by
  have hm := (mem_topWiredRectangle_iff k ℓ n x.val).mp x.property
  change ¬ (x.val.1 = -⌊k * n⌋ ∨ x.val.1 = ⌊k * n⌋ ∨ x.val.2 = ⌊ℓ * n⌋) at hx
  change ¬ (x.val.1 = -⌊k * n⌋ ∨ x.val.1 = ⌊k * n⌋ ∨ x.val.2 = ⌊L * n⌋)
  omega

/-- Real height comparison preserves every lattice floor, including n=0. -/
theorem topWired_height_floor_mono (ℓ L : ℝ) (h : ℓ ≤ L) (n : ℕ) :
    ⌊ℓ * n⌋ ≤ ⌊L * n⌋ :=
  Int.floor_mono (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n))

end
end PottsContinuity.Push
