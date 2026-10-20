module

public import PottsContinuity.Thm3.RSW.WalkClipping
public import PottsContinuity.Thm3.RSW.StripVerticalSeed

@[expose] public section

namespace PottsContinuity.RSW

/-- Narrowing the height interval and enlarging the horizontal interval
preserves a literal vertical strip crossing by clipping its sampled walk. -/
theorem stripConfined_vertical_subset_of_intervals
    (n : ℕ) (l r b t L R H : ℤ) (hb : b ≤ 0) (hH : 0 ≤ H) (ht : H ≤ t)
    (hl : L ≤ l) (hr : r ≤ R) :
    stripConfinedConnection n (stripRectangleVertices n l r b t)
      {u | u.val.2 = b} {v | v.val.2 = t} ⊆ stripVerticalCrossing n L R H := by
  rintro ω ⟨u,v,w,hu,hv,hw⟩
  have hstep : ∀ {x y : stripVertices n}, (stripOpenGraph n ω).Adj x y →
      y.val.2 ≤ x.val.2+1 := by
    intro x y hxy
    have h := stripOpenGraph_le n ω hxy
    change |x.val.1-y.val.1|+|x.val.2-y.val.2|=1 at h
    have := abs_nonneg (x.val.1-y.val.1)
    have := neg_le_abs (x.val.2-y.val.2)
    omega
  obtain ⟨x,y,p,hx,hy,hp⟩ := walk_clip_coordinate (stripOpenGraph n ω)
    (fun z => z.val.2) hstep 0 H hH
    (fun z => L ≤ z.val.1 ∧ z.val.1 ≤ R) w (hu.trans_le hb) (ht.trans hv.ge)
    (by
      intro z hz
      have h := hw z hz
      simp only [stripRectangleVertices,Finset.mem_preimage,
        latticeRectangle,Finset.mem_product,Finset.mem_Icc] at h
      exact ⟨hl.trans h.1.1,h.1.2.trans hr⟩)
  refine ⟨x,y,p,hx,hy,?_⟩
  intro z hz
  have h := hp z hz
  simp only [stripRectangleVertices,Finset.mem_preimage,
    latticeRectangle,Finset.mem_product,Finset.mem_Icc]
  exact ⟨h.2.2,⟨h.1,h.2.1⟩⟩

/-- The source reflected crossing with its extra bottom row is contained in
the original central primal vertical crossing. -/
theorem strip_shifted_vertical_subset_central (n k : ℕ) :
    stripConfinedConnection n
      (stripRectangleVertices n (-(k:ℤ)*n) ((k:ℤ)*n-1) (-1) (2*n))
      {u | u.val.2 = -1} {v | v.val.2 = 2*n} ⊆
        stripVerticalCrossing n (-(k:ℤ)*n) ((k:ℤ)*n) (2*n) := by
  apply stripConfined_vertical_subset_of_intervals <;> omega

end PottsContinuity.RSW
