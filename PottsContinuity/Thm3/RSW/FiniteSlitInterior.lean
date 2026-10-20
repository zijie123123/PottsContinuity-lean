module

public import PottsContinuity.PlanarMixed.FiniteSlit.Corners

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK BD12 PlanarMixed.FiniteSlit
noncomputable section

/-- Literal inclusion of the source square into a strictly larger finite slit
rectangle. The padding 2n+2 keeps both outer wired sides off the source square. -/
def sourceSquareSlitEmbedding (n : ℕ) (x : ℤ) (hx0 : 0 ≤ x) (hxn : x ≤ (2*n:ℕ)) :
    RectangleVertex (0,0) (2*n) (2*n) ↪ Vertex (2*n+2) x where
  toFun v := ⟨v.val,sourceSquare_subset_box n x hx0 hxn v.property⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    change u.val = v.val
    have hval := congrArg (fun w : Vertex (2*n+2) x => w.val) h
    exact hval

/-- Inside the source square, beta consists precisely of the marked ray;
the right and top outer wiring are strictly beyond the source vertices. -/
theorem sourceSquareSlitEmbedding_mem_beta_iff
    (n : ℕ) (x y : ℤ) (hx0 : 0 ≤ x) (hxn : x ≤ (2*n:ℕ))
    (v : RectangleVertex (0,0) (2*n) (2*n)) :
    sourceSquareSlitEmbedding n x hx0 hxn v ∈ beta (2*n+2) x y ↔
      v.val.1 = x ∧ y ≤ v.val.2 := by
  have hb := sourceSquare_strictly_inside n x hx0 hxn v.val v.property
  change (v.val.1 = x+((2*n+2:ℕ):ℤ)-1 ∨
    (v.val.2 = ((2*n+2:ℕ):ℤ) ∧ x ≤ v.val.1) ∨
    (v.val.1 = x ∧ y ≤ v.val.2)) ↔ _
  constructor
  · rintro (h | h | h)
    · omega
    · omega
    · exact h
  · exact fun h => Or.inr (Or.inr h)

/-- Every source nearest-neighbor edge with neither endpoint on the marked
ray is retained in the finite slit graph at the original coordinates. -/
theorem sourceSquareSlitEmbedding_adj_of_avoid_ray
    (n : ℕ) (x y : ℤ) (hx0 : 0 ≤ x) (hxn : x ≤ (2*n:ℕ))
    {u v : RectangleVertex (0,0) (2*n) (2*n)}
    (huv : (rectangleGraph (0,0) (2*n) (2*n)).Adj u v)
    (hu : ¬ (u.val.1 = x ∧ y ≤ u.val.2))
    (hv : ¬ (v.val.1 = x ∧ y ≤ v.val.2)) :
    (graph (2*n+2) x y).Adj
      (sourceSquareSlitEmbedding n x hx0 hxn u)
      (sourceSquareSlitEmbedding n x hx0 hxn v) := by
  refine ⟨huv,?_⟩
  change ¬ (y < u.val.2 ∧ y < v.val.2 ∧
    ((u.val.1 = x-1 ∧ v.val.1 = x) ∨ (v.val.1 = x-1 ∧ u.val.1 = x)))
  rintro ⟨huY,hvY,h | h⟩
  · exact hv ⟨h.2,hvY.le⟩
  · exact hu ⟨h.2,huY.le⟩

end
end PottsContinuity.RSW
