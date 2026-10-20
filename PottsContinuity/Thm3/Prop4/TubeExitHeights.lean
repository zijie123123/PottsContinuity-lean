module

public import PottsContinuity.Thm3.Prop4.UniformConfinedTube
public import PottsContinuity.PlanarTopology.SubpathExtraction

/-!
# Signed heights of actual tube exit arcs

At slopes of absolute value at most one, an original bond changes the
supporting-line deviation by at most one. First exit arcs therefore reach
within one of the tube radius on the correct side, while staying inside.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- An exit vertex in the original box has affine deviation at least the
radius in absolute value; leaving through an artificial exterior is excluded. -/
theorem radiusTube_exit_abs_deviation_ge {n : ℕ} (hn : 1 ≤ n)
    (R : ℝ) (u v : LatticeVertex) (ha : u.1 = -(n : ℤ)) (hb : v.1 = (n : ℤ))
    (t b : ℝ) (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    {z : LatticeVertex} (hz : z ∈ box n) (hout : z ∉ radiusTube n R u v) :
    R ≤ |(z.2 : ℝ)-(t*z.1+b)| := by
  have hdist : R ≤ tubeDistance u v z := by
    by_contra h
    exact hout ((mem_radiusTube n R u v z).mpr ⟨hz,lt_of_not_ge h⟩)
  have hzX := hz
  simp only [box,Finset.mem_product,Finset.mem_Icc] at hzX
  exact hdist.trans (tubeDistance_le_supporting_vertical hn u v ha hb t b hu hv z.1 z.2 hzX.1)

end
end PottsContinuity.Thm3.Prop4
