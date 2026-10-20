module

public import PottsContinuity.Thm3.RSW.StripBandArm
public import PottsContinuity.Thm3.RSW.AdjacentSegmentCover
public import PottsContinuity.Thm3.RSW.FiniteUnionSeed

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

/-- An actual vertical rectangle crossing, confined to its original vertices. -/
def stripVerticalCrossing (n : ℕ) (l r H : ℤ) : Set (StripConfiguration n) :=
  stripConfinedConnection n (stripRectangleVertices n l r 0 H)
    {u | u.val.2 = 0} {v | v.val.2 = H}

/-- A vertical crossing contains a height-confined arm from one of the
closed adjacent bottom segments covering its lower endpoint. -/
theorem stripVerticalCrossing_subset_segment_bandArms
    (n : ℕ) (l r H A : ℤ) (N s : ℕ) (hN : 0 < N) (hs : 0 < s)
    (hAl : A ≤ l) (hr : r ≤ A+(N:ℤ)*s) :
    stripVerticalCrossing n l r H ⊆ ⋃ j : Fin N,
      stripBandArm n H (A+(j.val:ℤ)*s) (A+((j.val:ℤ)+1)*s) := by
  rintro ω ⟨u,v,p,hu,hv,hp⟩
  have hubox := hp u p.start_mem_support
  simp only [stripRectangleVertices,Finset.mem_preimage,
    latticeRectangle,Finset.mem_product,Finset.mem_Icc] at hubox
  obtain ⟨j,hj0,hj1⟩ := int_interval_covered_by_adjacent_segments N s A u.val.1
    hN hs (hAl.trans hubox.1.1) (hubox.1.2.trans hr)
  apply Set.mem_iUnion.mpr
  refine ⟨j,u,v,p,hj0,hj1,hu,hv,?_⟩
  intro z hz
  have h := hp z hz
  simp only [stripRectangleVertices,Finset.mem_preimage,
    latticeRectangle,Finset.mem_product,Finset.mem_Icc] at h
  exact h.2

/-- The exact vertical-crossing union bound gives a band-confined segment
seed. It does not use or assume translation invariance of the measure. -/
theorem strip_vertical_crossing_has_band_seed (n : ℕ) (l r H A : ℤ)
    (N s : ℕ) (hN : 0 < N) (hs : 0 < s) (hAl : A ≤ l) (hr : r ≤ A+(N:ℤ)*s)
    (μ : Measure (StripConfiguration n)) [IsFiniteMeasure μ]
    (c : ℝ) (hc : c ≤ μ.real (stripVerticalCrossing n l r H)) :
    ∃ j : Fin N, c/(N:ℝ) ≤
      μ.real (stripBandArm n H (A+(j.val:ℤ)*s) (A+((j.val:ℤ)+1)*s)) :=
  finite_union_seed_lower μ N hN _ _
    (stripVerticalCrossing_subset_segment_bandArms n l r H A N s hN hs hAl hr) c hc

end PottsContinuity.RSW
