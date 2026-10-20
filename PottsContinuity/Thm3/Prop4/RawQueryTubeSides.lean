module

public import PottsContinuity.Thm3.Prop4.TraceHullTubeSide
public import PottsContinuity.Thm3.Prop4.RawMarkedTraceAccess

/-! # Raw queried endpoints outside the tube retain their proper source side -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
local instance rawQueryTubeSidesEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- On the lower one-sided trace event, EVERY lower raw queried endpoint
outside the tube has affine height at most minus the radius. This includes
queried bonds internal to the reached region, not just frontier bonds. -/
theorem markedLowerBoxRawReveal_outside_endpoint_height_le
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 < R)
    (u v : (box n : Set LatticeVertex)) (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (t b : ℝ) (hut : (u.val.2 : ℝ) = t*u.val.1+b) (hvt : (v.val.2 : ℝ) = t*v.val.1+b)
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v)
    (htrace : ∀ z ∈ markedLowerBoxTrace n u v A,
      z.val ∈ radiusTube n R u.val v.val ∨ (z.val.2 : ℝ)-(t*z.val.1+b) ≤ 0)
    (e : (finiteLatticeGraph (box n)).edgeSet) (he : e ∈ markedLowerBoxRawReveal n u v A)
    (x : (box n : Set LatticeVertex)) (hx : x ∈ e.val) (hout : x.val ∉ radiusTube n R u.val v.val) :
    (x.val.2 : ℝ)-(t*x.val.1+b) ≤ -R := by
  classical
  have hno := markedLowerBoxRawReveal_endpoint_no_top_access_of_connection n hn u v hu hv A hA e he x hx
  have hhull : x.val ∈ lowerTraceHull n ((markedLowerBoxTrace n u v A).image Subtype.val) :=
    Finset.mem_filter.mpr ⟨x.property,hno⟩
  have hside := lowerTraceHull_outside_tube_nonpos hn R hR u.val v.val hu hv t b hut hvt
    ((markedLowerBoxTrace n u v A).image Subtype.val) (by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
      exact htrace y hy) x.val hhull hout
  have hexit := radiusTube_exit_abs_deviation_ge hn R u.val v.val hu hv t b hut hvt x.property hout
  rw [abs_of_nonpos hside] at hexit
  linarith only [hexit]

/-- The exact upper counterpart holds for EVERY upper raw queried endpoint
outside the tube, including boundary columns and original corner vertices. -/
theorem markedUpperBoxRawReveal_outside_endpoint_height_ge
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 < R)
    (u v : (box n : Set LatticeVertex)) (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (t b : ℝ) (hut : (u.val.2 : ℝ) = t*u.val.1+b) (hvt : (v.val.2 : ℝ) = t*v.val.1+b)
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v)
    (htrace : ∀ z ∈ markedUpperBoxTrace n u v A,
      z.val ∈ radiusTube n R u.val v.val ∨ 0 ≤ (z.val.2 : ℝ)-(t*z.val.1+b))
    (e : (finiteLatticeGraph (box n)).edgeSet) (he : e ∈ markedUpperBoxRawReveal n u v A)
    (x : (box n : Set LatticeVertex)) (hx : x ∈ e.val) (hout : x.val ∉ radiusTube n R u.val v.val) :
    R ≤ (x.val.2 : ℝ)-(t*x.val.1+b) := by
  have hno := markedUpperBoxRawReveal_endpoint_no_bottom_access_of_connection n hn u v hu hv A hA e he x hx
  have hside := traceBottomInaccessible_outside_tube_nonneg hn R hR u.val v.val hu hv t b hut hvt
    ((markedUpperBoxTrace n u v A).image Subtype.val) (by
      intro z hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
      exact htrace y hy) x.val x.property hno hout
  have hexit := radiusTube_exit_abs_deviation_ge hn R u.val v.val hu hv t b hut hvt x.property hout
  rwa [abs_of_nonneg hside] at hexit

end
end PottsContinuity.Thm3.Prop4
