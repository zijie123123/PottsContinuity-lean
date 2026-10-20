module

public import PottsContinuity.PlanarMixed.TiltedHalfHeight.NativeDualBoundaryStep
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.HullBoundaryCrosscut
public import PottsContinuity.PlanarMixed.TiltedHalfHeight.LowerHullCells

@[expose] public section

namespace PottsContinuity.PlanarMixed.TiltedHalfHeight
open Thm3.Prop4 PD.FK PD.FK.Medial PD.Duality
noncomputable section

/-- Stop the actual transported hull-boundary path when it first reaches
the wired top. All preceding edges are genuine native reduced dual edges. -/
theorem hullBoundary_walk_to_native_top (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 0) (ω : TiltedConfiguration N t)
    (C : Finset LatticeVertex) (hC : ∀ z ∈ C, tiltedHeight t z ≤ (N:ℝ)-1)
    (hsat : ∀ b : TiltedBond N t, ω (tiltedBondEdge N t b)=true →
      (b.val.source∈C ↔ b.val.target∈C))
    {u v : LatticeVertex} (p : (latticeCellBoundaryGraph (vertexCellBases C)).Walk u v)
    (hu : RSW.tiltedStripReducedDualVertex N t u ∈ tiltedStripVertices N t)
    (hv : tiltedTop N t (RSW.tiltedStripReducedDualVertex N t v)) :
    tiltedConnectedToTop N t (reducedCarrierLift N t
      (RSW.tiltedStripReducedDualTransport N t (by exact ⟨ht.1,by linarith [ht.2]⟩)
        (RSW.tiltedStripReducedRestriction N t ω)))
      (RSW.tiltedStripReducedDualVertex N t u) := by
  revert hu hv
  induction p with
  | @nil a =>
    intro hu hv
    exact ⟨hu,⟨_,hu⟩,hv,.refl _⟩
  | @cons a b c hab p ih =>
    intro hu hv
    by_cases ha : tiltedTop N t (RSW.tiltedStripReducedDualVertex N t a)
    · exact ⟨hu,⟨_,hu⟩,ha,.refl _⟩
    · obtain ⟨hb,hab'⟩ := hullBoundary_step_to_native_dual N t ht ω C hC hsat hab hu ha
      obtain ⟨_,w,hw,hpath⟩ := ih hb hv
      exact ⟨hu,w,hw,hab'.reachable.trans hpath⟩

/-- Finite deterministic contracted-pair alternative on the nonpositive slope
branch. It uses the actual original hull and the exact native reduced map
`RSW.tiltedStripReducedDualTransport`. -/
theorem halfHeight_or_native_dual_of_open_columns_nonpositive
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 0)
    (ω : TiltedConfiguration (2*n) t) (xm xp : ℤ) (hm : xm < 0) (hp : 0 < xp)
    (hfm : FullyOpenColumn (2*n) t xm ω) (hfp : FullyOpenColumn (2*n) t xp ω) :
    lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n ∨
      RSW.tiltedStripReducedDualTransport (2*n) t (by exact ⟨ht.1,by linarith [ht.2]⟩)
        (RSW.tiltedStripReducedRestriction (2*n) t ω) ∈
          reducedCarrierHalfHeight n (by omega) t := by
  classical
  by_cases hH : lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n
  · exact Or.inl hH
  right
  have htfull : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨ht.1,by linarith [ht.2]⟩
  have hfinite := lowerStripHull_points_finite n hn t htfull ω hH xm xp hm hp hfm hfp
  let C := hfinite.toFinset
  have hC : (C : Set LatticeVertex) = Subtype.val '' LowerStripHull n t ω :=
    hfinite.coe_toFinset
  have hzero := lowerHull_core_mem n t ω C hC 0 (by omega)
  have hrootn := lowerHull_core_mem n t ω C hC n le_rfl
  have hconn := lowerHull_points_connected n t ω C hC
  have hCtop := lowerHull_points_not_top n hn t htfull ω hH C hC
  have hsat := lowerHull_points_saturated n t ω C hC
  obtain ⟨yu,yl,hyu,hyl,⟨p⟩⟩ :=
    finite_connected_hull_boundary_central_crosscut C n hzero hrootn hconn
  have hyuTop : tiltedHeight t (0,yu) ≤ ((2*n : ℕ):ℝ)-1 := by
    cases p with
    | nil => omega
    | cons h _ => exact (cellBoundary_height_le_of_hull_not_top (2*n) t ht.2 C hCtop h).1
  have hstartHeight : 0 ≤ tiltedHeight t (RSW.tiltedStripReducedDualVertex (2*n) t (0,yu)) ∧
      tiltedHeight t (RSW.tiltedStripReducedDualVertex (2*n) t (0,yu)) ≤ n := by
    rw [reducedDualVertex_height_nonpositive (2*n) t ht.2]
    have hyuR : (n:ℝ) ≤ (yu:ℝ) := by exact_mod_cast hyu
    simp only [tiltedHeight,Int.cast_zero,mul_zero,sub_zero] at hyuTop ⊢
    push_cast at hyuTop
    constructor <;> push_cast <;> linarith
  have hu : RSW.tiltedStripReducedDualVertex (2*n) t (0,yu) ∈ tiltedStripVertices (2*n) t :=
    ⟨hstartHeight.1,hstartHeight.2.trans (by exact_mod_cast (show n ≤ 2*n by omega))⟩
  have hv : tiltedTop (2*n) t (RSW.tiltedStripReducedDualVertex (2*n) t (0,yl)) := by
    rw [tiltedTop_iff_height (2*n) htfull,reducedDualVertex_height_nonpositive (2*n) t ht.2]
    have hylR : (yl:ℝ) < 0 := by exact_mod_cast hyl
    simp only [tiltedHeight,Int.cast_zero,mul_zero,sub_zero]
    linarith
  have hc := hullBoundary_walk_to_native_top (2*n) t ht ω C hCtop hsat p hu hv
  have he : RSW.tiltedStripReducedDualVertex (2*n) t (0,yu) = (0,(2*n:ℤ)-1-yu) := by
    simp [RSW.tiltedStripReducedDualVertex,not_lt.mpr ht.2]
  have hf := lowestTopConnectedHeight_le_of_connected (2*n) (by omega) t
    (reducedCarrierLift (2*n) t (RSW.tiltedStripReducedDualTransport (2*n) t htfull
      (RSW.tiltedStripReducedRestriction (2*n) t ω)))
    (RSW.tiltedStripReducedDualVertex (2*n) t (0,yu)) hc
  have hx : (RSW.tiltedStripReducedDualVertex (2*n) t (0,yu)).1 = 0 := by rw [he]
  rw [hx] at hf
  exact hf.trans hstartHeight.2

end
end PottsContinuity.PlanarMixed.TiltedHalfHeight
