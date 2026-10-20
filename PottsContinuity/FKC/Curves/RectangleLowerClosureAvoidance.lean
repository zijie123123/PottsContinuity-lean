-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/RectangleLowerClosureAvoidance.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleOpenExtension
public import PottsContinuity.FKC.Curves.DualWalkAvoidance
public import PottsContinuity.FKC.Curves.LatticeWalkInterpolation
public import Mathlib.Topology.Path

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial PottsContinuity.FKC.Curves Set

noncomputable section

/-- Unit mesh used for the literal geometric lower closure. -/
def rectangleLowerClosureMesh : PositiveMesh := ⟨1, by norm_num⟩

private theorem rectangleDualVertex_y_lower (n : ℕ) (v : RectangleDualVertex (-((n : ℤ)), 0) (2*n) n) :
    -1 ≤ v.1.2 := by
  have hv := v.2
  change v.1 ∈ latticeRectangle (-((n : ℤ)) - 1, -1) (2*n+1) (n+1) at hv
  rw [mem_latticeRectangle] at hv
  omega

private theorem segment_im_ge (a b : ℂ) (hA : (-1 / 2 : ℝ) ≤ a.im)
    (hB : (-1 / 2 : ℝ) ≤ b.im) {z : ℂ} (hz : z ∈ segment ℝ a b) :
    (-1 / 2 : ℝ) ≤ z.im := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hleft := mul_nonneg (sub_nonneg.mpr ht1) (by linarith : 0 ≤ a.im + 1/2)
  have hright := mul_nonneg ht0 (by linarith : 0 ≤ b.im + 1/2)
  have hsum : 0 ≤ (1-t)*(a.im+1/2) + t*(b.im+1/2) := add_nonneg hleft hright
  have hA' : (↑(1-t) * a).im = (1-t) * a.im := by simp
  have hB' : (↑t * b).im = t * b.im := by simp
  change (-1/2 : ℝ) ≤ ((1-t) • a + t • b).im
  simp only [Complex.add_im, Complex.real_smul]
  rw [hA', hB']
  have hlin : ((1-t)*a.im + t*b.im) + 1/2 =
      (1-t)*(a.im+1/2) + t*(b.im+1/2) := by ring
  have hshift : 0 ≤ ((1-t)*a.im + t*b.im) + 1/2 := by rw [hlin]; exact hsum
  linarith

def lowerGraphConfig (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n)) :
    Configuration (rectangleGraph (-((n : ℤ)), 0) (2*n) n) := A

/-- Extend the finite primal rectangle configuration by making all outside
original bonds open. -/
def rectangleLowerClosureExtension (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n)) :=
  rectangleOpenOutsideExtension (-((n : ℤ)), 0) (2*n) n (lowerGraphConfig n A)

def lowerDualHom (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n)) :=
  rectangleOpenOutsideDualGraphHom (-((n : ℤ)), 0) (2*n) n (lowerGraphConfig n A)

/-- Actual face-center interpolation of a complementary dual walk in the
finite rectangle, mapped into its literal whole-plane extension. -/
def rectangleLowerClosureDualPath (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n))
    {u v : RectangleDualVertex (-((n : ℤ)), 0) (2*n) n}
    (q : (openGraph (rectangleDualGraph (-((n : ℤ)), 0) (2*n) n) (rectangleDualConfiguration (-((n : ℤ)), 0) (2*n) n A)).Walk u v) :=
  closedDualWalkPath rectangleLowerClosureMesh (rectangleLowerClosureExtension n A) (q.map (lowerDualHom n A))

/-- Every point on the actual face-center interpolation of a finite
complementary-dual walk has imaginary coordinate at least `-1/2`. -/
theorem rectangleLowerClosureDualPath_range_im_ge (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n))
    {u v : RectangleDualVertex (-((n : ℤ)), 0) (2*n) n}
    (q : (openGraph (rectangleDualGraph (-((n : ℤ)), 0) (2*n) n) (rectangleDualConfiguration (-((n : ℤ)), 0) (2*n) n A)).Walk u v) {z : ℂ}
    (hz : z ∈ Set.range (rectangleLowerClosureDualPath n A q)) :
    (-1 / 2 : ℝ) ≤ z.im := by
  induction q generalizing z with
  | @nil a =>
      have hy := rectangleDualVertex_y_lower n a
      have hcenter : (-1/2 : ℝ) ≤ (dualFaceCenter rectangleLowerClosureMesh a.1).im := by
        simp [dualFaceCenter, rectangleLowerClosureMesh, latticeEmbed]
        have hyR : (-1 : ℝ) ≤ (a.1.2 : ℝ) := by exact_mod_cast hy
        linarith
      rcases hz with ⟨t, ht, rfl⟩
      change (-1/2 : ℝ) ≤ (Path.refl (dualFaceCenter rectangleLowerClosureMesh
        ((rectangleOpenOutsideDualGraphHom (-((n : ℤ)), 0) (2*n) n
          (lowerGraphConfig n A)) a)) t).im
      rw [Path.refl_apply]
      have hm : rectangleOpenOutsideDualGraphHom (-((n : ℤ)), 0) (2*n) n
          (lowerGraphConfig n A) a = a.1 := rfl
      rw [hm]
      exact hcenter
  | @cons a b c hadj q ih =>
      change z ∈ Set.range ((Path.segment
        (dualFaceCenter rectangleLowerClosureMesh a.val)
        (dualFaceCenter rectangleLowerClosureMesh b.val)).trans
        (closedDualWalkPath rectangleLowerClosureMesh (rectangleLowerClosureExtension n A)
          (q.map (lowerDualHom n A)))) at hz
      rw [Path.trans_range] at hz
      rcases hz with hz | hz
      · have hA : (-1/2 : ℝ) ≤ (dualFaceCenter rectangleLowerClosureMesh a.val).im := by
          have hy := rectangleDualVertex_y_lower n a
          simp [dualFaceCenter, rectangleLowerClosureMesh, latticeEmbed]
          have hyR : (-1 : ℝ) ≤ (a.val.2 : ℝ) := by exact_mod_cast hy
          linarith
        have hB : (-1/2 : ℝ) ≤ (dualFaceCenter rectangleLowerClosureMesh b.val).im := by
          have hy := rectangleDualVertex_y_lower n b
          simp [dualFaceCenter, rectangleLowerClosureMesh, latticeEmbed]
          have hyR : (-1 : ℝ) ≤ (b.val.2 : ℝ) := by exact_mod_cast hy
          linarith
        exact segment_im_ge _ _ hA hB (by simpa only [Path.range_segment] using hz)
      · simpa [rectangleLowerClosureDualPath, lowerDualHom, rectangleLowerClosureExtension] using ih hz

private theorem hline_im_eq_minus_one (lo hi : ℤ) {z : ℂ}
    (hz : z ∈ segment ℝ (latticeEmbed rectangleLowerClosureMesh (lo, -1))
      (latticeEmbed rectangleLowerClosureMesh (hi, -1))) : z.im = -1 := by
  rw [segment_eq_image] at hz
  rcases hz with ⟨t, ht, rfl⟩
  simp [latticeEmbed, rectangleLowerClosureMesh]
  ring

/-- The interpolated complementary-dual walk of the open-outside rectangle
configuration stays above the geometric bottom side of the rectangle. -/
theorem rectangleLowerClosureDualPath_disjoint_bottomSegment (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n))
    {u v : RectangleDualVertex (-((n : ℤ)), 0) (2*n) n}
    (q : (openGraph (rectangleDualGraph (-((n : ℤ)), 0) (2*n) n) (rectangleDualConfiguration (-((n : ℤ)), 0) (2*n) n A)).Walk u v) (lo hi : ℤ) :
    Disjoint (Set.range (rectangleLowerClosureDualPath n A q))
      (segment ℝ (latticeEmbed rectangleLowerClosureMesh (lo, -1))
        (latticeEmbed rectangleLowerClosureMesh (hi, -1))) := by
  rw [Set.disjoint_left]
  intro z hzPath hzSeg
  have hlow := rectangleLowerClosureDualPath_range_im_ge n A q hzPath
  have heq := hline_im_eq_minus_one lo hi hzSeg
  linarith

private theorem rectangleOpenEdgeImage_ne_lowerVertical (n : ℕ) (m : ℤ)
    (e : rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n) :
    rectanglePrimalEdgeToSquareEdge (-((n : ℤ)), 0) (2*n) n e ≠
      latticeBondEdge (⟨(m, -1), .vertical⟩ : LatticeBond) := by
  intro he
  let p := e.1.out
  have hrepr : s(p.1, p.2) = e.1 := Quot.out_eq _
  have heval := congrArg Subtype.val he
  have hmap : Sym2.map (fun z : RectangleVertex (-((n : ℤ)), 0) (2*n) n => z.val) e.1 =
      s((m, -1), (m, 0)) := by
    calc
      _ = (rectanglePrimalEdgeToSquareEdge (-((n : ℤ)), 0) (2*n) n e).val := by
        rfl
      _ = (latticeBondEdge (⟨(m, -1), .vertical⟩ : LatticeBond)).val := heval
      _ = s((m, -1), (m, 0)) := by rfl
  have hreprMap : Sym2.map (fun z : RectangleVertex (-((n : ℤ)), 0) (2*n) n => z.val)
      (s(p.1, p.2)) = Sym2.map (fun z : RectangleVertex (-((n : ℤ)), 0) (2*n) n => z.val) e.1 :=
    congrArg (Sym2.map (fun z : RectangleVertex (-((n : ℤ)), 0) (2*n) n => z.val)) hrepr
  have hpairs : s(p.1.1, p.2.1) = s((m, -1), (m, 0)) := by
    calc
      _ = Sym2.map (fun z : RectangleVertex (-((n : ℤ)), 0) (2*n) n => z.val)
          (s(p.1, p.2)) := by simp
      _ = Sym2.map (fun z : RectangleVertex (-((n : ℤ)), 0) (2*n) n => z.val) e.1 := hreprMap
      _ = _ := hmap
  have h1 : p.1.1.2 ≥ 0 := by
    have hp := p.1.2
    rw [mem_latticeRectangle] at hp
    omega
  have h2 : p.2.1.2 ≥ 0 := by
    have hp := p.2.2
    rw [mem_latticeRectangle] at hp
    omega
  rcases Sym2.eq_iff.mp hpairs with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have hneg : p.1.1.2 = -1 := congrArg Prod.snd hleft
    omega
  · have hneg : p.2.1.2 = -1 := congrArg Prod.snd hright
    omega

/-- A vertical unit bond immediately below the finite rectangle is open in the
literal open-outside extension, whatever the finite configuration. -/
theorem rectangleLowerClosureExtension_lowerVertical_open (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n)) (m : ℤ) :
    latticeConfigurationBondState (rectangleLowerClosureExtension n A)
      (⟨(m, -1), .vertical⟩ : LatticeBond) = true := by
  apply rectangleOpenOutsideExtension_outside_open
  intro e he
  exact rectangleOpenEdgeImage_ne_lowerVertical n m e he

/-- The mapped complementary-dual walk avoids every vertical unit segment on
its lower boundary row; each such original primal bond is outside and hence
open in the same extension. -/
theorem rectangleLowerClosureDualPath_disjoint_lowerVertical (n : ℕ)
    (A : Finset (rectanglePrimalEdgeCarrier (-((n : ℤ)), 0) (2*n) n))
    {u v : RectangleDualVertex (-((n : ℤ)), 0) (2*n) n}
    (q : (openGraph (rectangleDualGraph (-((n : ℤ)), 0) (2*n) n)
      (rectangleDualConfiguration (-((n : ℤ)), 0) (2*n) n A)).Walk u v) (m : ℤ) :
    Disjoint (Set.range (rectangleLowerClosureDualPath n A q))
      (segment ℝ (latticeEmbed rectangleLowerClosureMesh (m, -1))
        (latticeEmbed rectangleLowerClosureMesh (m, 0))) := by
  let b : LatticeBond := ⟨(m, -1), .vertical⟩
  have hb : latticeConfigurationBondState (rectangleLowerClosureExtension n A) b = true := by
    exact rectangleLowerClosureExtension_lowerVertical_open n A m
  have hd := closedDualWalkPath_range_disjoint_openPrimal_any rectangleLowerClosureMesh
    (rectangleLowerClosureExtension n A) (q.map (lowerDualHom n A)) b hb
  simpa [rectangleLowerClosureDualPath, b, primalBondSegment,
    LatticeBond.source, LatticeBond.target] using hd

end
end PottsContinuity.FKC.FiniteFK
