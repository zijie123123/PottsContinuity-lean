module

public import PottsContinuity.PlanarTopology.DualWalkCurves
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial
noncomputable section

/-- The usual lattice mesh of size one. -/
def unitLatticeMesh : PositiveMesh := ⟨1, by norm_num⟩

/-- Coordinate projection onto the closed, unit-mesh lattice rectangle. -/
def rectangleClamp (a : LatticeVertex) (w h : ℕ) (z : ℂ) : ℂ :=
  ⟨max (a.1 : ℝ) (min ((a.1 : ℝ) + w) z.re),
   max (a.2 : ℝ) (min ((a.2 : ℝ) + h) z.im)⟩

theorem continuous_rectangleClamp (a : LatticeVertex) (w h : ℕ) :
    Continuous (rectangleClamp a w h) := by
  exact Complex.equivRealProdCLM.symm.continuous.comp
    ((continuous_const.max (continuous_const.min Complex.continuous_re)).prodMk
      (continuous_const.max (continuous_const.min Complex.continuous_im)))

theorem rectangleClamp_mem (a : LatticeVertex) (w h : ℕ) (z : ℂ) :
    (a.1 : ℝ) ≤ (rectangleClamp a w h z).re ∧
    (rectangleClamp a w h z).re ≤ (a.1 : ℝ) + w ∧
    (a.2 : ℝ) ≤ (rectangleClamp a w h z).im ∧
    (rectangleClamp a w h z).im ≤ (a.2 : ℝ) + h := by
  dsimp [rectangleClamp]
  exact ⟨le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) w]) (min_le_left _ _),
    le_max_left _ _, max_le (by linarith [Nat.cast_nonneg (α := ℝ) h]) (min_le_left _ _)⟩

private theorem clamp_between {l r c d x : ℝ} (hcx : c ≤ x) (hxd : x ≤ d)
    (hcr : c ≤ r) (hld : l ≤ d) :
    c ≤ max l (min r x) ∧ max l (min r x) ≤ d :=
  ⟨(le_min hcr hcx).trans (le_max_right _ _),
    max_le hld ((min_le_right _ _).trans hxd)⟩

private theorem horizontal_unit_segment (x y : ℝ) (z : ℂ) :
    z ∈ segment ℝ (⟨x,y⟩ : ℂ) (⟨x+1,y⟩ : ℂ) ↔
      x ≤ z.re ∧ z.re ≤ x+1 ∧ z.im = y := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t,⟨ht0,ht1⟩,rfl⟩
    simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
      smul_eq_mul]
    constructor
    · nlinarith
    constructor <;> nlinarith
  · rintro ⟨h0,h1,hy⟩
    refine ⟨z.re-x,⟨by linarith,by linarith⟩,?_⟩
    apply Complex.ext <;>
      simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
        smul_eq_mul] <;> nlinarith

private theorem vertical_unit_segment (x y : ℝ) (z : ℂ) :
    z ∈ segment ℝ (⟨x,y⟩ : ℂ) (⟨x,y+1⟩ : ℂ) ↔
      z.re = x ∧ y ≤ z.im ∧ z.im ≤ y+1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨t,⟨ht0,ht1⟩,rfl⟩
    simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
      smul_eq_mul]
    constructor
    · ring
    constructor <;> nlinarith
  · rintro ⟨hx,h0,h1⟩
    refine ⟨z.im-y,⟨by linarith,by linarith⟩,?_⟩
    apply Complex.ext <;>
      simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,
        smul_eq_mul] <;> nlinarith

private theorem unit_center_eq (x y : ℤ) :
    dualFaceCenter unitLatticeMesh (x,y) = (⟨(x : ℝ)+1/2,(y : ℝ)+1/2⟩ : ℂ) := by
  apply Complex.ext <;> norm_num [dualFaceCenter,latticeEmbed,unitLatticeMesh]

/-- Clamping a genuine crossing dual segment retains its OWN segment. Thus
projection introduces no new primal contacts on the rectangle boundary. -/
theorem rectangleClamp_crossingDualBond_mem (a : LatticeVertex) (w h : ℕ)
    (b : LatticeBond) (hs : b.source ∈ latticeRectangle a w h)
    (ht : b.target ∈ latticeRectangle a w h) {z : ℂ}
    (hz : z ∈ dualBondSegment unitLatticeMesh (dualBondOfPrimal b)) :
    rectangleClamp a w h z ∈ dualBondSegment unitLatticeMesh (dualBondOfPrimal b) := by
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax
  · have hS := (mem_latticeRectangle a (x,y) w h).mp hs
    have hT := (mem_latticeRectangle a (x+1,y) w h).mp ht
    have hS' : (a.1 : ℝ) ≤ x ∧ (x : ℝ) ≤ (a.1 : ℝ)+w ∧
        (a.2 : ℝ) ≤ y ∧ (y : ℝ) ≤ (a.2 : ℝ)+h := by
      simpa only [Prod.fst,Prod.snd,and_assoc] using (show
        ((a.1 : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (a.1 : ℝ)+w) ∧
        (a.2 : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ (a.2 : ℝ)+h from by exact_mod_cast hS)
    have hT' : (a.1 : ℝ) ≤ (x : ℝ)+1 ∧ (x : ℝ)+1 ≤ (a.1 : ℝ)+w ∧
        (a.2 : ℝ) ≤ y ∧ (y : ℝ) ≤ (a.2 : ℝ)+h := by
      have hh := hT
      simp only [and_assoc] at hh
      exact_mod_cast hh
    simp only [dualBondOfPrimal,dualBondSegment,LatticeBond.source,LatticeBond.target,
      unit_center_eq,Int.cast_sub,Int.cast_one,Int.cast_add] at hz ⊢
    rw [show (y : ℝ)-1+1+1/2 = ((y : ℝ)-1+1/2)+1 by ring] at hz ⊢
    rw [vertical_unit_segment] at hz ⊢
    refine ⟨?_,?_⟩
    · change max (a.1 : ℝ) (min ((a.1 : ℝ)+w) z.re) = (x : ℝ)+1/2
      rw [hz.1,min_eq_right (by linarith [hT'.2.1]),max_eq_right (by linarith [hS'.1])]
    · exact clamp_between hz.2.1 hz.2.2 (by linarith [hS'.2.2.2])
        (by linarith [hS'.2.2.1])
  · have hS := (mem_latticeRectangle a (x,y) w h).mp hs
    have hT := (mem_latticeRectangle a (x,y+1) w h).mp ht
    have hS' : (a.1 : ℝ) ≤ x ∧ (x : ℝ) ≤ (a.1 : ℝ)+w ∧
        (a.2 : ℝ) ≤ y ∧ (y : ℝ) ≤ (a.2 : ℝ)+h := by
      simpa only [Prod.fst,Prod.snd,and_assoc] using (show
        ((a.1 : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ (a.1 : ℝ)+w) ∧
        (a.2 : ℝ) ≤ (y : ℝ) ∧ (y : ℝ) ≤ (a.2 : ℝ)+h from by exact_mod_cast hS)
    have hT' : (a.1 : ℝ) ≤ x ∧ (x : ℝ) ≤ (a.1 : ℝ)+w ∧
        (a.2 : ℝ) ≤ (y : ℝ)+1 ∧ (y : ℝ)+1 ≤ (a.2 : ℝ)+h := by
      have hh := hT
      simp only [and_assoc] at hh
      exact_mod_cast hh
    simp only [dualBondOfPrimal,dualBondSegment,LatticeBond.source,LatticeBond.target,
      unit_center_eq,Int.cast_sub,Int.cast_one,Int.cast_add] at hz ⊢
    rw [show (x : ℝ)-1+1+1/2 = ((x : ℝ)-1+1/2)+1 by ring] at hz ⊢
    rw [horizontal_unit_segment] at hz ⊢
    have hb := clamp_between hz.1 hz.2.1 (by linarith [hS'.2.1])
      (by linarith [hS'.1]) (l := (a.1 : ℝ)) (r := (a.1 : ℝ)+w)
    refine ⟨hb.1,hb.2,?_⟩
    change max (a.2 : ℝ) (min ((a.2 : ℝ)+h) z.im) = (y : ℝ)+1/2
    rw [hz.2.2,min_eq_right (by linarith [hT'.2.2.2]),
      max_eq_right (by linarith [hS'.2.2.1])]

/-- The preceding geometric retention statement with the actual original-edge
label carried by the rectangle dual graph. -/
theorem rectangleClamp_dualBond_mem (a : LatticeVertex) (w h : ℕ)
    (d : RectangleDualEdgeCarrier a w h) {z : ℂ}
    (hz : z ∈ dualBondSegment unitLatticeMesh d.crossingBond) :
    rectangleClamp a w h z ∈ dualBondSegment unitLatticeMesh d.crossingBond := by
  have hd : d.crossingBond = dualBondOfPrimal (rectanglePrimalEdgeBond a w h d.primalEdge) :=
    d.crossingBond_eq
  rw [hd] at hz ⊢
  exact rectangleClamp_crossingDualBond_mem a w h _
    (rectanglePrimalEdgeBond_endpoints_mem_public a w h d.primalEdge).1
    (rectanglePrimalEdgeBond_endpoints_mem_public a w h d.primalEdge).2 hz

end
end PottsContinuity.PlanarTopology
