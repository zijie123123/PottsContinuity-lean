module

public import PottsContinuity.PlanarTopology.KSTUpperArmConstruction
public import PottsContinuity.PlanarTopology.KSTLowerArmConstruction
public import PottsContinuity.PlanarTopology.KSTQuasiFromWalls
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- KST's six-event quasi-crossing construction at every positive multiple
of 192. The four arm targets, both short crossing rectangles and every actual
open attachment are checked literally, without fractional-side conventions. -/
theorem kst_quasi_construction_multiple192 (n : ℕ) (hn : 1 ≤ n) :
    let m := 192*n
    (latticeConfigurationTranslate (-(((m/16 : ℕ) : ℤ),0))) ⁻¹' kstArm m ∩
    (latticeConfigurationTranslate (-(-((m/16 : ℕ) : ℤ),0))) ⁻¹' kstArm m ∩
    (latticeConfigurationTranslate (-(0,((3*m/2 : ℕ) : ℤ)))) ⁻¹' kstArm (5*m/2) ∩
    (latticeConfigurationTranslate (-(0,-((3*m/2 : ℕ) : ℤ)))) ⁻¹' kstArm (5*m/2) ∩
    horizontalRectangle (-5*(m : ℤ),-4*(m : ℤ)) (31*m/4) (8*m) ∩
    horizontalRectangle (-((11*m/4 : ℕ) : ℤ),-4*(m : ℤ)) (31*m/4) (8*m) ⊆
      kstQuasiCrossing (4*m) m := by
  dsimp only
  rintro ω ⟨⟨⟨⟨⟨hR,hL⟩,hT⟩,hB⟩,hHL⟩,hHR⟩
  have h16 : 192*n/16 = 12*n := by omega
  have h32 : 3*(192*n)/2 = 288*n := by omega
  have h52 : 5*(192*n)/2 = 480*n := by omega
  have h314 : 31*(192*n)/4 = 1488*n := by omega
  have h114 : 11*(192*n)/4 = 528*n := by omega
  have h8 : 8*(192*n) = 1536*n := by omega
  have h4 : 4*(192*n) = 768*n := by omega
  have hL' : ω ∈ (latticeConfigurationTranslate (-(-12*(n : ℤ),0))) ⁻¹' kstArm (192*n) := by
    simpa only [h16,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hL
  have hR' : ω ∈ (latticeConfigurationTranslate (-(12*(n : ℤ),0))) ⁻¹' kstArm (192*n) := by
    simpa only [h16,Nat.cast_mul,Nat.cast_ofNat] using hR
  have hT' : ω ∈ (latticeConfigurationTranslate (-(0,288*(n : ℤ)))) ⁻¹' kstArm (480*n) := by
    simpa only [h32,h52,Nat.cast_mul,Nat.cast_ofNat] using hT
  have hB' : ω ∈ (latticeConfigurationTranslate (-(0,-288*(n : ℤ)))) ⁻¹' kstArm (480*n) := by
    simpa only [h32,h52,Nat.cast_mul,Nat.cast_ofNat,neg_mul] using hB
  obtain ⟨a,b,s,g,B,hg,hgO,hBO,hs,hBbox⟩ := kst_three_arms_bottom_attachment n hn ω hL' hR' hB'
  obtain ⟨c,d,t,g',T,hg',hgO',hTO,ht,hTbox⟩ := kst_three_arms_top_attachment n hn ω hL' hR' hT'
  rw [h4]
  apply kst_quasi_of_vertical_walls n hn ω g g' B T hg hg' hgO hgO' hBO hTO hs ht hBbox hTbox
  · have hbase : (-5*((192*n : ℕ) : ℤ),-4*((192*n : ℕ) : ℤ)) =
        (-960*(n : ℤ),-768*(n : ℤ)) := by push_cast; apply Prod.ext <;> dsimp <;> ring
    simpa only [hbase,h314,h8] using hHL
  · have hbase : (-((11*(192*n)/4 : ℕ) : ℤ),-4*((192*n : ℕ) : ℤ)) =
        (-528*(n : ℤ),-768*(n : ℤ)) := by
      rw [h114]
      push_cast
      apply Prod.ext <;> dsimp <;> ring
    simpa only [hbase,h314,h8] using hHR

/-- The exact six-event integral-scale construction of KST §4.3, used in
`BD12.KSTConstructionExport`. The inverse-translation preimages are the image translations
`BD12.kstTranslateEvent`, expanded without introducing a second event definition. -/
theorem kst_quasi_construction (j : ℕ) :
    let m := 192*4^j
    (latticeConfigurationTranslate (-(((m/16 : ℕ) : ℤ),0))) ⁻¹' kstArm m ∩
    (latticeConfigurationTranslate (-(-((m/16 : ℕ) : ℤ),0))) ⁻¹' kstArm m ∩
    (latticeConfigurationTranslate (-(0,((3*m/2 : ℕ) : ℤ)))) ⁻¹' kstArm (5*m/2) ∩
    (latticeConfigurationTranslate (-(0,-((3*m/2 : ℕ) : ℤ)))) ⁻¹' kstArm (5*m/2) ∩
    horizontalRectangle (-5*(m : ℤ),-4*(m : ℤ)) (31*m/4) (8*m) ∩
    horizontalRectangle (-((11*m/4 : ℕ) : ℤ),-4*(m : ℤ)) (31*m/4) (8*m) ⊆
      kstQuasiCrossing (4*m) m := by
  apply kst_quasi_construction_multiple192 (4^j)
  have h : 0 < (4 : ℕ)^j := pow_pos (by norm_num) j
  omega

end
end PottsContinuity.PlanarTopology
