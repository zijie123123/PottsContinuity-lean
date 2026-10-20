module

public import PottsContinuity.PlanarTopology.ClampedDualConnector
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial
noncomputable section

private theorem unit_center_coordinates (z : LatticeVertex) :
    dualFaceCenter unitLatticeMesh z = (⟨(z.1 : ℝ)+1/2,(z.2 : ℝ)+1/2⟩ : ℂ) := by
  apply Complex.ext <;> norm_num [dualFaceCenter,latticeEmbed,unitLatticeMesh]

private theorem central_clamp_coordinates (k : ℕ) (z : ℂ) :
    rectangleClamp (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k) z =
      (⟨max (-13*(k : ℝ)) (min (13*(k : ℝ)) z.re),
        max (-12*(k : ℝ)) (min (12*(k : ℝ)) z.im)⟩ : ℂ) := by
  have hx : -(13*(k : ℝ))+26*k = 13*k := by ring
  have hy : -(12*(k : ℝ))+24*k = 12*k := by ring
  apply Complex.ext <;> simp [rectangleClamp,hx,hy]

/-- Projected B ports lie on the left complementary three-piece boundary arc,
strictly to the left of the entire central target interval. -/
theorem central_clamped_left_endpoint (k : ℕ) (hk : 1 ≤ k) (b : LatticeVertex)
    (hb : b ∈ centralLeftDualPorts k) :
    let z := rectangleClamp (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
      (dualFaceCenter unitLatticeMesh b)
    z.re < -(k : ℝ) ∧ (z.re = -13*(k : ℝ) ∨
      z.im = -12*(k : ℝ) ∨ z.im = 12*(k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : b.1+1 ≤ -(k : ℤ) := by rcases hb with hb | hb <;> omega
  have hxR : (b.1 : ℝ)+1 ≤ -(k : ℝ) := by exact_mod_cast hx
  dsimp only
  rw [central_clamp_coordinates,unit_center_coordinates]
  constructor
  · change max (-13*(k : ℝ)) (min (13*(k : ℝ)) ((b.1 : ℝ)+1/2)) < -(k : ℝ)
    exact max_lt (by linarith) ((min_le_right _ _).trans_lt (by linarith))
  · rcases hb with hb | ⟨hy,_,_⟩
    · left
      have he : (b.1 : ℝ) = -13*(k : ℝ)-1 := by exact_mod_cast hb.1
      change max (-13*(k : ℝ)) (min (13*(k : ℝ)) ((b.1 : ℝ)+1/2)) = _
      rw [max_eq_left]
      exact (min_le_right _ _).trans (by linarith)
    · rcases hy with hy | hy
      · right; left
        have he : (b.2 : ℝ) = -12*(k : ℝ)-1 := by exact_mod_cast hy
        change max (-12*(k : ℝ)) (min (12*(k : ℝ)) ((b.2 : ℝ)+1/2)) = _
        rw [max_eq_left]
        exact (min_le_right _ _).trans (by linarith)
      · right; right
        have he : (b.2 : ℝ) = 12*(k : ℝ) := by exact_mod_cast hy
        change max (-12*(k : ℝ)) (min (12*(k : ℝ)) ((b.2 : ℝ)+1/2)) = _
        rw [min_eq_left (by linarith),max_eq_right (by linarith)]

/-- Projected D ports lie on the right complementary boundary arc, strictly
to the right of the entire central target interval. -/
theorem central_clamped_right_endpoint (k : ℕ) (hk : 1 ≤ k) (d : LatticeVertex)
    (hd : d ∈ centralRightDualPorts k) :
    let z := rectangleClamp (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
      (dualFaceCenter unitLatticeMesh d)
    (k : ℝ) < z.re ∧ (z.re = 13*(k : ℝ) ∨
      z.im = -12*(k : ℝ) ∨ z.im = 12*(k : ℝ)) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx : (k : ℤ) ≤ d.1 := by rcases hd with hd | hd <;> omega
  have hxR : (k : ℝ) ≤ (d.1 : ℝ) := by exact_mod_cast hx
  dsimp only
  rw [central_clamp_coordinates,unit_center_coordinates]
  constructor
  · change (k : ℝ) < max (-13*(k : ℝ)) (min (13*(k : ℝ)) ((d.1 : ℝ)+1/2))
    exact (lt_min (by linarith) (by linarith)).trans_le (le_max_right _ _)
  · rcases hd with hd | ⟨hy,_,_⟩
    · left
      have he : (d.1 : ℝ) = 13*(k : ℝ) := by exact_mod_cast hd.1
      change max (-13*(k : ℝ)) (min (13*(k : ℝ)) ((d.1 : ℝ)+1/2)) = _
      rw [min_eq_left (by linarith),max_eq_right (by linarith)]
    · rcases hy with hy | hy
      · right; left
        have he : (d.2 : ℝ) = -12*(k : ℝ)-1 := by exact_mod_cast hy
        change max (-12*(k : ℝ)) (min (12*(k : ℝ)) ((d.2 : ℝ)+1/2)) = _
        rw [max_eq_left]
        exact (min_le_right _ _).trans (by linarith)
      · right; right
        have he : (d.2 : ℝ) = 12*(k : ℝ) := by exact_mod_cast hy
        change max (-12*(k : ℝ)) (min (12*(k : ℝ)) ((d.2 : ℝ)+1/2)) = _
        rw [min_eq_left (by linarith),max_eq_right (by linarith)]

end
end PottsContinuity.PlanarTopology
