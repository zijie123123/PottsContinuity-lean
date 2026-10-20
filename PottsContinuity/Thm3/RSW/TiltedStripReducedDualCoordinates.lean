module

public import PottsContinuity.Thm3.RSW.TiltedStripReducedCarrier

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial Thm3.Prop4
noncomputable section

/-- Actual dual face labels under the chosen half-turn and staircase phase. -/
def tiltedStripReducedDualVertex (N : ℕ) (t : ℝ) (z : LatticeVertex) : LatticeVertex :=
  (-z.1-(if 0 < t then 1 else 0),(N : ℤ)-1-z.2)

/-- Normalize the image of an actual dual bond under that same vertex map. -/
def tiltedStripReducedDualBond (N : ℕ) (t : ℝ) (d : LatticeBond) : LatticeBond :=
  match d.axis with
  | .horizontal => ⟨(-d.base.1-(if 0 < t then 1 else 0)-1,(N : ℤ)-1-d.base.2),.horizontal⟩
  | .vertical => ⟨(-d.base.1-(if 0 < t then 1 else 0),(N : ℤ)-1-d.base.2-1),.vertical⟩

/-- The normalization preserves exactly the unordered transported endpoints. -/
theorem tiltedStripReducedDualBond_pair (N : ℕ) (t : ℝ) (d : LatticeBond) :
    Sym2.map (tiltedStripReducedDualVertex N t) d.toSym2 =
      (tiltedStripReducedDualBond N t d).toSym2 := by
  rcases d with ⟨⟨x,y⟩,ax⟩
  cases ax <;> by_cases hp : 0 < t
  all_goals
    simp [tiltedStripReducedDualVertex,tiltedStripReducedDualBond,
      LatticeBond.toSym2,LatticeBond.source,LatticeBond.target,hp]; omega

/-- The crossed map is literally dualization followed by the dual vertex
half-turn, rather than an axis-preserving original-edge relabeling. -/
theorem tiltedStripReducedDualBond_dualBondOfPrimal (N : ℕ) (t : ℝ) (b : LatticeBond) :
    tiltedStripReducedDualBond N t (dualBondOfPrimal b) =
      tiltedStripReducedCrossedBond N t b := by
  rcases b with ⟨⟨x,y⟩,ax⟩
  cases ax <;> by_cases hp : 0 < t
  all_goals
    simp [tiltedStripReducedDualBond,dualBondOfPrimal,tiltedStripReducedCrossedBond,hp] <;> omega

/-- Statewise genuine crossed-dual endpoint identity, on every original bond. -/
theorem tiltedStripReducedDualBond_dualBondOfPrimal_pair
    (N : ℕ) (t : ℝ) (b : LatticeBond) :
    Sym2.map (tiltedStripReducedDualVertex N t) (dualBondOfPrimal b).toSym2 =
      (tiltedStripReducedCrossedBond N t b).toSym2 := by
  rw [tiltedStripReducedDualBond_pair,tiltedStripReducedDualBond_dualBondOfPrimal]

end
end PottsContinuity.RSW
