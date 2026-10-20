module

public import PottsContinuity.PlanarTopology.WalkIntersection
public import PottsContinuity.PD.Duality.RectangleWalks
public import PottsContinuity.PD.Duality.RectanglePathIntersection
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-! Opposite-side lattice walks in a rectangle share a vertex of their original supports.
This includes repeated visits and degenerate rectangles. No simplicity is needed.
-/

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PottsContinuity.PD.FK PottsContinuity.PD.FK.Curves unitInterval
noncomputable section

 def unitMesh : PositiveMesh := ⟨1, by norm_num⟩
def complexPair (z : ℂ) : ℝ × ℝ := (z.re, z.im)
private theorem continuous_complexPair : Continuous complexPair := by
  unfold complexPair
  fun_prop

/-- A left-right walk and a bottom-top walk in the same closed lattice rectangle meet.
The common vertex belongs to both given walks, not just to their connected components. -/
theorem rectangle_walks_common_vertex
    {a b c d : ℤ} {u v u' v' : LatticeVertex}
    (p : squareLattice.Walk u v) (q : squareLattice.Walk u' v')
    (hab : a ≤ b) (hcd : c ≤ d)
    (hp : ∀ x ∈ p.support, a ≤ x.1 ∧ x.1 ≤ b ∧ c ≤ x.2 ∧ x.2 ≤ d)
    (hq : ∀ x ∈ q.support, a ≤ x.1 ∧ x.1 ≤ b ∧ c ≤ x.2 ∧ x.2 ≤ d)
    (hu : u.1 = a) (hv : v.1 = b) (hu' : u'.2 = c) (hv' : v'.2 = d) :
    ∃ x, x ∈ p.support ∧ x ∈ q.support := by
  let P := (latticeWalkPath unitMesh p).map continuous_complexPair
  let Q := (latticeWalkPath unitMesh q).map continuous_complexPair
  have hpR : ∀ x ∈ p.support,
      (a : ℝ) ≤ (x.1 : ℝ) ∧ (x.1 : ℝ) ≤ (b : ℝ) ∧
      (c : ℝ) ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ (d : ℝ) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hp x hx
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4⟩
  have hqR : ∀ x ∈ q.support,
      (a : ℝ) ≤ (x.1 : ℝ) ∧ (x.1 : ℝ) ≤ (b : ℝ) ∧
      (c : ℝ) ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ (d : ℝ) := by
    intro x hx
    obtain ⟨h1, h2, h3, h4⟩ := hq x hx
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
      by exact_mod_cast h3, by exact_mod_cast h4⟩
  have hPb : ∀ t, (a : ℝ) ≤ (P t).1 ∧ (P t).1 ≤ (b : ℝ) ∧
      (c : ℝ) ≤ (P t).2 ∧ (P t).2 ≤ (d : ℝ) :=
    latticeWalkPath_coordinate_bounds p hpR
  have hQb : ∀ t, (a : ℝ) ≤ (Q t).1 ∧ (Q t).1 ≤ (b : ℝ) ∧
      (c : ℝ) ≤ (Q t).2 ∧ (Q t).2 ≤ (d : ℝ) :=
    latticeWalkPath_coordinate_bounds q hqR
  have hPl : (P 0).1 = (a : ℝ) := by
    simpa [complexPair, latticeEmbed, unitMesh, hu] using congrArg Prod.fst P.source'
  have hPr : (P 1).1 = (b : ℝ) := by
    simpa [complexPair, latticeEmbed, unitMesh, hv] using congrArg Prod.fst P.target'
  have hQb' : (Q 0).2 = (c : ℝ) := by
    simpa [complexPair, latticeEmbed, unitMesh, hu'] using congrArg Prod.snd Q.source'
  have hQt : (Q 1).2 = (d : ℝ) := by
    simpa [complexPair, latticeEmbed, unitMesh, hv'] using congrArg Prod.snd Q.target'
  obtain ⟨s, t, hst⟩ := pathRectangle_crossing_intersection
    (a := ((a : ℝ), (c : ℝ))) (b := ((b : ℝ), (d : ℝ))) P Q
    (by change (a : ℝ) ≤ (b : ℝ); exact_mod_cast hab)
    (by change (c : ℝ) ≤ (d : ℝ); exact_mod_cast hcd) hPb hQb hPl hPr hQb' hQt
  apply latticeWalkPaths_intersection_common_support unitMesh p q
  apply Complex.ext
  · exact congrArg Prod.fst hst
  · exact congrArg Prod.snd hst

end
end PottsContinuity.PlanarTopology
