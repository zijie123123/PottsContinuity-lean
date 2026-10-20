module

public import PottsContinuity.PlanarTopology.CentralConnectorEndpoints
public import PottsContinuity.PlanarTopology.ContinuousThreeArc
public import PottsContinuity.PlanarTopology.WalkIntersection
public import PottsContinuity.PD.Duality.RectangleWalks
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Curves PD.FK.Medial
noncomputable section

/-- The real coordinates of a complex point. -/
def complexCoordinates (z : ℂ) : ℝ × ℝ := (z.re,z.im)

theorem continuous_complexCoordinates : Continuous complexCoordinates := by
  unfold complexCoordinates
  fun_prop

/-- Unit-mesh interpolation of the actual walk, expressed in real coordinates. -/
def latticePairCurve {u v : LatticeVertex} (p : PD.squareLattice.Walk u v) :
    Path ((u.1 : ℝ),(u.2 : ℝ)) ((v.1 : ℝ),(v.2 : ℝ)) :=
  ((latticeWalkPath unitLatticeMesh p).map continuous_complexCoordinates).cast
    (by simp [complexCoordinates,latticeEmbed,unitLatticeMesh])
    (by simp [complexCoordinates,latticeEmbed,unitLatticeMesh])

/-- Coordinate bounds on the visited vertices bound the whole interpolated curve. -/
theorem latticePairCurve_bounds {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    {l r b t : ℝ}
    (hp : ∀ z ∈ p.support, l ≤ (z.1 : ℝ) ∧ (z.1 : ℝ) ≤ r ∧
      b ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ t) :
    ∀ z ∈ Set.range (latticePairCurve p), l ≤ z.1 ∧ z.1 ≤ r ∧ b ≤ z.2 ∧ z.2 ≤ t := by
  rintro z ⟨θ,rfl⟩
  exact latticeWalkPath_coordinate_bounds p hp θ

/-- A real-coordinate intersection still gives an actual shared lattice vertex. -/
theorem latticePairCurves_common_vertex {u v x y : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (q : PD.squareLattice.Walk x y)
    {s t : unitInterval} (hst : latticePairCurve p s = latticePairCurve q t) :
    ∃ z, z ∈ p.support ∧ z ∈ q.support := by
  apply latticeWalkPaths_intersection_common_support unitLatticeMesh p q
  apply Complex.ext
  · exact congrArg Prod.fst hst
  · exact congrArg Prod.snd hst

/-- Changing to real coordinates preserves disjointness from a lattice curve. -/
theorem latticePairCurve_disjoint {u v : LatticeVertex} (p : PD.squareLattice.Walk u v)
    {a b : ℂ} (Q : Path a b)
    (h : Disjoint (Set.range (latticeWalkPath unitLatticeMesh p)) (Set.range Q)) :
    Disjoint (Set.range (latticePairCurve p))
      (Set.range (Q.map continuous_complexCoordinates)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨s,hs⟩ ⟨t,ht⟩
  have he : latticeWalkPath unitLatticeMesh p s = Q t := by
    apply Complex.ext
    · exact congrArg Prod.fst (hs.trans ht.symm)
    · exact congrArg Prod.snd (hs.trans ht.symm)
  exact Set.disjoint_left.mp h ⟨s,rfl⟩ ⟨t,he.symm⟩

/-- At integral scale 12k the m-path's curve is confined to the exact central box. -/
theorem kst_mpath_pairCurve_bounds (k : ℕ) {u v : LatticeVertex}
    (p : PD.squareLattice.Walk u v) (hp : BD12.kstMPath (12*k) p) :
    ∀ z ∈ Set.range (latticePairCurve p),
      -13*(k : ℝ) ≤ z.1 ∧ z.1 ≤ 13*(k : ℝ) ∧
      -12*(k : ℝ) ≤ z.2 ∧ z.2 ≤ 12*(k : ℝ) := by
  apply latticePairCurve_bounds
  intro z hz
  obtain ⟨hx,hy⟩ := hp.2.2.2.2.2 z hz
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hx hy
  have hx' : |z.1| ≤ 13*(k : ℤ) := by omega
  obtain ⟨hxl,hxr⟩ := abs_le.mp hx'
  obtain ⟨hyl,hyr⟩ := abs_le.mp hy
  exact ⟨by exact_mod_cast hxl,by exact_mod_cast hxr,
    by exact_mod_cast hyl,by exact_mod_cast hyr⟩

/-- Every integral-scale m-path meets the continuous B/D avoidance connector.
This is a continuous intersection statement: the connector is not asserted to
be a lattice path. -/
theorem kst_mpath_meets_connector (k : ℕ) (hk : 1 ≤ k)
    {u v b d : LatticeVertex} (p : PD.squareLattice.Walk u v)
    (hp : BD12.kstMPath (12*k) p)
    (hb : b ∈ centralLeftDualPorts k) (hd : d ∈ centralRightDualPorts k)
    (Q : Path
      (rectangleClamp (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
        (dualFaceCenter unitLatticeMesh b))
      (rectangleClamp (-13*(k : ℤ),-12*(k : ℤ)) (26*k) (24*k)
        (dualFaceCenter unitLatticeMesh d)))
    (hQ : ∀ θ, -13*(k : ℝ) ≤ (Q θ).re ∧ (Q θ).re ≤ 13*(k : ℝ) ∧
      -12*(k : ℝ) ≤ (Q θ).im ∧ (Q θ).im ≤ 12*(k : ℝ)) :
    (Set.range (latticePairCurve p) ∩
      Set.range (Q.map continuous_complexCoordinates)).Nonempty := by
  have huabs := hp.2.2.2.1
  have hvabs := hp.2.2.2.2.1
  simp only [Nat.cast_mul,Nat.cast_ofNat] at huabs hvabs
  have hu' : |u.1| ≤ (k : ℤ) := by omega
  have hv' : |v.1| ≤ (k : ℤ) := by omega
  obtain ⟨hul,hur⟩ := abs_le.mp hu'
  obtain ⟨hvl,hvr⟩ := abs_le.mp hv'
  have huc : -(k : ℝ) ≤ (u.1 : ℝ) ∧ (u.1 : ℝ) ≤ k :=
    ⟨by exact_mod_cast hul,by exact_mod_cast hur⟩
  have hvc : -(k : ℝ) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) ≤ k :=
    ⟨by exact_mod_cast hvl,by exact_mod_cast hvr⟩
  have htop : (u.2 : ℝ) = 12*(k : ℝ) := by exact_mod_cast hp.2.1
  have hbottom : (v.2 : ℝ) = -12*(k : ℝ) := by exact_mod_cast hp.2.2.1
  exact continuous_three_arc_paths_intersect (-13*k) (13*k) (-12*k) (12*k) (-k) k
    (latticePairCurve p) (Q.map continuous_complexCoordinates)
    (kst_mpath_pairCurve_bounds k p hp) (by rintro z ⟨θ,rfl⟩; exact hQ θ)
    htop hbottom huc hvc (central_clamped_left_endpoint k hk b hb)
    (central_clamped_right_endpoint k hk d hd)

end
end PottsContinuity.PlanarTopology
