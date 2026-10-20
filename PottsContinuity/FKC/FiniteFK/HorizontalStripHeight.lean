-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripHeight.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.WholePlaneClusterContainment
public import PottsContinuity.FKC.Medial.WholePlaneTraversalEvents
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Topology.Clopen

@[expose] public section

namespace PottsContinuity.FKC.Medial

/-- Vertices of the actual zero-tilt strip of height `2*n`. -/
abbrev horizontalStripVertex (n : ℕ) :=
  {v : LatticeVertex // 0 ≤ v.2 ∧ v.2 ≤ (2 * (n : ℤ))}

/-- A literal strip vertex in a fixed column at a natural-number height. -/
def horizontalStripVertexOfNat (n : ℕ) (k : ℤ) (y : ℕ) (hy : y ≤ 2 * n) :
    horizontalStripVertex n :=
  ⟨(k, y), by
    constructor
    · omega
    · change (y : ℤ) ≤ (2 * (n : ℤ))
      exact_mod_cast hy⟩

/-- The graph obtained by restricting the literal whole-plane open graph to the strip. -/
def horizontalStripOpenGraph (n : ℕ) (ω : LatticeConfiguration) :
    SimpleGraph (horizontalStripVertex n) :=
  (wholePlaneOpenPrimalGraph ω).induce (fun v : LatticeVertex =>
    0 ≤ v.2 ∧ v.2 ≤ (2 * (n : ℤ)))

/-- Actual open connectivity from an in-strip vertex to some point on the top row. -/
def horizontalStripTopReachable (n : ℕ) (ω : LatticeConfiguration)
    (v : horizontalStripVertex n) : Prop :=
  ∃ x : ℤ,
    (horizontalStripOpenGraph n ω).Reachable v
      (horizontalStripVertexOfNat n x (2 * n) (le_rfl))

/-- Heights in the strip from which the fixed column is connected to the top row. -/
noncomputable def horizontalStripTopHeights (n : ℕ) (ω : LatticeConfiguration) (k : ℤ) : Set ℕ := by
  classical
  exact {y | ∃ hy : y ≤ 2 * n,
    horizontalStripTopReachable n ω (horizontalStripVertexOfNat n k y hy)}

theorem horizontalStripTopHeights_nonempty (n : ℕ) (ω : LatticeConfiguration)
    (k : ℤ) : ∃ y, y ∈ horizontalStripTopHeights n ω k := by
  classical
  refine ⟨2 * n, ⟨le_rfl, ?_⟩⟩
  exact ⟨k, SimpleGraph.Reachable.refl _⟩

/-- The least height in a fixed column from which the top row is reachable. -/
noncomputable def horizontalStripHeight (n : ℕ) (ω : LatticeConfiguration) (k : ℤ) : ℕ := by
  classical
  exact Nat.find (horizontalStripTopHeights_nonempty n ω k)

theorem horizontalStripHeight_spec (n : ℕ) (ω : LatticeConfiguration) (k : ℤ) :
    ∃ h : horizontalStripHeight n ω k ≤ 2 * n,
      horizontalStripTopReachable n ω
        (horizontalStripVertexOfNat n k (horizontalStripHeight n ω k) h) := by
  classical
  exact Nat.find_spec (horizontalStripTopHeights_nonempty n ω k)

theorem horizontalStripHeight_no_lower_top_connection
    (n : ℕ) (ω : LatticeConfiguration) (k : ℤ) (y : ℕ)
    (hy : y < horizontalStripHeight n ω k) :
    ¬ horizontalStripTopReachable n ω
      (horizontalStripVertexOfNat n k y
        (le_trans (Nat.le_of_lt hy) (horizontalStripHeight_spec n ω k).choose)) := by
  classical
  intro hconn
  have hmem : y ∈ horizontalStripTopHeights n ω k :=
    ⟨le_trans (Nat.le_of_lt hy) (horizontalStripHeight_spec n ω k).choose, hconn⟩
  have hmin := Nat.find_min' (horizontalStripTopHeights_nonempty n ω k) (m := y) hmem
  change horizontalStripHeight n ω k ≤ y at hmin
  omega

end PottsContinuity.FKC.Medial
