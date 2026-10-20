module

public import PottsContinuity.Frozen.Defs
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The actual Euclidean tube in Lemma 7

Source: DCST, proof of Lemma 7, lines 1645–1660. We keep the original
integer lattice. Euclidean recentering is a translation of its embedding
in ℂ, including when the midpoint has a half-integer coordinate.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

/-- The Euclidean embedding, with the complex norm rather than the product sup norm. -/
def tubeLatticePoint (z : ℤ × ℤ) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

/-- Euclidean distance to the closed straight segment between the two endpoints. -/
noncomputable def tubeDistance (u v z : ℤ × ℤ) : ℝ :=
  Metric.infDist (tubeLatticePoint z)
    (segment ℝ (tubeLatticePoint u) (tubeLatticePoint v))

/-- The literal finite tube of radius n^ε in the original square. -/
noncomputable def inductionTube (n : ℕ) (ε : ℝ) (u v : ℤ × ℤ) :
    Finset (ℤ × ℤ) := by
  classical
  exact (box n).filter (fun z => tubeDistance u v z < (n : ℝ)^ε)

/-- Signed area relative to the oriented line from u to v. -/
def tubeLineOffset (u v z : ℤ × ℤ) : ℤ :=
  (v.1-u.1)*(z.2-u.2)-(v.2-u.2)*(z.1-u.1)

/-- Vertices above the tube, with u on the left and v on the right. -/
noncomputable def inductionTubeAbove (n : ℕ) (ε : ℝ) (u v : ℤ × ℤ) :
    Finset (ℤ × ℤ) := by
  classical
  exact (box n).filter (fun z => z ∉ inductionTube n ε u v ∧ 0 < tubeLineOffset u v z)

/-- Vertices below the tube. -/
noncomputable def inductionTubeBelow (n : ℕ) (ε : ℝ) (u v : ℤ × ℤ) :
    Finset (ℤ × ℤ) := by
  classical
  exact (box n).filter (fun z => z ∉ inductionTube n ε u v ∧ tubeLineOffset u v z < 0)

@[simp] theorem mem_inductionTube (n : ℕ) (ε : ℝ) (u v z : ℤ × ℤ) :
    z ∈ inductionTube n ε u v ↔ z ∈ box n ∧ tubeDistance u v z < (n : ℝ)^ε := by
  classical
  simp [inductionTube]

theorem tubeDistance_nonneg (u v z : ℤ × ℤ) : 0 ≤ tubeDistance u v z :=
  Metric.infDist_nonneg

theorem inductionTube_mem_of_segment {n : ℕ} (hn : 1 ≤ n) (ε : ℝ)
    (u v z : ℤ × ℤ) (hz : z ∈ box n)
    (hseg : tubeLatticePoint z ∈ segment ℝ (tubeLatticePoint u) (tubeLatticePoint v)) :
    z ∈ inductionTube n ε u v := by
  rw [mem_inductionTube]
  refine ⟨hz, ?_⟩
  unfold tubeDistance
  rw [Metric.infDist_zero_of_mem hseg]
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) ε

theorem inductionTube_endpoints {n : ℕ} (hn : 1 ≤ n) (ε : ℝ)
    (u v : ℤ × ℤ) (hu : u ∈ box n) (hv : v ∈ box n) :
    u ∈ inductionTube n ε u v ∧ v ∈ inductionTube n ε u v :=
  ⟨inductionTube_mem_of_segment hn ε u v u hu (left_mem_segment ℝ _ _),
   inductionTube_mem_of_segment hn ε u v v hv (right_mem_segment ℝ _ _)⟩

end PottsContinuity.Thm3.Prop4
