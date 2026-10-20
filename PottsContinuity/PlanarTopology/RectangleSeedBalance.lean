module

public import PottsContinuity.PlanarTopology.RectangleConnectionEvents
public import PottsContinuity.PlanarTopology.RectangleProbabilityBalance
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

namespace PottsContinuity.PlanarTopology
open MeasureTheory PD.FK PD.RCInfinite BD12
noncomputable section

/-- Connections from a square of side s whose anchor lies in the rectangle
of admissible anchors. The whole marked square is inside the actual domain. -/
abbrev rectangleSeedConnectionEvent (W H s : ℕ) (v : Fin (W+1) × Fin (H+1))
    (T : Set LatticeVertex) : Set LatticeConfiguration :=
  rectangleConnectionEvent (0,0) (W+s) (H+s)
    (latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) T

/-- DRT's two boundary-probability comparisons and reverse witnesses for actual
sampled rectangle connections. Witness anchors differ by at most one in each
coordinate. This gives finite balancing, without a bulk-escape assertion. -/
theorem rectangle_seed_connection_balanced_cell
    (μ : Measure LatticeConfiguration) [IsProbabilityMeasure μ]
    (W H s : ℕ) (hW : 0 < W) (hH : 0 < H) :
    let L := fun v => μ.real (rectangleSeedConnectionEvent W H s v {z | z.1 = 0})
    let R := fun v => μ.real (rectangleSeedConnectionEvent W H s v {z | z.1 = ((W+s:ℕ):ℤ)})
    let B := fun v => μ.real (rectangleSeedConnectionEvent W H s v {z | z.2 = 0})
    let T := fun v => μ.real (rectangleSeedConnectionEvent W H s v {z | z.2 = ((H+s:ℕ):ℤ)})
    ∃ v, R v ≤ L v ∧ T v ≤ B v ∧
      ∃ x, L x ≤ R x ∧ (x.1.val ≤ v.1.val+1 ∧ v.1.val ≤ x.1.val+1) ∧
        (x.2.val ≤ v.2.val+1 ∧ v.2.val ≤ x.2.val+1) ∧
      ∃ y, B y ≤ T y ∧ (y.1.val ≤ v.1.val+1 ∧ v.1.val ≤ y.1.val+1) ∧
        (y.2.val ≤ v.2.val+1 ∧ v.2.val ≤ y.2.val+1) := by
  classical
  have hone (v : Fin (W+1) × Fin (H+1)) (dx dy : ℕ) (hx : dx ≤ s) (hy : dy ≤ s)
      (T : Set LatticeVertex)
      (ht : ((v.1.val:ℤ)+(dx:ℤ),(v.2.val:ℤ)+(dy:ℤ)) ∈ T) :
      μ.real (rectangleSeedConnectionEvent W H s v T) = 1 := by
    let z : LatticeVertex := ((v.1.val:ℤ)+(dx:ℤ),(v.2.val:ℤ)+(dy:ℤ))
    have hvx := v.1.isLt
    have hvy := v.2.isLt
    have hd : z ∈ latticeRectangle (0,0) (W+s) (H+s) := by
      rw [mem_latticeRectangle]
      dsimp [z]
      omega
    have hs : z ∈ latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s := by
      rw [mem_latticeRectangle]
      dsimp [z]
      omega
    have heq := rectangleConnectionEvent_eq_univ_of_common_vertex (0,0) (W+s) (H+s)
      (latticeRectangle ((v.1.val:ℤ),(v.2.val:ℤ)) s s : Set LatticeVertex) T ⟨z,hd⟩ hs ht
    change μ.real (rectangleConnectionEvent _ _ _ _ _) = 1
    rw [heq]
    simp [Measure.real_def]
  dsimp only
  apply rectangle_probability_profiles_balanced_cell W H hW hH
  · intro v hv
    have hz : v.1.val = 0 := congrArg Fin.val hv
    have hp := hone v 0 0 (Nat.zero_le s) (Nat.zero_le s) {z | z.1 = 0}
      (by change (v.1.val:ℤ)+0 = 0; omega)
    rw [hp]
    exact measureReal_le_one
  · intro v hv
    have hp := hone v s 0 le_rfl (Nat.zero_le s) {z | z.1 = ((W+s:ℕ):ℤ)}
      (by change (v.1.val:ℤ)+(s:ℤ) = ((W+s:ℕ):ℤ); omega)
    rw [hp]
    exact measureReal_le_one
  · intro v hv
    have hz : v.2.val = 0 := congrArg Fin.val hv
    have hp := hone v 0 0 (Nat.zero_le s) (Nat.zero_le s) {z | z.2 = 0}
      (by change (v.2.val:ℤ)+0 = 0; omega)
    rw [hp]
    exact measureReal_le_one
  · intro v hv
    have hp := hone v 0 s (Nat.zero_le s) le_rfl {z | z.2 = ((H+s:ℕ):ℤ)}
      (by change (v.2.val:ℤ)+(s:ℤ) = ((H+s:ℕ):ℤ); omega)
    rw [hp]
    exact measureReal_le_one

end
end PottsContinuity.PlanarTopology
