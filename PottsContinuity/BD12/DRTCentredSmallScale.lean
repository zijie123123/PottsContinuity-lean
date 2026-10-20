module

public import PottsContinuity.BD12.DRTWiredOneArmSequence
public import PottsContinuity.BD12.FiniteWiredOneArmComparison
public import PottsContinuity.BD12.LatticeBoxContainment
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! The actual small-scale wired comparison in DRT: centred one-arm events in
Lambda_2n are bounded by the source theta_k whenever 2k<=n. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- Domain comparison and translation, with both the event restriction and
literal translated-box containment discharged. -/
theorem drt_centred_small_one_arm_le_sequence (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) (c : LatticeVertex) (n k : ℕ)
    (u : (latticeBox c n : Set LatticeVertex)) (hk : 2*k ≤ n) :
    drtMean (finiteLatticeGraph (latticeBox c (2*n))) q
        (BoundaryCondition.wired (boxVertexBoundary c (2*n)))
        (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β
        (radiusOneArmIndicator (finiteLatticeGraph (latticeBox c (2*n)))
          (fun v => latticeRadius u.val v.val) (radiusBoxInclusion c n (2*n) (by omega) u) k) ≤
      drtWiredOneArmMean q β k := by
  have hST := latticeBox_twice_subset_outer c n k u hk
  have hb : latticeBox u.val k ⊆ latticeBox u.val (2*k) := latticeBox_mono u.val (by omega)
  have hcomp := drt_finite_wired_one_arm_mean_le q hq β hST u.val k hb
    (radiusBoxCenter u.val (2*k)) rfl
  have hcenter : latticeTranslate u.val (0,0) = u.val := by
    ext <;> simp only [latticeTranslate, zero_add]
  have ht := drtMean_wired_box_one_arm_translation q hq β u.val (0,0) k (2*k)
  let F : LatticeVertex → ℝ := fun v => drtMean (boxGraph v (2*k)) q
    (BoundaryCondition.wired (boxVertexBoundary v (2*k)))
    (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β (boxOuterOneArmIndicator v k (2*k))
  have ht' : F (latticeTranslate u.val (0,0)) = F (0,0) := ht
  rw [hcenter] at ht'
  exact hcomp.trans_eq ht'

end
end PottsContinuity.BD12
