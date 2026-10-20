module

public import PottsContinuity.BD12.DRTCentredSmallScale
public import PottsContinuity.BD12.DRTHalvingSum
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-! The actual source bound M<=2*S_n under the wired Lambda_2n law. Domain
comparison, translation, radius monotonicity and multiplicities are proved. -/

@[expose] public section

namespace PottsContinuity.BD12
open PD.FK PD.RCInfinite
noncomputable section
open scoped Classical

/-- Every inner-centred one-arm partial sum is bounded by twice the source sum. -/
theorem drt_centred_one_arm_sum_le_twice_source (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) (c : LatticeVertex) (n : ℕ)
    (u : (latticeBox c n : Set LatticeVertex)) :
    (∑ k ∈ Finset.range n, drtMean (finiteLatticeGraph (latticeBox c (2*n))) q
      (BoundaryCondition.wired (boxVertexBoundary c (2*n)))
      (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β
      (radiusOneArmIndicator (finiteLatticeGraph (latticeBox c (2*n)))
        (fun v => latticeRadius u.val v.val) (radiusBoxInclusion c n (2*n) (by omega) u) k)) ≤
      2 * drtWiredOneArmSum q β n := by
  let H := finiteLatticeGraph (latticeBox c (2*n))
  let ξ := BoundaryCondition.wired (boxVertexBoundary c (2*n))
  let J : H.edgeSet → Set.Ioi (0 : ℝ) := fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩
  let r := fun v : (latticeBox c (2*n) : Set LatticeVertex) => latticeRadius u.val v.val
  let o := radiusBoxInclusion c n (2*n) (by omega) u
  let a := fun k => drtMean H q ξ J β (radiusOneArmIndicator H r o k)
  have hanti : Antitone a := drt_radius_one_arm_antitone H q ξ J β r o
    (latticeRadius_self u.val) (fun h => latticeRadius_step u.val h)
  have hbound (k : ℕ) (hk : k ∈ Finset.range n) : a k ≤ drtWiredOneArmMean q β (k/2) := by
    have hhalf : 2*(k/2) ≤ n := by
      have hkn := Finset.mem_range.mp hk
      omega
    exact (hanti (Nat.div_le_self k 2)).trans
      (drt_centred_small_one_arm_le_sequence q hq β c n (k/2) u hhalf)
  change (∑ k ∈ Finset.range n, a k) ≤ 2 * ∑ k ∈ Finset.range n, drtWiredOneArmMean q β k
  exact (Finset.sum_le_sum (fun k hk => hbound k hk)).trans
    (drt_sum_halved_le_twice _ (fun k => (drtWiredOneArmMean_mem_Icc q β k).1) n)

/-- DRT's denominator comparison for the actual full outer centred maximum. -/
theorem drtBoxOuterArmMaximum_le_twice_source (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (β : Set.Ioi (0 : ℝ)) (c : LatticeVertex) (n : ℕ) :
    drtBoxOuterArmMaximum c n (2*n) (by omega) q
      (BoundaryCondition.wired (boxVertexBoundary c (2*n)))
      (fun _ => ⟨1, (show (0 : ℝ) < 1 from zero_lt_one)⟩) β ≤ 2 * drtWiredOneArmSum q β n := by
  unfold drtBoxOuterArmMaximum
  apply Finset.max'_le
  intro y hy
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hy
  exact drt_centred_one_arm_sum_le_twice_source q hq β c n u

end
end PottsContinuity.BD12
