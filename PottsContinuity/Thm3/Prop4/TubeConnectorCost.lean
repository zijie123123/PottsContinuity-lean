module

public import PottsContinuity.Thm3.Prop4.RetainedCentralRows
public import PottsContinuity.Thm3.Prop4.TubeConnectorHeights
public import PottsContinuity.Thm3.Prop4.TubeSurgery

/-!
# Exact count and finite-energy cost of both retained connectors

Only actual remaining original edges are counted. Their two interval lengths
are less than eight radii plus one, including both physical stopping cases.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

/-- The actual connector union has the row-length count, even for empty intervals. -/
theorem tube_connector_union_card_le (n : ℕ) (r : ℝ) (u v : LatticeVertex)
    (lo hi L U : ℤ) :
    (tubeRemainingCentralRows n r u v (L+1) (lo-1) ∪
      tubeRemainingCentralRows n r u v (hi+1) U).card ≤
        (lo-1-L).toNat+(U-hi).toNat := by
  classical
  have hL := tubeRemainingCentralRows_card_le n r u v (L+1) (lo-1)
  have hU := tubeRemainingCentralRows_card_le n r u v (hi+1) U
  simp only [Int.card_Icc] at hL hU
  have heL : lo-1+1-(L+1) = lo-1-L := by omega
  have heU : U+1-(hi+1) = U-hi := by omega
  rw [heL] at hL
  rw [heU] at hU
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hL hU)

/-- Both stopped connectors cost at most nine radii worth of closed original edges. -/
theorem tube_connector_union_card_bound {n : ℕ} (hn : 1 ≤ n) (r : ℝ) (hr : 1 ≤ r)
    (u v : LatticeVertex) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi) :
    let L := max (-(n : ℤ)-1) ⌊b-2*r⌋;
    let U := min (n : ℤ) ⌈b+2*r⌉;
    ((tubeRemainingCentralRows n r u v (L+1) (lo-1) ∪
      tubeRemainingCentralRows n r u v (hi+1) U).card : ℝ) ≤ 9*r := by
  dsimp only
  have hL := central_cut_lower_connector_stopped hn r u v t b ht hu hv lo hi hlohi hrows
  have hU := central_cut_upper_connector_stopped hn r u v t b ht hu hv lo hi hlohi hrows
  have hc := tube_connector_union_card_le n r u v lo hi
    (max (-(n : ℤ)-1) ⌊b-2*r⌋) (min (n : ℤ) ⌈b+2*r⌉)
  have hcR : ((tubeRemainingCentralRows n r u v
      (max (-(n : ℤ)-1) ⌊b-2*r⌋+1) (lo-1) ∪
      tubeRemainingCentralRows n r u v (hi+1) (min (n : ℤ) ⌈b+2*r⌉)).card : ℝ) ≤ ((lo-1-max (-(n : ℤ)-1) ⌊b-2*r⌋).toNat : ℝ)+
      ((min (n : ℤ) ⌈b+2*r⌉-hi).toNat : ℝ) := by exact_mod_cast hc
  have hminus : (0 : ℤ) ≤ lo-1-max (-(n : ℤ)-1) ⌊b-2*r⌋ := by omega
  have hplus : (0 : ℤ) ≤ min (n : ℤ) ⌈b+2*r⌉-hi := by omega
  have hmR : ((lo-1-max (-(n : ℤ)-1) ⌊b-2*r⌋).toNat : ℝ) =
      ((lo-1-max (-(n : ℤ)-1) ⌊b-2*r⌋ : ℤ) : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hminus]
  have hpR : ((min (n : ℤ) ⌈b+2*r⌉-hi).toNat : ℝ) =
      ((min (n : ℤ) ⌈b+2*r⌉-hi : ℤ) : ℝ) := by
    rw [← Int.cast_natCast,Int.toNat_of_nonneg hplus]
  rw [hmR,hpR] at hcR
  linarith only [hcR,hL.2.2.1,hU.2.2.1,hr]

/-- The literal retained connector set has the same parameter-only exponential cost. -/
theorem tube_connector_closing_cost_lower (θ : Parameters) {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) (u v : LatticeVertex) (t b : ℝ) (ht : |t| ≤ 1)
    (hu : (u.2 : ℝ) = t*u.1+b) (hv : (v.2 : ℝ) = t*v.1+b)
    (lo hi : ℤ) (hlohi : lo ≤ hi)
    (hrows : radiusTubeCutRows n r u v 0 = Finset.Icc lo hi) :
    let L := max (-(n : ℤ)-1) ⌊b-2*r⌋;
    let U := min (n : ℤ) ⌈b+2*r⌉;
    Real.exp (-tubeClosingCoefficient θ*r) ≤
      (1-edgeParameter θ)^(tubeRemainingCentralRows n r u v (L+1) (lo-1) ∪
        tubeRemainingCentralRows n r u v (hi+1) U).card := by
  dsimp only
  have hc := tube_connector_union_card_bound hn r hr u v t b ht hu hv lo hi hlohi hrows
  have hs := one_sub_edgeParameter_pos θ
  have hlog := Real.log_neg hs (show 1-edgeParameter θ < 1 by linarith only [edgeParameter_pos θ])
  calc
    _ ≤ Real.exp ((tubeRemainingCentralRows n r u v
        (max (-(n : ℤ)-1) ⌊b-2*r⌋+1) (lo-1) ∪
        tubeRemainingCentralRows n r u v (hi+1) (min (n : ℤ) ⌈b+2*r⌉)).card *
        Real.log (1-edgeParameter θ)) := by
      apply Real.exp_le_exp.mpr
      unfold tubeClosingCoefficient
      nlinarith only [mul_le_mul_of_nonpos_right hc hlog.le]
    _ = _ := by rw [Real.exp_nat_mul,Real.exp_log hs]

end
end PottsContinuity.Thm3.Prop4
