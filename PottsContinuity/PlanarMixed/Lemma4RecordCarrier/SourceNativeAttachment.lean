module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.InteriorOriginalEdges
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.OriginalQueryPorts
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.SourceBandQueryAvoidance
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.AnnulusWindowBoundary

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality Push RSW Exploration
noncomputable section

/-- The actual upper query has no OPEN attachment at a native vertex in
any of the three strict connector windows. -/
theorem lemma4_upper_query_no_native_window_attachment
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4DualBandEvent n 0)
    (d : (lemma4AmbientGraph n).edgeSet) (hd : d ∉ lemma4SourceBandReveal n 0 A)
    (u : (box (56*n) : Set LatticeVertex)) (hud : u ∈ d.val)
    (hx : -13*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ 13*(n:ℤ))
    (hy : -3*(n:ℤ) < u.val.2 ∧ u.val.2 < 3*(n:ℤ))
    (b : (lemma4AmbientGraph n).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ lemma4SourceBandReveal n 0 A) : u ∉ b.val := by
  let a := lemma4SourceBandBase n 0
  let B := lemma4SourceDualBandRead n 0 A
  have hB : B ∈ rectangleHorizontalCrossingEvent a (112*n+1) (n-1) :=
    (lemma4SourceDualBandRead_crossing_iff n hn 0 A).mpr hA
  have hraw : lemma4SourceBandReveal n 0 A =
      complementaryRevealPullback _ _ (rectangleDualOriginalEdge (box (56*n)) a (112*n+1) (n-1))
        (rectangleTopReveal a (112*n+1) (n-1) B) := by
    change complementaryRevealPullback _ _ _
      (Exploration.rectangleTopFrontierReveal a (112*n+1) (n-1) B)=_
    rw [rectangleTopFrontierReveal_eq_raw_of_crossing _ _ _ B hB]
  rw [hraw] at hd hb
  intro hub
  have hxi : a.1+1 ≤ u.val.1 ∧ u.val.1 ≤ a.1+((112*n+1:ℕ):ℤ) := by
    change -56*(n:ℤ)-1+1 ≤ u.val.1 ∧ u.val.1 ≤ -56*(n:ℤ)-1+((112*n+1:ℕ):ℤ)
    omega
  have hlo := top_raw_open_query_endpoint_above_bottom _ a _ _ A hB b hbA hb u hub hxi
  have hyi : a.2+1 ≤ u.val.2 ∧ u.val.2 ≤ a.2+((n-1:ℕ):ℤ) := by
    change 2*(n:ℤ)+1 ≤ u.val.2 ∧ u.val.2 ≤ 2*(n:ℤ)+((n-1:ℕ):ℤ)
    change 2*(n:ℤ) < u.val.2 at hlo
    omega
  exact complementary_raw_query_no_open_attachment_at_native_interior _ a _ _ A _ d hd u hud hxi hyi b hbA hb hub

/-- The actual lower reflected query has the same attachment exclusion. -/
theorem lemma4_lower_query_no_native_window_attachment
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4DualBandEvent n 1)
    (d : (lemma4AmbientGraph n).edgeSet) (hd : d ∉ lemma4SourceBandReveal n 1 A)
    (u : (box (56*n) : Set LatticeVertex)) (hud : u ∈ d.val)
    (hx : -13*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ 13*(n:ℤ))
    (hy : -3*(n:ℤ) < u.val.2 ∧ u.val.2 < 3*(n:ℤ))
    (b : (lemma4AmbientGraph n).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ lemma4SourceBandReveal n 1 A) : u ∉ b.val := by
  let a := lemma4SourceBandBase n 1
  let B := lemma4SourceDualBandRead n 1 A
  have hB : B ∈ rectangleHorizontalCrossingEvent a (112*n+1) (n-1) :=
    (lemma4SourceDualBandRead_crossing_iff n hn 1 A).mpr hA
  have hraw : lemma4SourceBandReveal n 1 A =
      complementaryRevealPullback _ _ (rectangleDualOriginalEdge (box (56*n)) a (112*n+1) (n-1))
        (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a (112*n+1) (n-1))
          (rectangleDualBottomPorts a (112*n+1) (n-1)) B) := by
    change complementaryRevealPullback _ _ _ (rectangleBottomFrontierReveal a (112*n+1) (n-1) B)=_
    rw [rectangleBottomFrontierReveal_eq_raw_of_crossing _ _ _ B hB]
  rw [hraw] at hd hb
  intro hub
  have hxi : a.1+1 ≤ u.val.1 ∧ u.val.1 ≤ a.1+((112*n+1:ℕ):ℤ) := by
    change -56*(n:ℤ)-1+1 ≤ u.val.1 ∧ u.val.1 ≤ -56*(n:ℤ)-1+((112*n+1:ℕ):ℤ)
    omega
  have hhi := bottom_raw_open_query_endpoint_below_top _ a _ _ A hB b hbA hb u hub hxi
  have hyi : a.2+1 ≤ u.val.2 ∧ u.val.2 ≤ a.2+((n-1:ℕ):ℤ) := by
    change -3*(n:ℤ)+1 ≤ u.val.2 ∧ u.val.2 ≤ -3*(n:ℤ)+((n-1:ℕ):ℤ)
    change u.val.2 ≤ -3*(n:ℤ)+((n-1:ℕ):ℤ) at hhi
    omega
  exact complementary_raw_query_no_open_attachment_at_native_interior _ a _ _ A _ d hd u hud hxi hyi b hbA hb hub


/-- A strict connector-window vertex is outside both annulus query cores. -/
theorem lemma4_annulus_query_no_interior_window_endpoint
    (n : ℕ) (j : Fin 3) (b : (lemma4AmbientGraph n).edgeSet)
    (hb : b ∈ lemma4AnnulusBondReveal n)
    (u : (box (56*n) : Set LatticeVertex))
    (hx : (10*(j:ℤ)-13)*(n:ℤ) < u.val.1 ∧
      u.val.1 < (10*(j:ℤ)-7)*(n:ℤ)) : u ∉ b.val := by
  intro hub
  have hrec : (∀ v ∈ b.val, v ∈ vertexBoxRegion (box (56*n)) (5*(n:ℤ),0) (2*n)) ∨
      (∀ v ∈ b.val, v ∈ vertexBoxRegion (box (56*n)) (-5*(n:ℤ),0) (2*n)) := by
    simpa only [lemma4AnnulusBondReveal,Finset.mem_filter,Finset.mem_univ,true_and] using hb
  have hpoint (z : ℤ × ℤ) (hv : u ∈ vertexBoxRegion (box (56*n)) z (2*n)) :
      z.1-2*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ z.1+2*(n:ℤ) := by
    change max |u.val.1-z.1| |u.val.2-z.2| ≤ ((2*n:ℕ):ℤ) at hv
    have h := abs_le.mp ((le_max_left _ _).trans hv)
    norm_num only [Nat.cast_mul,Nat.cast_ofNat] at h
    omega
  rcases hrec with hp | hm
  · have hp' := hpoint _ (hp u hub)
    fin_cases j <;> dsimp at hx hp' <;> omega
  · have hm' := hpoint _ (hm u hub)
    fin_cases j <;> dsimp at hx hm' <;> omega

/-- On the ACTUAL successful joint record, no recorded OPEN bond meets an
interior window vertex incident to any unrevealed original edge. -/
theorem lemma4_joint_query_no_open_native_window_attachment
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n) (j : Fin 3)
    (d : (lemma4AmbientGraph n).edgeSet) (hd : d ∉ lemma4JointSourceReveal n A)
    (u : (box (56*n) : Set LatticeVertex)) (hud : u ∈ d.val)
    (hx : (10*(j:ℤ)-13)*(n:ℤ) < u.val.1 ∧
      u.val.1 < (10*(j:ℤ)-7)*(n:ℤ))
    (hy : -3*(n:ℤ) < u.val.2 ∧ u.val.2 < 3*(n:ℤ))
    (b : (lemma4AmbientGraph n).edgeSet) (hbA : b ∈ A)
    (hb : b ∈ lemma4JointSourceReveal n A) : u ∉ b.val := by
  have hx' : -13*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ 13*(n:ℤ) := by
    fin_cases j <;> dsimp at hx <;> omega
  have hd' : d ∉ lemma4AnnulusBondReveal n ∧
      d ∉ lemma4SourceBandReveal n 0 A ∧ d ∉ lemma4SourceBandReveal n 1 A := by
    simpa only [lemma4JointSourceReveal,jointReveal,Finset.mem_union,not_or] using hd
  have hb' : b ∈ lemma4AnnulusBondReveal n ∨
      b ∈ lemma4SourceBandReveal n 0 A ∨ b ∈ lemma4SourceBandReveal n 1 A := by
    simpa only [lemma4JointSourceReveal,jointReveal,Finset.mem_union] using hb
  rcases hb' with hb' | hb' | hb'
  · exact lemma4_annulus_query_no_interior_window_endpoint n j b hb' u hx
  · exact lemma4_upper_query_no_native_window_attachment n hn A hA.2.1 d hd'.2.1 u hud hx' hy b hbA hb'
  · exact lemma4_lower_query_no_native_window_attachment n hn A hA.2.2 d hd'.2.2 u hud hx' hy b hbA hb'

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
