module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.HorizontalSeedQueries
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.SourceBandQueryAvoidance

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality Push RSW Exploration
noncomputable section

/-- On success the actual top source reveal queries every bond crossing the
upper boundary of a connector window, whatever that bond's state. -/
theorem lemma4_upper_window_exit_queried
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4DualBandEvent n 0) (x : ℤ)
    (hx : -13*(n:ℤ) ≤ x ∧ x ≤ 13*(n:ℤ))
    (e : (lemma4AmbientGraph n).edgeSet)
    (he : frozenEdgeEmbedding (box (56*n)) e=
      latticeBondEdge ⟨(x,3*(n:ℤ)-1),LatticeAxis.vertical⟩) :
    e ∈ lemma4SourceBandReveal n 0 A := by
  let a := lemma4SourceBandBase n 0
  let B := lemma4SourceDualBandRead n 0 A
  have hB := (lemma4SourceDualBandRead_crossing_iff n hn 0 A).mpr hA
  have hraw := rectangleTopFrontierReveal_eq_raw_of_crossing a (112*n+1) (n-1) B hB
  change e ∈ complementaryRevealPullback _ _ _
    (Exploration.rectangleTopFrontierReveal a (112*n+1) (n-1) B)
  rw [hraw]
  apply top_raw_query_contains_vertical_boundary_bond
  · change -56*(n:ℤ)-1+1 ≤ x ∧ x ≤ -56*(n:ℤ)-1+((112*n+1:ℕ):ℤ)
    omega
  · have hrow : a.2+((n-1:ℕ):ℤ)=3*(n:ℤ)-1 := by
      change 2*(n:ℤ)+((n-1:ℕ):ℤ)=3*(n:ℤ)-1
      omega
    simpa only [hrow] using he

/-- The actual lower reflected source reveal queries every lower window exit. -/
theorem lemma4_lower_window_exit_queried
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4DualBandEvent n 1) (x : ℤ)
    (hx : -13*(n:ℤ) ≤ x ∧ x ≤ 13*(n:ℤ))
    (e : (lemma4AmbientGraph n).edgeSet)
    (he : frozenEdgeEmbedding (box (56*n)) e=
      latticeBondEdge ⟨(x,-3*(n:ℤ)),LatticeAxis.vertical⟩) :
    e ∈ lemma4SourceBandReveal n 1 A := by
  let a := lemma4SourceBandBase n 1
  let B := lemma4SourceDualBandRead n 1 A
  have hB := (lemma4SourceDualBandRead_crossing_iff n hn 1 A).mpr hA
  have hraw := rectangleBottomFrontierReveal_eq_raw_of_crossing a (112*n+1) (n-1) B hB
  change e ∈ complementaryRevealPullback _ _ _ (rectangleBottomFrontierReveal a (112*n+1) (n-1) B)
  rw [hraw]
  apply bottom_raw_query_contains_vertical_boundary_bond
  · change -56*(n:ℤ)-1+1 ≤ x ∧ x ≤ -56*(n:ℤ)-1+((112*n+1:ℕ):ℤ)
    omega
  · exact he

/-- An actual native bond at a strict-height window vertex stays within the
strict-height strip. This is independent of both sampled edge states. -/
theorem lemma4_unqueried_edge_preserves_window_height
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n)
    (e : (lemma4AmbientGraph n).edgeSet) (he : e ∉ lemma4JointSourceReveal n A)
    (u v : (box (56*n) : Set LatticeVertex)) (huv : e.val=s(u,v))
    (hx : -13*(n:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ 13*(n:ℤ))
    (hy : -3*(n:ℤ) < u.val.2 ∧ u.val.2 < 3*(n:ℤ)) :
    -3*(n:ℤ) < v.val.2 ∧ v.val.2 < 3*(n:ℤ) := by
  have hadj : PD.FK.squareLattice.Adj u.val v.val := by
    have h := e.property
    rw [huv] at h
    exact (lemma4AmbientGraph n).mem_edgeSet.mp h
  have hstep := (PD.FK.squareLattice_adj_iff u.val v.val).mp hadj
  have he' : e ∉ lemma4AnnulusBondReveal n ∧
      e ∉ lemma4SourceBandReveal n 0 A ∧ e ∉ lemma4SourceBandReveal n 1 A := by
    simpa only [lemma4JointSourceReveal,jointReveal,Finset.mem_union,not_or] using he
  constructor
  · by_contra hv
    have hxy : u.val.1=v.val.1 ∧ v.val.2=-3*(n:ℤ) ∧ u.val.2=-3*(n:ℤ)+1 := by omega
    have hemb : frozenEdgeEmbedding (box (56*n)) e=
        latticeBondEdge ⟨(u.val.1,-3*(n:ℤ)),LatticeAxis.vertical⟩ := by
      apply Subtype.ext
      change Sym2.map Subtype.val e.val=s((u.val.1,-3*(n:ℤ)),(u.val.1,-3*(n:ℤ)+1))
      rw [huv]
      apply Sym2.eq_iff.mpr
      right
      constructor <;> apply Prod.ext <;> dsimp <;> omega
    exact he'.2.2 (lemma4_lower_window_exit_queried n hn A hA.2.2 _ hx e hemb)
  · by_contra hv
    have hxy : u.val.1=v.val.1 ∧ u.val.2=3*(n:ℤ)-1 ∧ v.val.2=3*(n:ℤ) := by omega
    have hemb : frozenEdgeEmbedding (box (56*n)) e=
        latticeBondEdge ⟨(u.val.1,3*(n:ℤ)-1),LatticeAxis.vertical⟩ := by
      apply Subtype.ext
      change Sym2.map Subtype.val e.val=s((u.val.1,3*(n:ℤ)-1),(u.val.1,(3*(n:ℤ)-1)+1))
      rw [huv]
      apply Sym2.eq_iff.mpr
      left
      constructor <;> apply Prod.ext <;> dsimp <;> omega
    exact he'.2.1 (lemma4_upper_window_exit_queried n hn A hA.2.1 _ hx e hemb)

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
