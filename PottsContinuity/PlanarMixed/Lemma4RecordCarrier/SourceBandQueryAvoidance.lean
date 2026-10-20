module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.SourceUpperQueryAvoidance
public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.VerticalReflectionQueries

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality Push RSW Exploration
noncomputable section

/-- Actual lower-band queries have an original endpoint of index zero.
The reflected top-frontier reveal is identified with the direct bottom exploration. -/
theorem lemma4_source_lower_query_original_endpoint_zero
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4DualBandEvent n 1)
    {z : LatticeVertex} (P : PD.FK.squareLattice.Walk z z)
    (hclosed : finiteDualWalkClosed (box (56*n)) A P)
    (hlower : ∀ v ∈ P.support, -3*(n:ℤ) ≤ v.2)
    (e : (lemma4AmbientGraph n).edgeSet) (he : e ∈ lemma4SourceBandReveal n 1 A) :
    ∃ v ∈ e.val, rayIndex v.val P=0 := by
  let a := lemma4SourceBandBase n 1
  let B := lemma4SourceDualBandRead n 1 A
  have hB : B ∈ rectangleHorizontalCrossingEvent a (112*n+1) (n-1) :=
    (lemma4SourceDualBandRead_crossing_iff n hn 1 A).mpr hA
  have hraw := rectangleBottomFrontierReveal_eq_raw_of_crossing a (112*n+1) (n-1) B hB
  have he' : e ∈ complementaryRevealPullback _ _
      (rectangleDualOriginalEdge (box (56*n)) a (112*n+1) (n-1))
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a (112*n+1) (n-1))
        (rectangleDualBottomPorts a (112*n+1) (n-1)) B) := by
    change e ∈ complementaryRevealPullback _ _ _
      (rectangleBottomFrontierReveal a (112*n+1) (n-1) B) at he
    rwa [hraw] at he
  apply complementary_raw_query_endpoint_index_of_closed_trace (box (56*n)) a
    (112*n+1) (n-1) A (rectangleDualBottomPorts a (112*n+1) (n-1)) P hclosed 0 _ e he'
  intro s hs
  have hsy : s.val.2=a.2-1 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
    rfl
  have has : a.2 = -3*(n:ℤ) := rfl
  apply rayIndex_zero_of_level (faceIndexMark s.val) P 0
  intro v hv
  have h := hlower v hv
  simp only [faceIndexMark,hsy,has]
  rw [ite_eq_right (by omega)]

/-- Both actual one-sided source queries avoid open index-one components. -/
theorem lemma4_source_band_queries_avoid_component
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4BandConstructionEvent n)
    {z : LatticeVertex} (P : PD.FK.squareLattice.Walk z z)
    (hclosed : finiteDualWalkClosed (box (56*n)) A P)
    (hstrip : ∀ v ∈ P.support, -3*(n:ℤ) ≤ v.2 ∧ v.2 ≤ 3*(n:ℤ)-1)
    (u : (box (56*n) : Set LatticeVertex))
    (hcomponent : ∀ v, ActualConnected _ A u v → rayIndex v.val P=1)
    (e : (lemma4AmbientGraph n).edgeSet) (he : e ∈ A)
    (hroot : ∃ v ∈ e.val, ActualConnected _ A u v) :
    e ∉ lemma4SourceBandReveal n 0 A ∪ lemma4SourceBandReveal n 1 A := by
  classical
  intro heR
  rcases Finset.mem_union.mp heR with heR | heR
  · exact lemma4_source_upper_query_avoids_core_component n hn A hA.2.1 P hclosed
      (fun v hv => (hstrip v hv).2) u hcomponent e he hroot heR
  · exact edge_not_query_of_component_index P A (lemma4SourceBandReveal n 1 A) 0 1 (by norm_num)
      (lemma4_source_lower_query_original_endpoint_zero n hn A hA.2.2 P hclosed
        (fun v hv => (hstrip v hv).1)) u hcomponent e he hroot heR

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
