module

public import PottsContinuity.PlanarMixed.Lemma4RecordCarrier.RawQueryOriginalIndex
public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.SourceBandStoppingRecords

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.FK.Medial PD.Duality Push RSW Exploration
noncomputable section

/-- On the crossing event, the top-frontier reveal `Exploration.rectangleTopFrontierReveal`
queries precisely the genuine raw upper exploration. -/
theorem rectangleTopFrontierReveal_eq_raw_of_crossing
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h) :
    Exploration.rectangleTopFrontierReveal a w h A=Push.rectangleTopReveal a w h A := by
  change extremalPathUpperRevealMap (Push.rectangleTopFrontierSelector a w h) Prod.fst A=_
  simp only [extremalPathUpperRevealMap,Push.rectangleTopFrontierSelector,ite_eq_left hA]

/-- Every actual upper-band query has an original endpoint outside a closed
source loop lying below its top seed marks. No selected-path premise occurs. -/
theorem lemma4_source_upper_query_original_endpoint_zero
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4DualBandEvent n 0)
    {z : LatticeVertex} (P : PD.FK.squareLattice.Walk z z)
    (hclosed : finiteDualWalkClosed (box (56*n)) A P)
    (hupper : ∀ v ∈ P.support, v.2 ≤ 3*(n:ℤ)-1)
    (e : (lemma4AmbientGraph n).edgeSet) (he : e ∈ lemma4SourceBandReveal n 0 A) :
    ∃ v ∈ e.val, rayIndex v.val P=0 := by
  let a := lemma4SourceBandBase n 0
  let B := lemma4SourceDualBandRead n 0 A
  have hB : B ∈ rectangleHorizontalCrossingEvent a (112*n+1) (n-1) :=
    (lemma4SourceDualBandRead_crossing_iff n hn 0 A).mpr hA
  have hraw := rectangleTopFrontierReveal_eq_raw_of_crossing a (112*n+1) (n-1) B hB
  have he' : e ∈ complementaryRevealPullback _ _
      (rectangleDualOriginalEdge (box (56*n)) a (112*n+1) (n-1))
      (Push.rectangleTopReveal a (112*n+1) (n-1) B) := by
    change e ∈ complementaryRevealPullback _ _ _
      (Exploration.rectangleTopFrontierReveal a (112*n+1) (n-1) B) at he
    rwa [hraw] at he
  apply complementary_raw_query_endpoint_index_of_closed_trace (box (56*n)) a
    (112*n+1) (n-1) A (rectangleDualTopPorts a (112*n+1) (n-1)) P hclosed 0 _ e he'
  intro s hs
  have hsy : s.val.2=a.2+((n-1:ℕ):ℤ) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hs
    rfl
  have hN : ((n-1:ℕ):ℤ)=(n:ℤ)-1 := by omega
  have has : a.2=2*(n:ℤ) := rfl
  apply rayIndex_zero_of_level (faceIndexMark s.val) P 1
  intro v hv
  have h := hupper v hv
  simp only [faceIndexMark,hsy,has,hN]
  rw [ite_eq_left (by omega)]

/-- The upper exploration cannot query an open edge in an index-one core
component. This assertion is independent of which crossing the exploration selects. -/
theorem lemma4_source_upper_query_avoids_core_component
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (lemma4AmbientGraph n))
    (hA : A ∈ lemma4DualBandEvent n 0)
    {z : LatticeVertex} (P : PD.FK.squareLattice.Walk z z)
    (hclosed : finiteDualWalkClosed (box (56*n)) A P)
    (hupper : ∀ v ∈ P.support, v.2 ≤ 3*(n:ℤ)-1)
    (u : (box (56*n) : Set LatticeVertex))
    (hcomponent : ∀ v, ActualConnected _ A u v → rayIndex v.val P=1)
    (e : (lemma4AmbientGraph n).edgeSet) (he : e ∈ A)
    (hroot : ∃ v ∈ e.val, ActualConnected _ A u v) :
    e ∉ lemma4SourceBandReveal n 0 A :=
  edge_not_query_of_component_index P A (lemma4SourceBandReveal n 0 A) 0 1 (by norm_num)
    (lemma4_source_upper_query_original_endpoint_zero n hn A hA P hclosed hupper)
    u hcomponent e he hroot

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
