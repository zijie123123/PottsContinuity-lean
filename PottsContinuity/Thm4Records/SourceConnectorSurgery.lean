module

public import PottsContinuity.Thm4Records.CentralTraceSegment
public import PottsContinuity.Thm4Records.CentralFaceFreshness
public import PottsContinuity.Thm4Records.AuxiliarySourceWalk
public import PottsContinuity.Thm4Records.AuxiliaryCrossing

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK PD.Duality Exploration Push RSW Thm4Plane
noncomputable section
local instance sourceConnectorSurgeryEdgeEq (m : ℕ) :
    DecidableEq (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet := Classical.decEq _

/-- An auxiliary crossing on the actual residual square gives the unchanged
source connector. Every step of the extracted middle segment is unqueried;
full source screens are used throughout, including all folds and excursions. -/
theorem connectorAuxiliaryCrossing_implies_sourceConnector (m : ℕ) (hm : 1 ≤ m)
    (X Y : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hrecord : Y ∈ revealRecordEvent (connectorReveal m hm) X)
    (hleft : Y ∈ FKC.FiniteFK.slitScreenLeftCrossingEvent m)
    (hright : Y ∈ FKC.FiniteFK.slitScreenRightCrossingEvent m)
    (haux : (configurationSplitEquiv _ (connectorReveal m hm X) Y).1 ∈
      connectorAuxiliaryCrossing m hm (connectorReveal m hm X)) :
    Y ∈ slitScreenConnectorEvent m := by
  classical
  let U := (configurationSplitEquiv _ (connectorReveal m hm X) Y).1
  obtain ⟨a,b,p,ha,hb,hp⟩ := connectorAuxiliaryCrossing_source_walk m hm _ U haux
  rw [FKC.FiniteFK.slitScreenLeftCrossingEvent_eq_actualClosedDual m hm] at hleft
  rw [FKC.FiniteFK.slitScreenRightCrossingEvent_eq_actualClosedDual m hm] at hright
  obtain ⟨lb,hlb,lt,hlt,⟨pL⟩⟩ := hleft
  obtain ⟨rb,hrb,rt,hrt,⟨pR⟩⟩ := hright
  let PL := sourceScreenIndexWalk m Y (sideFaceBases m false) pL
  let PR := sourceScreenIndexWalk m Y (sideFaceBases m true) pR
  let P := sourceScreenIndexWalk m U.val (FKC.FiniteFK.slitScreenMiddleFaceBases m) p
  have hLsupport := sourceScreenIndexWalk_support m Y (sideFaceBases m false) pL
  have hRsupport := sourceScreenIndexWalk_support m Y (sideFaceBases m true) pR
  have hPsupport := sourceScreenIndexWalk_support m U.val _ p
  have hLbase := PlanarTopology.slitScreen_actual_walk_support (16*m) Y _ pL hlb.1
  have hRbase := PlanarTopology.slitScreen_actual_walk_support (16*m) Y _ pR hrb.1
  have hLbounds : ∀ z ∈ PL.support,
      -(5*(m:ℤ)) ≤ z.1 ∧ z.1 ≤ -(m:ℤ)-1 ∧
      -(16*(m:ℤ))-1 ≤ z.2 ∧ z.2 ≤ 16*(m:ℤ) := by
    intro z hz
    have hc := hLbase z (hLsupport ▸ hz)
    simpa only [FKC.FiniteFK.slitScreenLeftFaceBases,Finset.mem_product,Finset.mem_Icc,and_assoc] using hc
  have hRbounds : ∀ z ∈ PR.support,
      (m:ℤ) ≤ z.1 ∧ z.1 ≤ 5*(m:ℤ)-1 ∧
      -(16*(m:ℤ))-1 ≤ z.2 ∧ z.2 ≤ 16*(m:ℤ) := by
    intro z hz
    have hc := hRbase z (hRsupport ▸ hz)
    simpa only [FKC.FiniteFK.slitScreenRightFaceBases,Finset.mem_product,Finset.mem_Icc,and_assoc] using hc
  have hPbounds : ∀ z ∈ P.support,
      -(5*(m:ℤ)) ≤ z.1 ∧ z.1 ≤ 5*(m:ℤ)-1 ∧
      -(12*(m:ℤ)) ≤ z.2 ∧ z.2 ≤ -(2*(m:ℤ))-1 := by
    intro z hz
    have hc := hp z (hPsupport ▸ hz)
    simpa only [FKC.FiniteFK.slitScreenMiddleFaceBases,Finset.mem_product,Finset.mem_Icc,and_assoc] using hc
  obtain ⟨u,hu,v,hv,q,hqs,hqe,hcentral⟩ := crossing_full_screens_central_segment m hm PL PR P
    hLbounds hRbounds hlb.2 hlt.2 hrb.2 hrt.2 hPbounds ha hb
  have hqActual : ∀ x y, s(x,y) ∈ q.edges →
      (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m Y
        (FKC.FiniteFK.slitScreenMiddleFaceBases m)).Adj x y := by
    intro x y hxy
    have hxyP : s(x,y) ∈ p.edges :=
      sourceScreenIndexWalk_edges m U.val _ p ▸ hqe hxy
    have hxyAux : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m U.val
        (FKC.FiniteFK.slitScreenMiddleFaceBases m)).Adj x y :=
      (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m U.val
        (FKC.FiniteFK.slitScreenMiddleFaceBases m)).mem_edgeSet.mp (p.edges_subset_edgeSet hxyP)
    obtain ⟨d,e,hcross,hclosed,hdir,hxF,hyF⟩ := hxyAux
    obtain ⟨z,hz,hzL,hzR,hidxL,hidxR⟩ := hcentral x y hxy
    have hd : d.source ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m ∧
        d.target ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m := by
      rcases hdir with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨hxF,hyF⟩
      · exact ⟨hyF,hxF⟩
    have hzD : z ∈ d.toSym2 := by
      rcases hz with rfl | rfl <;>
        rcases hdir with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        simp [FKC.Medial.LatticeBond.toSym2]
    have hnotY : e ∉ connectorReveal m hm Y :=
      centralFace_crossedBond_unqueried m hm Y pL pR hlb.1 hrb.1 hlb.2 hlt.2 hrb.2 hrt.2
        d e hcross hd z hzD
        (fun h => hzL (hLsupport.symm ▸ h)) (fun h => hzR (hRsupport.symm ▸ h)) hidxL hidxR
    have hnotX : e ∉ connectorReveal m hm X := by
      rw [← hrecord.1]
      exact hnotY
    have heY : e ∉ Y := by
      intro heY
      apply hclosed
      change e ∈ Y \ connectorReveal m hm X
      exact Finset.mem_sdiff.mpr ⟨heY,hnotX⟩
    exact ⟨d,e,hcross,heY,hdir,hxF,hyF⟩
  have hu' : u ∈ pL.support := hLsupport ▸ hu
  have hv' : v ∈ pR.support := hRsupport ▸ hv
  obtain ⟨u',hu',v',hv',hconn⟩ := actual_connection_of_full_trace_segment
    {z | z ∈ pL.support} {z | z ∈ pR.support} q hu' hv' hqActual
  exact ⟨lb,hlb,lt,hlt,pL,rb,hrb,rt,hrt,pR,u',v',hu',hv',hconn⟩

/-- D-prime on the actual original stopping records, without an interface
premise or any assumption on a selected square crop. -/
theorem sourceConnectorSurgery (m : ℕ) (hm : 1 ≤ m) : SourceConnectorSurgery m hm := by
  classical
  unfold SourceConnectorSurgery
  intro X hX Y hY hnon
  have hs : Y ∈ connectorSourceEvent m :=
    (connectorSourceEvent_readFrom_connectorReveal m hm X Y hY).mpr hX
  let U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X) :=
    (configurationSplitEquiv _ (connectorReveal m hm X) Y).1
  change U ∈ connectorRemainingNoncrossing m hm X at hnon
  have haux : U ∈ connectorAuxiliaryCrossing m hm (connectorReveal m hm X) :=
    connectorRemainingNoncrossing_implies_auxiliaryCrossing m hm X U hnon
  exact connectorAuxiliaryCrossing_implies_sourceConnector m hm X Y hY hs.2.1 hs.2.2 haux

end
end PottsContinuity.Thm4Records
