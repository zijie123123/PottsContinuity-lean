module

public import PottsContinuity.PlanarMixed.Square.RectangleDualVerticalReflection
public import PottsContinuity.PlanarMixed.Lemma4StoppingRecords.ReflectedBottomReveal

@[expose] public section

namespace PottsContinuity.PlanarMixed.Lemma4Connectors
open PD.FK PD.Duality Push Square
noncomputable section
local instance routeSevenReflectOriginalFintype (a : LatticeVertex) (w h : ℕ) :
    Fintype (rectangleGraph a w h).edgeSet := Fintype.ofFinite _
local instance routeSevenReflectEdgeEq {V : Type*} (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _

/-- Complementing a sampled configuration commutes with both true reflections. -/
theorem rectangle_verticalReflection_auxiliary_closed
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h)) :
    configurationIso (rectangleDualGraphVerticalReflectionIso a w h)
      (auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv a w h) A) =
    auxiliaryClosedConfiguration (DualityExt.rectangleDualEdgeEquiv a w h)
      (configurationIso (rectangleGraphVerticalReflectionIso a w h) A) := by
  have hcomm := rectanglePrimalDualConfiguration_reflection_commute a w h A
  rw [auxiliaryClosedConfiguration_rectangle_eq,auxiliaryClosedConfiguration_rectangle_eq]
  convert! hcomm using 1

/-- Exact edge commutation is extracted from the complete complementary-state
identity, avoiding any duplicate reflected-bond construction. -/
theorem rectangle_verticalReflection_dual_edge_commutes
    (a : LatticeVertex) (w h : ℕ) (f : (rectangleGraph a w h).edgeSet) :
    configurationIsoEdgeEquiv (rectangleDualGraphVerticalReflectionIso a w h)
      (DualityExt.rectangleDualEdgeEquiv a w h f) =
    DualityExt.rectangleDualEdgeEquiv a w h
      (configurationIsoEdgeEquiv (rectangleGraphVerticalReflectionIso a w h) f) := by
  classical
  let e := DualityExt.rectangleDualEdgeEquiv a w h
  let P := configurationIsoEdgeEquiv (rectangleGraphVerticalReflectionIso a w h)
  let D := configurationIsoEdgeEquiv (rectangleDualGraphVerticalReflectionIso a w h)
  let A : Configuration (rectangleGraph a w h) := Finset.univ.erase f
  have hf : e f ∈ auxiliaryClosedConfiguration e A := by simp [A]
  have hd : D (e f) ∈ configurationIso (rectangleDualGraphVerticalReflectionIso a w h)
      (auxiliaryClosedConfiguration e A) := Finset.mem_map.mpr ⟨e f,hf,rfl⟩
  rw [rectangle_verticalReflection_auxiliary_closed] at hd
  rw [mem_auxiliaryClosedConfiguration] at hd
  have hn : P.symm (e.symm (D (e f))) ∉ A := by
    simpa only [configurationIso,Equiv.finsetCongr_apply,Finset.mem_map_equiv] using hd
  have heq : P.symm (e.symm (D (e f)))=f := by
    simpa only [A,Finset.mem_erase,Finset.mem_univ,and_true,not_not] using hn
  have hback : e.symm (D (e f))=P f := by
    simpa only [Equiv.apply_symm_apply] using congrArg P heq
  exact (e.apply_symm_apply (D (e f))).symm.trans (congrArg e hback)

/-- The true dual top ports reflect exactly to bottom ports, including corners. -/
theorem rectangle_verticalReflection_bottom_ports_map
    (a : LatticeVertex) (w h : ℕ) :
    (rectangleDualBottomPorts a w h).map
      (rectangleDualGraphVerticalReflectionIso a w h).toEquiv.toEmbedding =
      rectangleDualTopPorts a w h := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
    apply Finset.mem_image.mpr
    refine ⟨i,hi,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change a.2+(h:ℤ)=2*a.2+(h:ℤ)-1-(a.2-1)
      omega
  · intro hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_map.mpr ⟨rectangleDualBottomPortVertex a w h i,Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change 2*a.2+(h:ℤ)-1-(a.2-1)=a.2+(h:ℤ)
      omega

/-- The actual lower-port reached set is the reflection of the upper one. -/
theorem rectangle_verticalReflection_reached_iff
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (u : RectangleDualVertex a w h) :
    rectangleDualGraphVerticalReflectionIso a w h u ∈ closedClusterReached
      (DualityExt.rectangleDualEdgeEquiv a w h) (rectangleDualTopPorts a w h)
        (configurationIso (rectangleGraphVerticalReflectionIso a w h) A) ↔
    u ∈ closedClusterReached (DualityExt.rectangleDualEdgeEquiv a w h)
      (rectangleDualBottomPorts a w h) A := by
  classical
  let e := DualityExt.rectangleDualEdgeEquiv a w h
  let D := rectangleDualGraphVerticalReflectionIso a w h
  change (∃ t ∈ rectangleDualTopPorts a w h,
    ActualConnected _ (auxiliaryClosedConfiguration e (configurationIso (rectangleGraphVerticalReflectionIso a w h) A)) t (D u)) ↔
    ∃ s ∈ rectangleDualBottomPorts a w h, ActualConnected _ (auxiliaryClosedConfiguration e A) s u
  rw [← rectangle_verticalReflection_bottom_ports_map,← rectangle_verticalReflection_auxiliary_closed]
  constructor
  · rintro ⟨t,ht,hconn⟩
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp ht
    exact ⟨s,hs,(actualConnected_configurationIso D (auxiliaryClosedConfiguration e A) s u).mp hconn⟩
  · rintro ⟨s,hs,hconn⟩
    exact ⟨D s,Finset.mem_map.mpr ⟨s,hs,rfl⟩,
      (actualConnected_configurationIso D (auxiliaryClosedConfiguration e A) s u).mpr hconn⟩

/-- Every queried bond, open or closed, transports with the original reflection. -/
theorem rectangle_verticalReflection_closedReveal_map
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h)) :
    configurationIso (rectangleGraphVerticalReflectionIso a w h)
      (closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) (rectangleDualBottomPorts a w h) A) =
    closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h)
      (rectangleDualTopPorts a w h) (configurationIso (rectangleGraphVerticalReflectionIso a w h) A) := by
  classical
  let e := DualityExt.rectangleDualEdgeEquiv a w h
  let P := configurationIsoEdgeEquiv (rectangleGraphVerticalReflectionIso a w h)
  let D := rectangleDualGraphVerticalReflectionIso a w h
  have hpair (f : (rectangleGraph a w h).edgeSet) :
      Sym2.map D (e f).val=(e (P f)).val := by
    exact congrArg Subtype.val (rectangle_verticalReflection_dual_edge_commutes a w h f)
  ext f
  obtain ⟨g,rfl⟩ := P.surjective f
  have hl : P g ∈ configurationIso (rectangleGraphVerticalReflectionIso a w h)
      (closedClusterReveal e (rectangleDualBottomPorts a w h) A) ↔
      g ∈ closedClusterReveal e (rectangleDualBottomPorts a w h) A := by
    change P g ∈ (closedClusterReveal e (rectangleDualBottomPorts a w h) A).map P.toEmbedding ↔ _
    simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]
  rw [hl,mem_closedClusterReveal_iff_endpoint,mem_closedClusterReveal_iff_endpoint]
  constructor
  · rintro ⟨u,hu,hreach⟩
    refine ⟨D u,?_,(rectangle_verticalReflection_reached_iff a w h A u).mpr hreach⟩
    rw [← hpair g]
    exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
  · rintro ⟨v,hv,hreach⟩
    rw [← hpair g] at hv
    obtain ⟨u,hu,rfl⟩ := Sym2.mem_map.mp hv
    exact ⟨u,hu,(rectangle_verticalReflection_reached_iff a w h A u).mp hreach⟩

/-- The reflected success reveal is the direct bottom-port query, with
all queried open and closed chords retained in the record. -/
theorem rectangleBottomFrontierReveal_eq_raw_of_crossing
    (a : LatticeVertex) (w h : ℕ) (A : Configuration (rectangleGraph a w h))
    (hA : A ∈ rectangleHorizontalCrossingEvent a w h) :
    rectangleBottomFrontierReveal a w h A =
      closedClusterReveal (DualityExt.rectangleDualEdgeEquiv a w h) (rectangleDualBottomPorts a w h) A := by
  let P := rectangleGraphVerticalReflectionIso a w h
  have hsymm (C : Configuration (rectangleGraph a w h)) :
      (configurationIso P).symm C=configurationIso P C := by rfl
  have hcross : (configurationIso P).symm A ∈ rectangleHorizontalCrossingEvent a w h := by
    have hc := horizontalCrossing_verticalReflection_iff a w h ((configurationIso P).symm A)
    apply hc.mp
    change configurationIso P ((configurationIso P).symm A) ∈ _
    simpa only [Equiv.apply_symm_apply] using hA
  have hraw : Exploration.rectangleTopFrontierReveal a w h ((configurationIso P).symm A)=
      Push.rectangleTopReveal a w h ((configurationIso P).symm A) := by
    change Exploration.extremalPathUpperRevealMap (Push.rectangleTopFrontierSelector a w h) Prod.fst _=_
    simp only [Exploration.extremalPathUpperRevealMap,Push.rectangleTopFrontierSelector,ite_eq_left hcross]
  change configurationIso P (Exploration.rectangleTopFrontierReveal a w h ((configurationIso P).symm A))=_
  rw [hraw]
  have hm := rectangle_verticalReflection_closedReveal_map a w h A
  apply (configurationIso P).injective
  rw [← hsymm,Equiv.symm_apply_apply]
  simpa only [hsymm] using hm.symm

end
end PottsContinuity.PlanarMixed.Lemma4Connectors
