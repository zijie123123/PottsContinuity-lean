module

public import PottsContinuity.Thm4Records.NativeIncidentConnectivity
public import PottsContinuity.Thm4Records.SideRectangle

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section

/-- Transpose the original primal core so that bottom/top become left/right. -/
def connectorCutCoreBase (m : ℕ) : ℤ × ℤ := (-(12*(m:ℤ)),-(5*(m:ℤ))+1)
abbrev ConnectorCutCoreVertex (m : ℕ) :=
  RectangleVertex (connectorCutCoreBase m) (10*m) (10*m-2)

def connectorCutCoreSourceVertex (m : ℕ) (hm : 1 ≤ m)
    (v : ConnectorCutCoreVertex m) : FKC.FiniteFK.SlitBoxVertex (16*m) := by
  refine ⟨v.val.swap,?_⟩
  have hv := (PD.FK.mem_latticeRectangle _ _ _ _).mp v.property
  rw [FKC.mem_latticeRectangle]
  dsimp [connectorCutCoreBase] at hv ⊢
  constructor <;> constructor <;> omega

theorem connectorCutCoreSource_adj (m : ℕ) (hm : 1 ≤ m)
    (u v : ConnectorCutCoreVertex m)
    (huv : (rectangleGraph (connectorCutCoreBase m) (10*m) (10*m-2)).Adj u v) :
    (FKC.FiniteFK.slitBoxGraph (16*m)).Adj (connectorCutCoreSourceVertex m hm u)
      (connectorCutCoreSourceVertex m hm v) := by
  have hstep := (PD.FK.squareLattice_adj_iff _ _).mp
    ((PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mp huv)
  apply (FKC.FiniteFK.slitBoxGraph_adj_iff _ _ _).mpr
  constructor
  · apply (FKC.squareLattice_adj_iff _ _).mpr
    change ((u.val.2+1=v.val.2 ∨ v.val.2+1=u.val.2) ∧ u.val.1=v.val.1) ∨
      (u.val.2=v.val.2 ∧ (u.val.1+1=v.val.1 ∨ v.val.1+1=u.val.1))
    tauto
  · intro h
    have hc := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
    have hy := h.1.2.1
    change 0 ≤ u.val.1 at hy
    dsimp [connectorCutCoreBase] at hc
    omega

/-- A remaining open state is an actual open bond of the native graph. -/
theorem remaining_open_edge_native_adj (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet) (he : e ∈ U.val)
    (u v : FKC.FiniteFK.SlitBoxVertex (16*m)) (heq : e.val=s(u,v)) :
    (openGraph (connectorNativeGraph m hm X)
      ((edgeRestrictionConfigurationEquiv _ (connectorReveal m hm X)).symm U)).Adj u v := by
  classical
  let C := (edgeRestrictionConfigurationEquiv _ (connectorReveal m hm X)).symm U
  have hmap : e ∈ C.map (edgeRestrictionEdgeEmbedding _ (connectorReveal m hm X)) := by
    rw [← edgeRestrictionConfigurationEquiv_val,Equiv.apply_symm_apply]
    exact he
  obtain ⟨d,hd,hde⟩ := Finset.mem_map.mp hmap
  apply (openGraph_adj _ _ _ _).mpr
  refine ⟨d,hd,?_⟩
  exact (congrArg Subtype.val hde).trans heq

def connectorCoreCutLabel (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (v : ConnectorCutCoreVertex m) : Bool := by
  classical
  exact decide (connectorCutCoreSourceVertex m hm v ∈ connectorBottomCluster m hm X U)

theorem connectorCoreCutLabel_boundary (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (hnon : U ∈ connectorRemainingNoncrossing m hm X) :
    (∀ v : ConnectorCutCoreVertex m, v.val.1=(connectorCutCoreBase m).1 →
      connectorCoreCutLabel m hm X U v=true) ∧
    (∀ v : ConnectorCutCoreVertex m, v.val.1=(connectorCutCoreBase m).1+((10*m:ℕ):ℤ) →
      connectorCoreCutLabel m hm X U v=false) := by
  classical
  constructor
  · intro v hv
    have hc := connectorBottomCluster_contains_bottom m hm X U
      (connectorCutCoreSourceVertex m hm v) hv
    simp [connectorCoreCutLabel,hc]
  · intro v hv
    have hy : (connectorCutCoreSourceVertex m hm v).val.2=-(2*(m:ℤ)) := by
      change v.val.1=-(2*(m:ℤ))
      dsimp [connectorCutCoreBase] at hv
      omega
    have hc := connectorBottomCluster_avoids_top_of_noncrossing m hm X U hnon
      (connectorCutCoreSourceVertex m hm v) hy
    simp [connectorCoreCutLabel,hc]

abbrev ConnectorCutDualVertex (m : ℕ) :=
  RectangleDualVertex (connectorCutCoreBase m) (10*m) (10*m-2)

def connectorCutRStarVertex (m : ℕ) (_hm : 1 ≤ m) (u : ConnectorCutDualVertex m) :
    SlitRStarVertex m := by
  classical
  exact if h : u.val.swap ∈ PD.FK.latticeRectangle (slitScreenRStarBase m)
      (slitScreenRStarSide m) (slitScreenRStarSide m) then ⟨u.val.swap,h⟩
    else ⟨slitScreenRStarBase m,by
      rw [PD.FK.mem_latticeRectangle]; constructor <;> constructor <;> omega⟩

private theorem cutDual_endpoint_mem_rStar (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (hnon : U ∈ connectorRemainingNoncrossing m hm X)
    (u v : ConnectorCutDualVertex m)
    (huv : (rectangleLabelCutDualGraph (connectorCutCoreBase m) (10*m) (10*m-2)
      (connectorCoreCutLabel m hm X U)).Adj u v) :
    u.val.swap ∈ PD.FK.latticeRectangle (slitScreenRStarBase m)
      (slitScreenRStarSide m) (slitScreenRStarSide m) := by
  have hb := connectorCoreCutLabel_boundary m hm X U hnon
  have hleft : u.val.1 ≠ (connectorCutCoreBase m).1-1 := by
    intro h
    exact rectangleDualLeftColumn_isolated _ _ _ _ hb.1 u h v huv
  have hright : u.val.1 ≠ (connectorCutCoreBase m).1+((10*m:ℕ):ℤ) := by
    intro h
    exact rectangleDualRightColumn_isolated _ _ _ _ hb.2 u h v huv
  have hc := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  rw [PD.FK.mem_latticeRectangle]
  dsimp [connectorCutCoreBase,slitScreenRStarBase,slitScreenRStarSide] at hc hleft hright ⊢
  constructor <;> constructor <;> omega

/-- Swap a normalized primal bond while keeping its true original endpoints. -/
def connectorTransposePrimalBond (b : PD.FK.Medial.LatticeBond) : FKC.Medial.LatticeBond :=
  match b.axis with
  | .horizontal => ⟨b.base.swap,.vertical⟩
  | .vertical => ⟨b.base.swap,.horizontal⟩

private theorem transposePrimal_source (b : PD.FK.Medial.LatticeBond) :
    (connectorTransposePrimalBond b).source=b.source.swap := by
  rcases b with ⟨base,a⟩
  cases a <;> rfl
private theorem transposePrimal_target (b : PD.FK.Medial.LatticeBond) :
    (connectorTransposePrimalBond b).target=b.target.swap := by
  rcases b with ⟨base,a⟩
  cases a <;> rfl
private theorem transposeDual_source (b : PD.FK.Medial.LatticeBond) :
    (FKC.Medial.dualBondOfPrimal (connectorTransposePrimalBond b)).source=(b.faceBase false).swap := by
  rcases b with ⟨base,a⟩
  cases a <;> rfl
private theorem transposeDual_target (b : PD.FK.Medial.LatticeBond) :
    (FKC.Medial.dualBondOfPrimal (connectorTransposePrimalBond b)).target=(b.faceBase true).swap := by
  rcases b with ⟨⟨bx,byy⟩,a⟩
  cases a <;> simp [connectorTransposePrimalBond,FKC.Medial.dualBondOfPrimal,
    FKC.Medial.LatticeBond.target,PD.FK.Medial.LatticeBond.faceBase]

/-- Every core cut step is an auxiliary-open R* bond: its crossed original
state is absent from the remaining primal configuration. -/
theorem connectorCoreCut_auxiliary_adj (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (hnon : U ∈ connectorRemainingNoncrossing m hm X)
    (u v : ConnectorCutDualVertex m)
    (huv : (rectangleLabelCutDualGraph (connectorCutCoreBase m) (10*m) (10*m-2)
      (connectorCoreCutLabel m hm X U)).Adj u v) :
    (openGraph (SlitRStarGraph m) (connectorAuxiliaryDual m hm (connectorReveal m hm X) U)).Adj
      (connectorCutRStarVertex m hm u) (connectorCutRStarVertex m hm v) := by
  classical
  obtain ⟨b,hs,ht,hdiff,hdir⟩ := (rectangleLabelCutDual_adj_iff_bond _ _ _ _ _ _).mp huv
  let x : ConnectorCutCoreVertex m := ⟨b.source,hs⟩
  let y : ConnectorCutCoreVertex m := ⟨b.target,ht⟩
  have hxy : (rectangleGraph (connectorCutCoreBase m) (10*m) (10*m-2)).Adj x y :=
    (PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mpr b.adjacent
  have hsource := connectorCutCoreSource_adj m hm x y hxy
  let e : (FKC.FiniteFK.slitBoxGraph (16*m)).edgeSet :=
    ⟨s(connectorCutCoreSourceVertex m hm x,connectorCutCoreSourceVertex m hm y),
      (FKC.FiniteFK.slitBoxGraph (16*m)).mem_edgeSet.mpr hsource⟩
  have he : e ∉ U.val := by
    intro he
    have hopen := remaining_open_edge_native_adj m hm X U e he
      (connectorCutCoreSourceVertex m hm x) (connectorCutCoreSourceVertex m hm y) rfl
    have hlabels : (connectorCutCoreSourceVertex m hm x ∈ connectorBottomCluster m hm X U) ↔
        (connectorCutCoreSourceVertex m hm y ∈ connectorBottomCluster m hm X U) := by
      constructor
      · rintro ⟨s,hs,hconn⟩
        exact ⟨s,hs,hconn.trans hopen.reachable⟩
      · rintro ⟨s,hs,hconn⟩
        exact ⟨s,hs,hconn.trans hopen.reachable.symm⟩
    change connectorCoreCutLabel m hm X U x != connectorCoreCutLabel m hm X U y at hdiff
    simp [connectorCoreCutLabel,hlabels] at hdiff
  have hu : (connectorCutRStarVertex m hm u).val=u.val.swap := by
    simp [connectorCutRStarVertex,cutDual_endpoint_mem_rStar m hm X U hnon u v huv]
  have hv : (connectorCutRStarVertex m hm v).val=v.val.swap := by
    simp [connectorCutRStarVertex,cutDual_endpoint_mem_rStar m hm X U hnon v u huv.symm]
  let c := connectorTransposePrimalBond b
  let d := FKC.Medial.dualBondOfPrimal c
  have hp : d.toSym2=s(u.val.swap,v.val.swap) := by
    change s(d.source,d.target)=_
    rw [transposeDual_source,transposeDual_target]
    rcases hdir with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · rw [h1,h2]
    · rw [h1,h2,Sym2.eq_swap]
  have hstar : (SlitRStarGraph m).Adj (connectorCutRStarVertex m hm u) (connectorCutRStarVertex m hm v) := by
    apply (PD.FK.rectangleGraph_adj_iff _ _ _ _ _).mpr
    apply PD.FK.squareLattice.mem_edgeSet.mp
    rw [hu,hv,← hp]
    exact (FKC.squareLattice_adj_iff _ _).mp d.adjacent |>
      (PD.FK.squareLattice_adj_iff _ _).mpr |>
      PD.FK.squareLattice.mem_edgeSet.mpr
  let f : (SlitRStarGraph m).edgeSet :=
    ⟨s(connectorCutRStarVertex m hm u,connectorCutRStarVertex m hm v),(SlitRStarGraph m).mem_edgeSet.mpr hstar⟩
  have hd : (slitRStarEdgeBridge m hm f).dualBond=d := by
    apply FKC.Medial.LatticeBond.toSym2_injective
    rw [(slitRStarEdgeBridge m hm f).pairEq]
    change s((connectorCutRStarVertex m hm u).val,(connectorCutRStarVertex m hm v).val)=d.toSym2
    rw [hu,hv,hp]
  have hbridge : (slitRStarEdgeBridge m hm f).primalEdge=e := by
    apply (FKC.FiniteFK.slitBoxEdgeEmbedding (16*m)).injective
    rw [← (slitRStarEdgeBridge m hm f).crosses,hd]
    rw [show FKC.Medial.primalBondOfDual d=c from FKC.Medial.primalBondOfDual_dualBondOfPrimal c]
    apply Subtype.ext
    change c.toSym2=s(b.source.swap,b.target.swap)
    exact congrArg₂ Sym2.mk (transposePrimal_source b) (transposePrimal_target b)
  apply (openGraph_adj _ _ _ _).mpr
  refine ⟨f,?_,rfl⟩
  exact (mem_connectorAuxiliaryDual m hm (connectorReveal m hm X) U f).mpr
    (by rw [hbridge]; exact he)


/-- The full cut maps into auxiliary R* connectivity using only residual reads. -/
def connectorCoreCutToAuxiliary (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (hnon : U ∈ connectorRemainingNoncrossing m hm X) :
    rectangleLabelCutDualGraph (connectorCutCoreBase m) (10*m) (10*m-2)
      (connectorCoreCutLabel m hm X U) →g
      openGraph (SlitRStarGraph m) (connectorAuxiliaryDual m hm (connectorReveal m hm X) U) where
  toFun := connectorCutRStarVertex m hm
  map_rel' := by
    intro u v huv
    exact connectorCoreCut_auxiliary_adj m hm X U hnon u v huv

private theorem connectorCutBottomPort_maps_left (m : ℕ) (hm : 1 ≤ m)
    (u : ConnectorCutDualVertex m)
    (hu : u ∈ rectangleDualBottomPorts (connectorCutCoreBase m) (10*m) (10*m-2)) :
    (connectorCutRStarVertex m hm u).val.1=-(5*(m:ℤ)) := by
  classical
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  have hi' : i < 10*m := Finset.mem_range.mp hi
  have hmem : (rectangleDualBottomPortVertex (connectorCutCoreBase m) (10*m) (10*m-2) i).val.swap ∈
      PD.FK.latticeRectangle (slitScreenRStarBase m) (slitScreenRStarSide m) (slitScreenRStarSide m) := by
    rw [PD.FK.mem_latticeRectangle]
    simp only [rectangleDualBottomPortVertex,Nat.min_eq_left (Nat.le_of_lt hi')]
    dsimp [connectorCutCoreBase,slitScreenRStarBase,slitScreenRStarSide]
    constructor <;> constructor <;> omega
  simp only [connectorCutRStarVertex,dite_eq_left hmem]
  dsimp [rectangleDualBottomPortVertex,connectorCutCoreBase]
  omega

private theorem connectorCutTopPort_maps_right (m : ℕ) (hm : 1 ≤ m)
    (u : ConnectorCutDualVertex m)
    (hu : u ∈ rectangleDualTopPorts (connectorCutCoreBase m) (10*m) (10*m-2)) :
    (connectorCutRStarVertex m hm u).val.1=5*(m:ℤ)-1 := by
  classical
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  have hi' : i < 10*m := Finset.mem_range.mp hi
  have hmem : (rectangleDualTopPortVertex (connectorCutCoreBase m) (10*m) (10*m-2) i).val.swap ∈
      PD.FK.latticeRectangle (slitScreenRStarBase m) (slitScreenRStarSide m) (slitScreenRStarSide m) := by
    rw [PD.FK.mem_latticeRectangle]
    simp only [rectangleDualTopPortVertex,Nat.min_eq_left (Nat.le_of_lt hi')]
    dsimp [connectorCutCoreBase,slitScreenRStarBase,slitScreenRStarSide]
    constructor <;> constructor <;> omega
  simp only [connectorCutRStarVertex,dite_eq_left hmem]
  dsimp [rectangleDualTopPortVertex,connectorCutCoreBase]
  omega

/-- Native primal no-crossing supplies the auxiliary dual LR crossing of
EXACTLY R*, with every queried original bond dual-open. -/
theorem connectorRemainingNoncrossing_implies_auxiliaryCrossing
    (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) (connectorReveal m hm X))
    (hnon : U ∈ connectorRemainingNoncrossing m hm X) :
    U ∈ connectorAuxiliaryCrossing m hm (connectorReveal m hm X) := by
  have hb := connectorCoreCutLabel_boundary m hm X U hnon
  obtain ⟨b,hb,t,ht,hconn⟩ := rectangleLabelCutDual_bottom_top_reachable
    (connectorCutCoreBase m) (10*m) (10*m-2) (connectorCoreCutLabel m hm X U) hb.1 hb.2
  exact ⟨connectorCutRStarVertex m hm b,connectorCutRStarVertex m hm t,
    connectorCutBottomPort_maps_left m hm b hb,connectorCutTopPort_maps_right m hm t ht,
    hconn.map (connectorCoreCutToAuxiliary m hm X U hnon)⟩

end
end PottsContinuity.Thm4Records
