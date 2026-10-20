module

public import PottsContinuity.Thm4Records.SideRectangle
public import PottsContinuity.Thm4Records.LatticeBondBridge

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW
noncomputable section

abbrev sideFaceBases (m : ℕ) (right : Bool) :=
  if right then FKC.FiniteFK.slitScreenRightFaceBases m else FKC.FiniteFK.slitScreenLeftFaceBases m

/-- Constant side labels exclude the two spurious outer dual columns. -/
theorem sideCutDual_endpoint_mem_faceBases (m : ℕ) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hno : X ∉ sidePrimalConnectionEvent m right)
    (u v : RectangleDualVertex (sideRectangleBase m right) (4*m) (32*m))
    (huv : (rectangleLabelCutDualGraph (sideRectangleBase m right) (4*m) (32*m)
      (sideRectangleCutLabel m right X)).Adj u v) : u.val ∈ sideFaceBases m right := by
  have hb := sideRectangleCutLabel_boundary_of_no_primal_connection m right X hno
  have hleft : u.val.1 ≠ (sideRectangleBase m right).1-1 := by
    intro h
    exact rectangleDualLeftColumn_isolated _ _ _ _ hb.1 u h v huv
  have hright : u.val.1 ≠ (sideRectangleBase m right).1+((4*m:ℕ):ℤ) := by
    intro h
    exact rectangleDualRightColumn_isolated _ _ _ _ hb.2 u h v huv
  have hc := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  cases right <;>
    simp only [sideFaceBases,Bool.false_eq_true,ite_false,ite_true,
      FKC.FiniteFK.slitScreenRightFaceBases,FKC.FiniteFK.slitScreenLeftFaceBases,
      Finset.mem_product,Finset.mem_Icc] <;>
    dsimp [sideRectangleBase,rectangleDualExpanded] at hc hleft hright <;>
    constructor <;> constructor <;> omega

/-- Every full cut-dual step is a genuinely closed original source bond.
No crop or freshness premise is used. -/
theorem sideCutDual_actual_source_adj (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hno : X ∉ sidePrimalConnectionEvent m right)
    (u v : RectangleDualVertex (sideRectangleBase m right) (4*m) (32*m))
    (huv : (rectangleLabelCutDualGraph (sideRectangleBase m right) (4*m) (32*m)
      (sideRectangleCutLabel m right X)).Adj u v) :
    (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m X (sideFaceBases m right)).Adj
      u.val v.val := by
  obtain ⟨b,hs,ht,hdiff,hdir⟩ := (rectangleLabelCutDual_adj_iff_bond _ _ _ _ _ _).mp huv
  obtain ⟨e,hepair,_,heclosed⟩ := sideRectangleCut_bond_queried_closed m hm right X b hs ht hdiff
  let bF := latticeBondEquiv.symm b
  let d := FKC.Medial.dualBondOfPrimal bF
  have hbs : bF.source=b.source := by
    rcases b with ⟨base,a⟩
    cases a <;> rfl
  have hbt : bF.target=b.target := by
    rcases b with ⟨base,a⟩
    cases a <;> rfl
  have hds : d.source=b.faceBase false := by
    rcases b with ⟨base,a⟩
    cases a <;> rfl
  have hdt : d.target=b.faceBase true := by
    rcases b with ⟨base,a⟩
    cases a <;> simp [d,bF,latticeBondEquiv,latticeAxisEquiv,
      FKC.Medial.dualBondOfPrimal,FKC.Medial.LatticeBond.target,
      PD.FK.Medial.LatticeBond.faceBase]
  refine ⟨d,e,?_,heclosed,?_,
    sideCutDual_endpoint_mem_faceBases m right X hno u v huv,
    sideCutDual_endpoint_mem_faceBases m right X hno v u huv.symm⟩
  · apply Subtype.ext
    rw [show FKC.Medial.primalBondOfDual d=bF from
      FKC.Medial.primalBondOfDual_dualBondOfPrimal bF]
    change bF.toSym2=Sym2.map Subtype.val e.val
    rw [hepair]
    change s(bF.source,bF.target)=s(b.source,b.target)
    rw [hbs,hbt]
  · simpa only [hds,hdt] using hdir

/-- Full source closed-dual paths are obtained by a literal coordinate map. -/
def sideCutDualToActualSource (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hno : X ∉ sidePrimalConnectionEvent m right) :
    rectangleLabelCutDualGraph (sideRectangleBase m right) (4*m) (32*m)
      (sideRectangleCutLabel m right X) →g
    FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m X (sideFaceBases m right) where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    exact sideCutDual_actual_source_adj m hm right X hno u v huv

private theorem sideBottomPort_terminal (m : ℕ) (right : Bool)
    (u : RectangleDualVertex (sideRectangleBase m right) (4*m) (32*m))
    (hu : u ∈ rectangleDualBottomPorts (sideRectangleBase m right) (4*m) (32*m)) :
    u.val ∈ FKC.FiniteFK.slitScreenBottomTerminals m (sideFaceBases m right) := by
  classical
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  have hi' : i < 4*m := Finset.mem_range.mp hi
  cases right <;>
    simp only [FKC.FiniteFK.slitScreenBottomTerminals,
      sideFaceBases,Bool.false_eq_true,ite_false,ite_true,
      FKC.FiniteFK.slitScreenRightFaceBases,FKC.FiniteFK.slitScreenLeftFaceBases,
      Finset.mem_product,Finset.mem_Icc,rectangleDualBottomPortVertex,
      Nat.min_eq_left (Nat.le_of_lt hi')] <;>
    dsimp [sideRectangleBase] <;> constructor <;> (try constructor) <;> (try constructor) <;> omega

private theorem sideTopPort_terminal (m : ℕ) (right : Bool)
    (u : RectangleDualVertex (sideRectangleBase m right) (4*m) (32*m))
    (hu : u ∈ rectangleDualTopPorts (sideRectangleBase m right) (4*m) (32*m)) :
    u.val ∈ FKC.FiniteFK.slitScreenTopTerminals m (sideFaceBases m right) := by
  classical
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hu
  have hi' : i < 4*m := Finset.mem_range.mp hi
  cases right <;>
    simp only [FKC.FiniteFK.slitScreenTopTerminals,
      sideFaceBases,Bool.false_eq_true,ite_false,ite_true,
      FKC.FiniteFK.slitScreenRightFaceBases,FKC.FiniteFK.slitScreenLeftFaceBases,
      Finset.mem_product,Finset.mem_Icc,rectangleDualTopPortVertex,
      Nat.min_eq_left (Nat.le_of_lt hi')] <;>
    dsimp [sideRectangleBase] <;> constructor <;> (try constructor) <;> (try constructor) <;> omega

/-- Absence of the opposite-side primal connection produces the actual full
source dual-screen crossing, including both literal terminal rows. -/
theorem sideCrossing_of_no_primal_connection (m : ℕ) (hm : 1 ≤ m) (right : Bool)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hno : X ∉ sidePrimalConnectionEvent m right) :
    X ∈ (if right then FKC.FiniteFK.slitScreenRightCrossingEvent m
      else FKC.FiniteFK.slitScreenLeftCrossingEvent m) := by
  obtain ⟨b,hb,t,ht,hconn⟩ := sideRectangleCutDual_crossing_of_no_primal_connection m right X hno
  have hactual : ∃ b ∈ FKC.FiniteFK.slitScreenBottomTerminals m (sideFaceBases m right),
      ∃ t ∈ FKC.FiniteFK.slitScreenTopTerminals m (sideFaceBases m right),
        (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m X (sideFaceBases m right)).Reachable b t :=
    ⟨b.val,sideBottomPort_terminal m right b hb,t.val,sideTopPort_terminal m right t ht,
      hconn.map (sideCutDualToActualSource m hm right X hno)⟩
  cases right
  · rw [ite_eq_right Bool.false_ne_true,FKC.FiniteFK.slitScreenLeftCrossingEvent_eq_actualClosedDual m hm]
    exact hactual
  · rw [ite_eq_left rfl,FKC.FiniteFK.slitScreenRightCrossingEvent_eq_actualClosedDual m hm]
    exact hactual

end
end PottsContinuity.Thm4Records
