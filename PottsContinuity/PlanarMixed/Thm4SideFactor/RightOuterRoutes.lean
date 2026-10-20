module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.OuterBond
public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushReducedDefinitions

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK PD.FK.Medial Thm4Side DualityExt
noncomputable section
abbrev SideDualVertex (m : ℕ) := RectangleDualVertex
  (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1))
abbrev sideDualGraph (m : ℕ) := rectangleDualGraph
  (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1))
abbrev rightDualExterior (m : ℕ)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  (rectangleSubgraphDualOpenRemovedState
    (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))
    (slitRightDualRectangleHostRemovedState m X)).val

theorem right_outer_step (m : ℕ)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) (b : LatticeBond)
    (hs : b.source ∈ PD.FK.latticeRectangle
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)))
    (ht : b.target ∈ PD.FK.latticeRectangle
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)))
    (hout : b.source ∉ FKC.latticeRectangle (-((16*m:ℕ):ℤ),-((16*m:ℕ):ℤ))
        (2*(16*m)) (2*(16*m)) ∨
      b.target ∉ FKC.latticeRectangle (-((16*m:ℕ):ℤ),-((16*m:ℕ):ℤ))
        (2*(16*m)) (2*(16*m)))
    (u v : SideDualVertex m) (hp : (dualBondOfPrimal b).toSym2 = s(u.val,v.val)) :
    ActualConnected (sideDualGraph m) (rightDualExterior m X) u v := by
  obtain ⟨d,hd,hpair⟩ := side_outer_dual_bond_open m
    (slitRightDualRectangleReveal m X) (slitRightDualRectangleHostRemovedState m X)
    (right_removed_open_endpoint_mem_original m X) b hs ht hout
  have hdv : d.val = s(u,v) := by
    apply Sym2.map.injective Subtype.val_injective
    exact hpair.trans hp
  exact (SimpleGraph.Adj.reachable ((openGraph_adj _ _ _ _).mpr ⟨d,hd,hdv⟩))

theorem right_native_outer_routes (m : ℕ)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (z : NativeSideVertex m) (hz : z ∈ (nativeSideFullBoundary m).boundary) :
    ∃ v : SideDualVertex m,
      v.val ∈ rectangleDualBoundary
        (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)) ∧
      ActualConnected (sideDualGraph m) (rightDualExterior m X)
        (rightNativeToHostDual m z) v := by
  have hb := (PD.FK.mem_latticeRectangle _ z.val _ _).mp z.property
  change z.val.1 = -16*(m:ℤ)-1 ∨ z.val.1 = 16*(m:ℤ) ∨ z.val.2 = 15*(m:ℤ) at hz
  rcases hz with hl | hr | ht
  · let v : SideDualVertex m := ⟨((m:ℤ)+z.val.2,-16*(m:ℤ)-2),by
      rw [rectangleDualExpanded,PD.FK.mem_latticeRectangle]
      push_cast at hb ⊢
      constructor <;> constructor <;> omega⟩
    refine ⟨v,?_,?_⟩
    · rw [rectangleDualBoundary,Finset.mem_filter]
      refine ⟨v.property,?_⟩
      intro hi
      have h := (Finset.mem_filter.mp hi).2
      dsimp [v] at h
      omega
    · let b : LatticeBond := ⟨((m:ℤ)+z.val.2,-16*(m:ℤ)-1),.horizontal⟩
      apply right_outer_step m X b
      · rw [PD.FK.mem_latticeRectangle]
        dsimp [b,LatticeBond.source]
        push_cast at hb ⊢
        constructor <;> constructor <;> omega
      · rw [PD.FK.mem_latticeRectangle]
        dsimp [b,LatticeBond.target]
        push_cast at hb ⊢
        constructor <;> constructor <;> omega
      · left
        rw [FKC.mem_latticeRectangle]
        dsimp [b,LatticeBond.source]
        omega
      · change (dualBondOfPrimal b).toSym2 = s(((m:ℤ)+z.val.2,z.val.1), v.val)
        simp [b,v,LatticeBond.toSym2,
          dualBondOfPrimal_source,dualBondOfPrimal_target,LatticeBond.faceBase,hl]
        omega
  · let v : SideDualVertex m := ⟨((m:ℤ)+z.val.2,16*(m:ℤ)+1),by
      rw [rectangleDualExpanded,PD.FK.mem_latticeRectangle]
      push_cast at hb ⊢
      constructor <;> constructor <;> omega⟩
    refine ⟨v,?_,?_⟩
    · rw [rectangleDualBoundary,Finset.mem_filter]
      refine ⟨v.property,?_⟩
      intro hi
      have h := (Finset.mem_filter.mp hi).2
      dsimp [v] at h
      omega
    · let b : LatticeBond := ⟨((m:ℤ)+z.val.2,16*(m:ℤ)+1),.horizontal⟩
      apply right_outer_step m X b
      · rw [PD.FK.mem_latticeRectangle]
        dsimp [b,LatticeBond.source]
        push_cast at hb ⊢
        constructor <;> constructor <;> omega
      · rw [PD.FK.mem_latticeRectangle]
        dsimp [b,LatticeBond.target]
        push_cast at hb ⊢
        constructor <;> constructor <;> omega
      · left
        rw [FKC.mem_latticeRectangle]
        dsimp [b,LatticeBond.source]
        omega
      · change (dualBondOfPrimal b).toSym2 = s(((m:ℤ)+z.val.2,z.val.1), v.val)
        simp [b,v,LatticeBond.toSym2,
          dualBondOfPrimal_source,dualBondOfPrimal_target,LatticeBond.faceBase,hr]
  · let v : SideDualVertex m := ⟨(16*(m:ℤ)+1,z.val.1),by
      rw [rectangleDualExpanded,PD.FK.mem_latticeRectangle]
      push_cast at hb ⊢
      constructor <;> constructor <;> omega⟩
    refine ⟨v,?_,?_⟩
    · rw [rectangleDualBoundary,Finset.mem_filter]
      refine ⟨v.property,?_⟩
      intro hi
      have h := (Finset.mem_filter.mp hi).2
      dsimp [v] at h
      omega
    · let b : LatticeBond := ⟨(16*(m:ℤ)+1,z.val.1),.vertical⟩
      apply right_outer_step m X b
      · rw [PD.FK.mem_latticeRectangle]
        dsimp [b,LatticeBond.source]
        push_cast at hb ⊢
        constructor <;> constructor <;> omega
      · rw [PD.FK.mem_latticeRectangle]
        dsimp [b,LatticeBond.target]
        push_cast at hb ⊢
        constructor <;> constructor <;> omega
      · left
        rw [FKC.mem_latticeRectangle]
        dsimp [b,LatticeBond.source]
        omega
      · change (dualBondOfPrimal b).toSym2 = s(((m:ℤ)+z.val.2,z.val.1), v.val)
        simp [b,v,LatticeBond.toSym2,
          dualBondOfPrimal_source,dualBondOfPrimal_target,LatticeBond.faceBase,ht]
        omega

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
