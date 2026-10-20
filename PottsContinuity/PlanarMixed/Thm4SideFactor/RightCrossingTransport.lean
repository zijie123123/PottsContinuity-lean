module

public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightReducedEmbedding
public import PottsContinuity.PlanarMixed.Thm4SideFactor.RightStateTransport
public import PottsContinuity.PlanarMixed.Thm4SideFactor.NativePushPaths
public import PottsContinuity.FKC.FiniteFK.SlitScreenCrossingEvents

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK PD.FK.Medial DualityExt Thm4Side Thm4SideEuler
noncomputable section

abbrev RightRetainedDualGraph (m : ℕ) (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :=
  rectangleSubgraphDualGraph (sideExactLawHostSubgraph_le m (slitRightDualRectangleReveal m X))

def rightNativeRemainingRead (m : ℕ) (hm : 1 ≤ m)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (B : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m))
      (slitRightDualRectangleReveal m X)) : Configuration (nativeSideReducedGraph m) :=
  embeddedConfigurationRestriction (nativeSideReducedGraph m) (RightRetainedDualGraph m X)
    (rightNativeToHostDual m) (rightNativeReduced_map_le_hostDual m hm X)
      (slitRightResidualToHostDual m X B)

def sideBondToFKC (d : LatticeBond) : FKC.Medial.LatticeBond :=
  ⟨d.base,match d.axis with | .horizontal => .horizontal | .vertical => .vertical⟩

theorem sideBondToFKC_pair (d : LatticeBond) : (sideBondToFKC d).toSym2 = d.toSym2 := by
  rcases d with ⟨base,axis⟩
  cases axis <;> rfl

theorem sideBondToFKC_primal_pair (d : LatticeBond) :
    (FKC.Medial.primalBondOfDual (sideBondToFKC d)).toSym2 = (primalBondOfDual d).toSym2 := by
  rcases d with ⟨base,axis⟩
  cases axis <;> rfl

theorem rightNative_band_mem_faces (m : ℕ) (hm : 1 ≤ m) (z : NativeSideVertex m)
    (hz : 0 ≤ z.val.2 ∧ z.val.2 ≤ ((4*m-1:ℕ):ℤ)) :
    ((m:ℤ)+z.val.2,z.val.1) ∈ FKC.FiniteFK.slitScreenRightFaceBases m := by
  have hb := (PD.FK.mem_latticeRectangle _ z.val _ _).mp z.property
  simp only [FKC.FiniteFK.slitScreenRightFaceBases,Finset.mem_product,Finset.mem_Icc]
  push_cast at hb ⊢
  omega

theorem rightNative_open_step_to_actual_closedDual (m : ℕ) (hm : 1 ≤ m)
    (X Y : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (u v : NativeSideVertex m)
    (hu : 0 ≤ u.val.2 ∧ u.val.2 ≤ ((4*m-1:ℕ):ℤ))
    (hv : 0 ≤ v.val.2 ∧ v.val.2 ≤ ((4*m-1:ℕ):ℤ))
    (hopen : (openGraph (nativeSideReducedGraph m)
      (rightNativeRemainingRead m hm X ((configurationSplitEquiv
        (FKC.FiniteFK.slitBoxGraph (16*m)) (slitRightDualRectangleReveal m X) Y).1))).Adj u v) :
    (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m Y
      (FKC.FiniteFK.slitScreenRightFaceBases m)).Adj
      ((m:ℤ)+u.val.2,u.val.1) ((m:ℤ)+v.val.2,v.val.1) := by
  classical
  let R := slitRightDualRectangleReveal m X
  let B := (configurationSplitEquiv (FKC.FiniteFK.slitBoxGraph (16*m)) R Y).1
  let C := rightNativeRemainingRead m hm X B
  have huv : (nativeSideReducedGraph m).Adj u v := openGraph_le _ C hopen
  let e : (nativeSideReducedGraph m).edgeSet := ⟨s(u,v),(nativeSideReducedGraph m).mem_edgeSet.mpr huv⟩
  have he : e ∈ C := by
    obtain ⟨a,ha,hap⟩ := (openGraph_adj _ _ _ _).mp hopen
    have hae : a=e := Subtype.ext hap
    exact hae ▸ ha
  let hsub := rightNativeReduced_map_le_hostDual m hm X
  let de := embeddedEdgeEmbedding (nativeSideReducedGraph m) (RightRetainedDualGraph m X)
    (rightNativeToHostDual m) hsub e
  have hde : de ∈ slitRightResidualToHostDual m X B :=
    (mem_embeddedConfigurationRestriction (nativeSideReducedGraph m) (RightRetainedDualGraph m X)
      (rightNativeToHostDual m) hsub (slitRightResidualToHostDual m X B) e).mp he
  have hfull : (nativeSideFullGraph m).Adj u v := edgeRestriction_le _ _ huv
  obtain ⟨d,hd⟩ := LatticeBond.exists_of_adj hfull
  let db := rightNativeDualBond m d
  let b := primalBondOfDual db
  have hsupp := rightNativeReduced_supported_bond m u v huv d hd
  have hdep : Sym2.map (fun z : RectangleDualVertex
      (-((16*m+1:ℕ):ℤ),-((16*m+1:ℕ):ℤ)) (2*(16*m+1)) (2*(16*m+1)) => z.val) de.val =
        (dualBondOfPrimal b).toSym2 := by
    rw [dualBondOfPrimal_primalBondOfDual,rightNativeDualBond_pair,hd]
    rfl
  have hclosed := (rightHostDual_edgeState m hm X Y b hsupp.1 hsupp.2 de hdep).mp hde
  let c := rightSourceBondEdge m hm b hsupp.1 hsupp.2
  have hcphys : Sym2.map (fun z : FKC.FiniteFK.SlitBoxVertex (16*m) => z.val) c.val = b.toSym2 := by rfl
  have hpair : (sideBondToFKC db).toSym2 = s(((m:ℤ)+u.val.2,u.val.1),((m:ℤ)+v.val.2,v.val.1)) := by
    rw [sideBondToFKC_pair,rightNativeDualBond_pair,hd]
    rfl
  refine ⟨sideBondToFKC db,c,?_,hclosed,?_,
    rightNative_band_mem_faces m hm u hu,rightNative_band_mem_faces m hm v hv⟩
  · apply Subtype.ext
    change (FKC.Medial.primalBondOfDual (sideBondToFKC db)).toSym2 =
      Sym2.map (fun z : FKC.FiniteFK.SlitBoxVertex (16*m) => z.val) c.val
    rw [sideBondToFKC_primal_pair,hcphys]
  · rcases Sym2.eq_iff.mp hpair with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨hs.symm,ht.symm⟩
    · exact Or.inr ⟨ht.symm,hs.symm⟩

theorem rightNative_crossing_implies_source_screen (m : ℕ) (hm : 1 ≤ m)
    (X Y : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (hC : rightNativeRemainingRead m hm X ((configurationSplitEquiv
      (FKC.FiniteFK.slitBoxGraph (16*m)) (slitRightDualRectangleReveal m X) Y).1) ∈
        nativeSideReducedCrossingEvent m) :
    Y ∈ FKC.FiniteFK.slitScreenRightCrossingEvent m := by
  classical
  let C := rightNativeRemainingRead m hm X ((configurationSplitEquiv
    (FKC.FiniteFK.slitBoxGraph (16*m)) (slitRightDualRectangleReveal m X) Y).1)
  obtain ⟨u,v,hu,hv,p,hp⟩ := nativeSideReducedCrossingEvent_confined_walk m C hC
  let S : Set (NativeSideVertex m) := {z | 0 ≤ z.val.2 ∧ z.val.2 ≤ ((4*m-1:ℕ):ℤ)}
  let hom : (openGraph (nativeSideReducedGraph m) C).induce S →g
      FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m Y
        (FKC.FiniteFK.slitScreenRightFaceBases m) :=
    { toFun := fun z => ((m:ℤ)+z.val.val.2,z.val.val.1)
      map_rel' := by
        intro z w hzw
        exact rightNative_open_step_to_actual_closedDual m hm X Y z.val w.val
          z.property w.property hzw }
  let P := (p.induce S hp).map hom
  rw [FKC.FiniteFK.slitScreenRightCrossingEvent_eq_actualClosedDual m hm]
  refine ⟨((m:ℤ)+u.val.2,u.val.1),?_,((m:ℤ)+v.val.2,v.val.1),?_,⟨P⟩⟩
  · exact ⟨rightNative_band_mem_faces m hm u (hp _ p.start_mem_support),by dsimp; omega⟩
  · exact ⟨rightNative_band_mem_faces m hm v (hp _ p.end_mem_support),by dsimp; omega⟩

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
