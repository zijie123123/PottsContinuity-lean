module

public import PottsContinuity.Thm4Records.ScreenIndex
public import PottsContinuity.Thm4Records.SideCutSource
public import PottsContinuity.PlanarTopology.SlitArchSampledGeometry

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK PD.FK.Medial PD.Duality Exploration Push RSW Thm4Plane
noncomputable section

def sourceScreenIndexWalk (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (F : Finset FKC.LatticeVertex) {s t : FKC.LatticeVertex}
    (p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A F).Walk s t) :
    squareLattice.Walk s t := p.map (PlanarTopology.slitScreenDualToIndexLattice (16*m) A F)

@[simp] theorem sourceScreenIndexWalk_support (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (F : Finset FKC.LatticeVertex) {s t : FKC.LatticeVertex}
    (p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A F).Walk s t) :
    (sourceScreenIndexWalk m A F p).support=p.support := by
  induction p with
  | nil => rfl
  | @cons x y z h q ih => exact congrArg (List.cons x) ih

@[simp] theorem sourceScreenIndexWalk_edges (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (F : Finset FKC.LatticeVertex) {s t : FKC.LatticeVertex}
    (p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A F).Walk s t) :
    (sourceScreenIndexWalk m A F p).edges=p.edges := by
  induction p with
  | nil => rfl
  | @cons x y z h q ih => exact congrArg (List.cons s(x,y)) ih

/-- A sampled primal step cannot cross any edge of a genuine full source
closed-dual screen. The normalized crossed original bond is identified exactly. -/
theorem sourceOpenStep_avoids_sourceScreen (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (F : Finset FKC.LatticeVertex) {s t : FKC.LatticeVertex}
    (p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A F).Walk s t)
    {u v : FKC.FiniteFK.SlitBoxVertex (16*m)}
    (huv : (openGraph (FKC.FiniteFK.slitBoxGraph (16*m)) A).Adj u v)
    (b : LatticeBond) (hb : b.toSym2=s(u.val,v.val)) :
    (dualBondOfPrimal b).toSym2 ∉ (sourceScreenIndexWalk m A F p).edges := by
  intro hcrossed
  have hed : (dualBondOfPrimal b).toSym2 ∈ p.edges :=
    sourceScreenIndexWalk_edges m A F p ▸ hcrossed
  have hdual := p.edges_subset_edgeSet hed
  have hdadj : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A F).Adj
      (dualBondOfPrimal b).source (dualBondOfPrimal b).target := by
    exact (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A F).mem_edgeSet.mp hdual
  obtain ⟨d,f,hcross,hclosed,hdir,_,_⟩ := hdadj
  have hd : latticeBondEquiv d=dualBondOfPrimal b := by
    apply LatticeBond.toSym2_injective
    rw [latticeBondEquiv_toSym2]
    rcases hdir with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact congrArg₂ Sym2.mk h1.symm h2.symm
    · exact (congrArg₂ Sym2.mk h2.symm h1.symm).trans Sym2.eq_swap
  have hp : latticeBondEquiv (FKC.Medial.primalBondOfDual d)=b := by
    rw [latticeBondEquiv_primalBondOfDual,hd,primalBondOfDual_dualBondOfPrimal]
  obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ _ _).mp huv
  have hfe : f=e := by
    apply (FKC.FiniteFK.slitBoxEdgeEmbedding (16*m)).injective
    rw [← hcross]
    apply Subtype.ext
    change (FKC.Medial.primalBondOfDual d).toSym2=Sym2.map Subtype.val e.val
    rw [← latticeBondEquiv_toSym2,hp,hb,heq]
    rfl
  exact hclosed (hfe ▸ he)

/-- Full-height source screens have constant index along actual primal bonds,
including the upper and lower source boundary rows. -/
theorem sourceScreenIndex_eq_of_open_adj (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (F : Finset FKC.LatticeVertex) {s t : FKC.LatticeVertex}
    (p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A F).Walk s t)
    (hs : s.2=-(16*(m:ℤ))-1) (ht : t.2=16*(m:ℤ))
    {u v : FKC.FiniteFK.SlitBoxVertex (16*m)}
    (huv : (openGraph (FKC.FiniteFK.slitBoxGraph (16*m)) A).Adj u v) :
    rayIndex u.val (sourceScreenIndexWalk m A F p)=
      rayIndex v.val (sourceScreenIndexWalk m A F p) := by
  have hlat := ((FKC.FiniteFK.slitBoxGraph_adj_iff _ _ _).mp (openGraph_le _ _ huv)).1
  have hu := (FKC.mem_latticeRectangle _ _ _ _).mp u.property
  have hv := (FKC.mem_latticeRectangle _ _ _ _).mp v.property
  have hstep := (FKC.squareLattice_adj_iff _ _).mp hlat
  apply screenIndex_eq_of_uncrossed_adj _
    ((PD.FK.squareLattice_adj_iff _ _).mpr hstep)
  · intro h; omega
  · intro h; omega
  · exact sourceOpenStep_avoids_sourceScreen m A F p huv

/-- Genuine primal connectivity preserves the full source screen index. -/
theorem sourceScreenIndex_eq_of_open_reachable (m : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (F : Finset FKC.LatticeVertex) {s t : FKC.LatticeVertex}
    (p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A F).Walk s t)
    (hs : s.2=-(16*(m:ℤ))-1) (ht : t.2=16*(m:ℤ))
    {u v : FKC.FiniteFK.SlitBoxVertex (16*m)}
    (hconn : ActualConnected (FKC.FiniteFK.slitBoxGraph (16*m)) A u v) :
    rayIndex u.val (sourceScreenIndexWalk m A F p)=
      rayIndex v.val (sourceScreenIndexWalk m A F p) := by
  obtain ⟨q⟩ := hconn
  induction q with
  | nil => rfl
  | cons hadj q ih => exact (sourceScreenIndex_eq_of_open_adj m A F p hs ht hadj).trans ih

/-- Censored actual connectivity is also actual ambient connectivity. -/
theorem censoredActualConnected_ambient {V : Type*} [Finite V]
    {G H : SimpleGraph V} (hHG : H ≤ G) (A : Configuration G) {u v : V}
    (hconn : ActualConnected H (Thm3.Prop4.censoredConfiguration hHG A) u v) :
    ActualConnected G A u v := by
  apply hconn.mono
  intro x y hxy
  obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ _ _).mp hxy
  exact (openGraph_adj _ _ _ _).mpr ⟨Thm3.Prop4.censoredEdgeInclusion hHG e,
    (Thm3.Prop4.mem_censoredConfiguration hHG A e).mp he,heq⟩

/-- A full side screen gives the outer explored primal cluster its exterior
index. This separation uses actual paths and permits arbitrary screen folds. -/
theorem sideOuterCluster_sourceScreenIndex (m : ℕ) (right : Bool)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    {s t : FKC.LatticeVertex}
    (p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A
      (sideFaceBases m right)).Walk s t)
    (hsF : s ∈ sideFaceBases m right)
    (hs : s.2=-(16*(m:ℤ))-1) (ht : t.2=16*(m:ℤ))
    (v : FKC.FiniteFK.SlitBoxVertex (16*m))
    (hv : v ∈ Thm3.Prop4.censoredSeedCluster
      (sideCensoredGraph_le m right) (sideOuterSeeds m right) A) :
    rayIndex v.val (sourceScreenIndexWalk m A (sideFaceBases m right) p)=
      if right then 0 else 1 := by
  obtain ⟨u,hu,hconn⟩ := hv
  have hidx := sourceScreenIndex_eq_of_open_reachable m A (sideFaceBases m right) p hs ht
    (censoredActualConnected_ambient (sideCensoredGraph_le m right) A hconn)
  rw [← hidx]
  have hsupport : ∀ z ∈ (sourceScreenIndexWalk m A (sideFaceBases m right) p).support,
      z ∈ sideFaceBases m right := by
    intro z hz
    rw [sourceScreenIndexWalk_support] at hz
    exact PlanarTopology.slitScreen_actual_walk_support (16*m) A _ p hsF z hz
  have hub := (FKC.mem_latticeRectangle _ _ _ _).mp u.property
  cases right
  · have hux : u.val.1=-(5*(m:ℤ)) := hu
    have hid := rayIndex_left_telescope u.val (sourceScreenIndexWalk m A (sideFaceBases m false) p) (by
      intro z hz
      have hz' := hsupport z hz
      simp only [sideFaceBases,Bool.false_eq_true,ite_false,
        FKC.FiniteFK.slitScreenLeftFaceBases,Finset.mem_product,Finset.mem_Icc] at hz'
      omega)
    rw [hid]
    simp only [hs,ht]
    rw [ite_eq_left (by omega),ite_eq_right (by omega)]
    rfl
  · have hux : u.val.1=5*(m:ℤ) := hu
    exact rayIndex_zero_of_right u.val (sourceScreenIndexWalk m A (sideFaceBases m true) p) (by
      intro z hz
      have hz' := hsupport z hz
      simp only [sideFaceBases,ite_true,FKC.FiniteFK.slitScreenRightFaceBases,
        Finset.mem_product,Finset.mem_Icc] at hz'
      omega)

end
end PottsContinuity.Thm4Records
