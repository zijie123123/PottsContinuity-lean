module

public import PottsContinuity.Thm4Records.ActualResidualConnector
public import PottsContinuity.Thm4Records.SourceScreenIndex

@[expose] public section

namespace PottsContinuity.Thm4Records
open PD.FK Exploration Push RSW Thm4Plane
noncomputable section

/-- Literal R-star vertices are exactly the original middle face labels. -/
theorem connectorRStarVertex_mem_middle (m : ℕ) (hm : 1 ≤ m) (u : SlitRStarVertex m) :
    u.val ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m := by
  have hc := (PD.FK.mem_latticeRectangle _ _ _ _).mp u.property
  simp only [FKC.FiniteFK.slitScreenMiddleFaceBases,Finset.mem_product,Finset.mem_Icc]
  dsimp [slitScreenRStarBase,slitScreenRStarSide] at hc
  constructor <;> constructor <;> omega

/-- The auxiliary square graph retains its actual original crossed-bond
interpretation when the source configuration contains only residual open bonds. -/
def connectorRStarReadToSource (m : ℕ) (hm : 1 ≤ m)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph (16*m))) :
    openGraph (SlitRStarGraph m) (slitRStarDualConfiguration m hm A) →g
      FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m A
        (FKC.FiniteFK.slitScreenMiddleFaceBases m) where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ _ _).mp huv
    let d := slitRStarEdgeBridge m hm e
    have hpair : d.dualBond.toSym2=s(u.val,v.val) := by
      rw [d.pairEq,heq]
      rfl
    have hdir : u.val=d.dualBond.source ∧ v.val=d.dualBond.target ∨
        u.val=d.dualBond.target ∧ v.val=d.dualBond.source := by
      rcases Sym2.eq_iff.mp hpair with h | h
      · exact Or.inl ⟨h.1.symm,h.2.symm⟩
      · exact Or.inr ⟨h.2.symm,h.1.symm⟩
    exact ⟨d.dualBond,d.primalEdge,d.crosses,
      (mem_slitRStarDualConfiguration m hm A e).mp he,hdir,
      connectorRStarVertex_mem_middle m hm u,connectorRStarVertex_mem_middle m hm v⟩

/-- The auxiliary left-right crossing has a full original-label source walk,
with every support vertex in R-star. -/
theorem connectorAuxiliaryCrossing_source_walk (m : ℕ) (hm : 1 ≤ m)
    (R : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (U : RemainingConfiguration (FKC.FiniteFK.slitBoxGraph (16*m)) R)
    (hU : U ∈ connectorAuxiliaryCrossing m hm R) :
    ∃ a b : FKC.LatticeVertex,
      ∃ p : (FKC.FiniteFK.slitScreenActualConfigurationClosedDualGraph m U.val
        (FKC.FiniteFK.slitScreenMiddleFaceBases m)).Walk a b,
      a.1=-(5*(m:ℤ)) ∧ b.1=5*(m:ℤ)-1 ∧
      ∀ z ∈ p.support, z ∈ FKC.FiniteFK.slitScreenMiddleFaceBases m := by
  obtain ⟨u,v,hu,hv,⟨p⟩⟩ := hU
  let P := p.map (connectorRStarReadToSource m hm U.val)
  refine ⟨u.val,v.val,P,hu,hv,?_⟩
  exact PlanarTopology.slitScreen_actual_walk_support (16*m) U.val _ P
    (connectorRStarVertex_mem_middle m hm u)

end
end PottsContinuity.Thm4Records
