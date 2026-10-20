module

public import PottsContinuity.PlanarMixed.StripRSWSelectors.PaddedCompletion
public import PottsContinuity.PlanarMixed.FiniteSlit.BarrierEdges
public import PottsContinuity.PD.Duality.RectangleFlowDimension

@[expose] public section

namespace PottsContinuity.PlanarMixed.StripRSWSelectors
open PD.FK PD.FK.Medial PlanarMixed.FiniteSlit
noncomputable section

/-- Closing a physical prefix through the fixed ray keeps every sampled
bond of the whole barrier open in the padded completion. -/
theorem prefixAux_barrier_trace_open (n s M : ℕ) (hfit : 9*s ≤ 2*n)
    (b : Push.CaseTwoTipEndpointRecord n s) (C : Configuration (rectangleGraph (0,0) (2*n) (2*n)))
    (hMN : 2*n+1 ≤ M) (hleft : 4*(s:ℤ)-(M:ℤ)<0)
    (hright : (2*n+1:ℕ)<4*(s:ℤ)+(M:ℤ)-1)
    (a t : ℤ) (P : squareLattice.Walk (a,0) (4*(s:ℤ)-1,t))
    (htip : (4*(s:ℤ),b.2.val.2) ∉ P.support)
    (htrace : ∀ f : (prefixAuxGraph n).edgeSet,
      (rectanglePrimalEdgeBond (0,0) (2*n+1) (2*n+1) f).toSym2 ∈ P.edges →
        f ∈ prefixAuxCompletion n s hfit b C)
    {z : LatticeVertex} (L : squareLattice.Walk z z)
    (hallowed : ∀ e ∈ L.edges, e ∈ slitBarrierEdges M (4*(s:ℤ)) b.2.val.2 a P) :
    ∀ f : (prefixAuxGraph n).edgeSet,
      (rectanglePrimalEdgeBond (0,0) (2*n+1) (2*n+1) f).toSym2 ∈ L.edges →
        f ∈ prefixAuxCompletion n s hfit b C := by
  classical
  intro f hf
  let d := rectanglePrimalEdgeBond (0,0) (2*n+1) (2*n+1) f
  have hd := rectanglePrimalEdgeBond_endpoints_mem_public (0,0) (2*n+1) (2*n+1) f
  have hs := (PD.FK.mem_latticeRectangle _ _ _ _).mp hd.1
  have ht := (PD.FK.mem_latticeRectangle _ _ _ _).mp hd.2
  simp only [zero_add] at hs ht
  rcases hallowed d.toSym2 hf with hp | hroot | ⟨_,hptip⟩ | ⟨u,v,huv,hout⟩
  · exact htrace f hp
  · change s(d.source,d.target)=s((a,-1),(a,0)) at hroot
    rcases Sym2.eq_iff.mp hroot with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
      have h1y := congrArg Prod.snd h1 <;> have h2y := congrArg Prod.snd h2 <;> (dsimp only [d] at *; omega)
  · exact (htip hptip).elim
  · have hp : s(d.source,d.target)=s(u,v) := huv
    rcases hout with hcol | hbottom | htop | hleft' | hright'
    · have hray : d.source.1=4*(s:ℤ)-1 ∧ d.target.1=4*(s:ℤ)-1 ∧
          b.2.val.2 ≤ d.source.2 ∧ b.2.val.2 ≤ d.target.2 := by
        rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
          have h1x := congrArg Prod.fst h1 <;> have h2x := congrArg Prod.fst h2 <;>
          have h1y := congrArg Prod.snd h1 <;> have h2y := congrArg Prod.snd h2 <;> (dsimp only [d] at *; omega)
      let u' : PrefixAuxVertex n := ⟨d.source,hd.1⟩
      let v' : PrefixAuxVertex n := ⟨d.target,hd.2⟩
      have hpair : f.val=s(u',v') := by
        apply Sym2.map.injective Subtype.val_injective
        exact (rectanglePrimalEdgeBond_toSym2_public (0,0) (2*n+1) (2*n+1) f).symm
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro w hw
      rw [hpair] at hw
      rcases Sym2.mem_iff'.mp hw with rfl | rfl
      · exact ⟨hray.1,hray.2.2.1⟩
      · exact ⟨hray.2.1,hray.2.2.2⟩
    · rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have h1y := congrArg Prod.snd h1 <;> have h2y := congrArg Prod.snd h2 <;> (dsimp only [d] at *; omega)
    · rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have h1y := congrArg Prod.snd h1 <;> have h2y := congrArg Prod.snd h2 <;> (dsimp only [d] at *; omega)
    · rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have h1x := congrArg Prod.fst h1 <;> have h2x := congrArg Prod.fst h2 <;> (dsimp only [d] at *; omega)
    · rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have h1x := congrArg Prod.fst h1 <;> have h2x := congrArg Prod.fst h2 <;> (dsimp only [d] at *; omega)

end
end PottsContinuity.PlanarMixed.StripRSWSelectors
