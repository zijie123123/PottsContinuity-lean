module

public import PottsContinuity.Thm3.Push.SideCollarExtension
public import PottsContinuity.PlanarMixed.FiniteSlit.BarrierEdges
public import PottsContinuity.PD.Duality.RectangleFlowDimension

@[expose] public section

namespace PottsContinuity.Push
open PD.FK PD.FK.Medial PlanarMixed.FiniteSlit
noncomputable section
private theorem collar_fixed_edge_of_pair (w h : ℕ)
    (f : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).edgeSet)
    (u v : RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h))
    (hp : (rectanglePrimalEdgeBond (0,0) (sideCollarSize w h) (sideCollarSize w h) f).toSym2 = s(u.val,v.val))
    (hu : u.val.1 = 1)
    (hv : v.val.1 = 1 ∨ (v.val.1 = 2 ∧ u.val.2 = v.val.2 ∧ 0 ≤ u.val.2 ∧ u.val.2 ≤ (h:ℤ))) :
    f ∈ sideCollarOpenEdges w h := by
  classical
  have heq : f.val = s(u,v) := by
    apply Sym2.map.injective Subtype.val_injective
    exact (rectanglePrimalEdgeBond_toSym2_public (0,0) (sideCollarSize w h) (sideCollarSize w h) f).symm.trans hp
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _,u,v,hu,hv,heq⟩

/-- Closing a tip path through the fixed open collar creates no closed
sampled barrier bond: every auxiliary-square edge of the whole barrier is
open. The bottom and remote return edges lie outside the sampled square. -/
theorem sideCollar_barrier_trace_open_of_open_source_trace
    (w h : ℕ) (A : Configuration (rectangleGraph (0,0) w h))
    (M : ℕ) (hMN : sideCollarSize w h ≤ M)
    (b y : ℤ) (hy0 : 0 ≤ y) (hyh : y ≤ (h:ℤ))
    (q : squareLattice.Walk (b,0) (2,y))
    {z : LatticeVertex} (p : squareLattice.Walk z z)
    (htrace : ∀ f : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).edgeSet,
      (rectanglePrimalEdgeBond (0,0) (sideCollarSize w h) (sideCollarSize w h) f).toSym2 ∈ q.edges →
      f ∈ sideCollarExtension w h A)
    (hallowed : ∀ e ∈ p.edges, e ∈ slitBarrierEdges M 2 y b q) :
    ∀ f : (rectangleGraph (0,0) (sideCollarSize w h) (sideCollarSize w h)).edgeSet,
      (rectanglePrimalEdgeBond (0,0) (sideCollarSize w h) (sideCollarSize w h) f).toSym2 ∈ p.edges →
      f ∈ sideCollarExtension w h A := by
  classical
  intro f hf
  let d := rectanglePrimalEdgeBond (0,0) (sideCollarSize w h) (sideCollarSize w h) f
  have hd := rectanglePrimalEdgeBond_endpoints_mem_public (0,0) (sideCollarSize w h) (sideCollarSize w h) f
  have hs := (PD.FK.mem_latticeRectangle _ _ _ _).mp hd.1
  have ht := (PD.FK.mem_latticeRectangle _ _ _ _).mp hd.2
  simp only [zero_add] at hs ht
  change (0 ≤ d.source.1 ∧ d.source.1 ≤ (sideCollarSize w h:ℤ)) ∧
    (0 ≤ d.source.2 ∧ d.source.2 ≤ (sideCollarSize w h:ℤ)) at hs
  change (0 ≤ d.target.1 ∧ d.target.1 ≤ (sideCollarSize w h:ℤ)) ∧
    (0 ≤ d.target.2 ∧ d.target.2 ≤ (sideCollarSize w h:ℤ)) at ht
  have he := hallowed d.toSym2 hf
  rcases he with hq | hroot | ⟨htip,_⟩ | ⟨u,v,huv,hout⟩
  · exact htrace f hq
  · change s(d.source,d.target) = s((b,-1),(b,0)) at hroot
    rcases Sym2.eq_iff.mp hroot with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · have hy := congrArg Prod.snd h1
      omega
    · have hy := congrArg Prod.snd h2
      omega
  · have hyN : y ≤ (sideCollarSize w h:ℤ) := by dsimp [sideCollarSize]; omega
    let u : RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h) :=
      ⟨(1,y),by rw [PD.FK.mem_latticeRectangle]; dsimp [sideCollarSize]; omega⟩
    let v : RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h) :=
      ⟨(2,y),by rw [PD.FK.mem_latticeRectangle]; dsimp [sideCollarSize]; omega⟩
    apply Finset.mem_union.mpr
    right
    apply collar_fixed_edge_of_pair w h f u v
    · exact htip
    · rfl
    · exact Or.inr ⟨rfl,rfl,hy0,hyh⟩
  · have hp : s(d.source,d.target) = s(u,v) := huv
    have hN : (4:ℤ) ≤ (sideCollarSize w h:ℤ) := by dsimp [sideCollarSize]; omega
    rcases hout with hcol | hbottom | htop | hleft | hright
    · have hxs : d.source.1 = 1 ∧ d.target.1 = 1 := by
        rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
          have hx1 := congrArg Prod.fst h1 <;> have hx2 := congrArg Prod.fst h2 <;> omega
      let u' : RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h) := ⟨d.source,hd.1⟩
      let v' : RectangleVertex (0,0) (sideCollarSize w h) (sideCollarSize w h) := ⟨d.target,hd.2⟩
      apply Finset.mem_union.mpr
      right
      exact collar_fixed_edge_of_pair w h f u' v' rfl hxs.1 (Or.inl hxs.2)
    · rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have hy1 := congrArg Prod.snd h1 <;> have hy2 := congrArg Prod.snd h2 <;> omega
    · rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have hy1 := congrArg Prod.snd h1 <;> have hy2 := congrArg Prod.snd h2 <;> omega
    · rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have hx1 := congrArg Prod.fst h1 <;> have hx2 := congrArg Prod.fst h2 <;> omega
    · rcases Sym2.eq_iff.mp hp with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have hx1 := congrArg Prod.fst h1 <;> have hx2 := congrArg Prod.fst h2 <;> omega

end
end PottsContinuity.Push
