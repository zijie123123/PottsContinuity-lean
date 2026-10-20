module

public import PottsContinuity.Thm3.RSW.StripPrunedFiniteDuality
public import PottsContinuity.PD.Duality.RectangleFlowDimension

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.FK.Medial
noncomputable section

/-- The transported top-row state contains exactly those actual host bonds
whose two physical endpoints lie on the source top row. -/
theorem mem_stripRectangleTopRowState_iff (n M : ℕ)
    (e : (rectangleGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).edgeSet) :
    e ∈ stripRectangleTopRowState n M ↔ ∀ v ∈ e.val, v.val.2=3*(n:ℤ) := by
  classical
  let iso := stripWindowRectangleIso n M
  obtain ⟨f,rfl⟩ := (configurationIsoEdgeEquiv iso).surjective e
  have hm : configurationIsoEdgeEquiv iso f ∈ configurationIso iso (stripTopRowState n M) ↔
      f ∈ stripTopRowState n M := by
    change configurationIsoEdgeEquiv iso f ∈
      (stripTopRowState n M).map (configurationIsoEdgeEquiv iso).toEmbedding ↔ _
    constructor
    · intro h
      obtain ⟨g,hg,hgf⟩ := Finset.mem_map.mp h
      have hgf' := (configurationIsoEdgeEquiv iso).injective hgf
      simpa only [hgf'] using hg
    · intro h
      exact Finset.mem_map.mpr ⟨f,h,rfl⟩
  change configurationIsoEdgeEquiv iso f ∈ configurationIso iso (stripTopRowState n M) ↔ _
  rw [hm]
  rcases f with ⟨f,hf⟩
  induction f using Sym2.inductionOn with
  | _ u v =>
    change (⟨s(u,v),hf⟩ : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet) ∈
      stripTopRowState n M ↔ ∀ z ∈ s(iso u,iso v), z.val.2=3*(n:ℤ)
    simp only [stripTopRowState,Finset.mem_filter,Finset.mem_univ,true_and]
    simp [stripWindowWiredVertices,iso,stripWindowRectangleIso]

/-- A genuine dual top-port edge crosses an original primal top-row bond.
The statement concerns actual host bonds, independently of any probability law. -/
theorem rectangleDual_top_port_crosses_top_row
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleDualVertex a w h)
    (e : RectangleDualEdgeCarrier a w h)
    (he : s(u,v)=rectangleDualCarrierPair a w h e)
    (hu : u.val.2=a.2+(h:ℤ)) :
    ∀ z ∈ e.primalEdge.val, z.val.2=a.2+(h:ℤ) := by
  have hpair := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.val)) he
  have hs := rectanglePrimalEdgeBond_endpoints_mem_public a w h e.primalEdge
  have hp : s(u.val,v.val) =
      s((dualBondOfPrimal (rectanglePrimalEdgeBond a w h e.primalEdge)).source,
        (dualBondOfPrimal (rectanglePrimalEdgeBond a w h e.primalEdge)).target) := by
    simpa [rectangleDualCarrierPair,rectangleDualEdgeSource_val,
      rectangleDualEdgeTarget_val,e.crossingBond_eq,rectangleCrossingDualBond] using hpair
  have hb := rectanglePrimalEdgeBond_toSym2_public a w h e.primalEdge
  intro z hz
  have hzm : z.val ∈ (rectanglePrimalEdgeBond a w h e.primalEdge).toSym2 := by
    rw [hb]
    exact Sym2.mem_map.mpr ⟨z,hz,rfl⟩
  generalize hbeq : rectanglePrimalEdgeBond a w h e.primalEdge = b at hp hs hzm
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis <;>
    simp only [dualBondOfPrimal,LatticeBond.source,LatticeBond.target,LatticeBond.toSym2] at hp hs hzm
  all_goals
    rw [mem_latticeRectangle,mem_latticeRectangle] at hs
    rcases Sym2.eq_iff.mp hp with ⟨huv,hvv⟩ | ⟨huv,hvv⟩
    all_goals
      have hy := congrArg Prod.snd huv
      dsimp at hy
      rcases Sym2.mem_iff'.mp hzm with hzm | hzm
      all_goals
        have hzy := congrArg Prod.snd hzm
        dsimp at hzy
        omega

/-- Conversely, an original primal top-row bond has a crossed dual edge
incident to the expanded top-port row. -/
theorem rectangleDual_top_row_crosses_top_port
    (a : LatticeVertex) (w h : ℕ) (u v : RectangleDualVertex a w h)
    (e : RectangleDualEdgeCarrier a w h)
    (he : s(u,v)=rectangleDualCarrierPair a w h e)
    (htop : ∀ z ∈ e.primalEdge.val, z.val.2=a.2+(h:ℤ)) :
    u.val.2=a.2+(h:ℤ) ∨ v.val.2=a.2+(h:ℤ) := by
  have hb := rectanglePrimalEdgeBond_toSym2_public a w h e.primalEdge
  have hheight (z : LatticeVertex) (hz : z ∈ (rectanglePrimalEdgeBond a w h e.primalEdge).toSym2) :
      z.2=a.2+(h:ℤ) := by
    rw [hb] at hz
    obtain ⟨x,hx,hxz⟩ := Sym2.mem_map.mp hz
    exact (congrArg Prod.snd hxz).symm.trans (htop x hx)
  have hs := hheight _ (show (rectanglePrimalEdgeBond a w h e.primalEdge).source ∈
      (rectanglePrimalEdgeBond a w h e.primalEdge).toSym2 by simp [LatticeBond.toSym2])
  have ht := hheight _ (show (rectanglePrimalEdgeBond a w h e.primalEdge).target ∈
      (rectanglePrimalEdgeBond a w h e.primalEdge).toSym2 by simp [LatticeBond.toSym2])
  have hpair := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.val)) he
  have hp : s(u.val,v.val) =
      s((dualBondOfPrimal (rectanglePrimalEdgeBond a w h e.primalEdge)).source,
        (dualBondOfPrimal (rectanglePrimalEdgeBond a w h e.primalEdge)).target) := by
    simpa [rectangleDualCarrierPair,rectangleDualEdgeSource_val,
      rectangleDualEdgeTarget_val,e.crossingBond_eq,rectangleCrossingDualBond] using hpair
  generalize hbeq : rectanglePrimalEdgeBond a w h e.primalEdge = b at hp hs ht
  rcases b with ⟨⟨x,y⟩,axis⟩
  cases axis <;>
    simp only [dualBondOfPrimal,LatticeBond.source,LatticeBond.target] at hp hs ht
  all_goals
    rcases Sym2.eq_iff.mp hp with ⟨hu,hv⟩ | ⟨hu,hv⟩
    all_goals
      have huy := congrArg Prod.snd hu
      have hvy := congrArg Prod.snd hv
      dsimp at huy hvy
      omega

end
end PottsContinuity.RSW
