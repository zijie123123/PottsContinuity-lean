module

public import PottsContinuity.Thm3.Prop4.FrozenReferenceDualSample
public import PottsContinuity.PlanarTopology.RectangleSampledClosedDual

/-!
# Restored finite dual paths retain actual sampled crossing bonds

The map forgets only the finite face membership proofs. Every mapped edge
is witnessed by its original closed primal bond in the restored sample.
Support is the exact coordinate image of the original retained walk.
-/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section

local instance finiteSampledMapPrimalEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _
local instance finiteSampledMapDualEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleDualGraph a w h).edgeSet := Classical.decEq _

/-- The actual finite complementary dual open graph maps to the genuine
sampled closed-dual graph on the original whole-plane face labels. -/
def rectanglePrimalDualOpenToSampled (a : LatticeVertex) (w h : ℕ)
    (A : Configuration (rectangleGraph a w h)) :
    openGraph (rectangleDualGraph a w h) (rectanglePrimalDualConfigurationEquiv a w h A) →g
      PlanarTopology.rectangleSampledClosedDualGraph a w h A where
  toFun z := z.val
  map_rel' := by
    intro x y hxy
    obtain ⟨e,he,hval⟩ := (openGraph_adj _ _ x y).mp hxy
    let d := (rectangleDualGraphEdgeEquiv a w h).symm e
    have hde : rectangleDualGraphEdgeEquiv a w h d = e := Equiv.apply_symm_apply _ e
    have hdmem : rectangleDualGraphEdgeEquiv a w h d ∈
        rectanglePrimalDualConfigurationEquiv a w h A := by rw [hde]; exact he
    have hclosed := (mem_rectanglePrimalDualConfigurationEquiv a w h A d).mp hdmem
    have hpair : rectangleDualCarrierPair a w h d = s(x,y) := by
      change (rectangleDualGraphEdgeEquiv a w h d).val = _
      rw [hde]
      exact hval
    have hcoords := congrArg (Sym2.map (fun z : RectangleDualVertex a w h => z.val)) hpair
    change s(d.crossingBond.source,d.crossingBond.target) = s(x.val,y.val) at hcoords
    refine ⟨d,hclosed,?_⟩
    rcases Sym2.eq_iff.mp hcoords with ⟨hs,ht⟩ | ⟨hs,ht⟩
    · exact Or.inl ⟨hs.symm,ht.symm⟩
    · exact Or.inr ⟨ht.symm,hs.symm⟩

/-- Every retained dual walk of the literal reference sample becomes an
actual sampled dual walk of the restored primal sample, with exact support. -/
theorem frozenReferenceDualSample_walk_sampled (a : LatticeVertex) (w h : ℕ)
    (R : Configuration (rectangleGraph a w h)) (A : RemainingConfiguration (rectangleGraph a w h) R)
    {s t : RectangleDualVertex a w h}
    (p : (openGraph _ (frozenReferenceDualSample a w h R A)).Walk s t) :
    ∃ q : (PlanarTopology.rectangleSampledClosedDualGraph a w h (A.val ∪ R)).Walk s.val t.val,
      q.support = p.support.map Subtype.val := by
  let p' := p.mapLe (frozenReferenceDualSample_openGraph a w h R A).le
  refine ⟨p'.map (rectanglePrimalDualOpenToSampled a w h (A.val ∪ R)),?_⟩
  have hm : (p'.map (rectanglePrimalDualOpenToSampled a w h (A.val ∪ R))).support =
      p'.support.map Subtype.val :=
    SimpleGraph.Walk.support_map (rectanglePrimalDualOpenToSampled a w h (A.val ∪ R)) p'
  have hp' : p'.support = p.support :=
    SimpleGraph.Walk.support_mapLe_eq_support (frozenReferenceDualSample_openGraph a w h R A).le p
  exact hm.trans (congrArg (fun l : List (RectangleDualVertex a w h) => l.map Subtype.val) hp')

end
end PottsContinuity.Thm3.Prop4
