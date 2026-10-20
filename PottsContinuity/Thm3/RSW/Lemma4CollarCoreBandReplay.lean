module

public import PottsContinuity.Thm3.RSW.BottomCollarCoreMarginal
public import PottsContinuity.Thm3.RSW.Lemma4NativeDualBand
public import PottsContinuity.Thm3.RSW.EmbeddedPath
public import PottsContinuity.Thm3.Push.BottomCoreBandTransfer

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality PlanarMixed.Square
noncomputable section

/-- Every sampled retained-core band crossing is a native crossing of the
actual residual collar graph, with literal face endpoints and full support. -/
theorem lemma4_coreBand_replays_native (n : ℕ) (hn : 1 ≤ n)
    (D : Configuration (bottomCollarInducedDualGraph (-56*(n:ℤ),0) (112*n) (54*n)))
    (hD : bottomCollarCoreRestriction (-56*(n:ℤ),0) (112*n) (54*n) D ∈
      Push.bottomCoreBandEvent (-56*(n:ℤ),0) (112*n) (54*n) (n-1)) :
    D ∈ lemma4NativeDualBandEvent n := by
  let a : LatticeVertex := (-56*(n:ℤ),0)
  let C := embeddedConfigurationRestriction (rectangleDualGraph a (112*n) (54*n))
    (bottomCollarInducedDualGraph a (112*n) (54*n))
    (generalRectangleDualBottomCollar_vertexEmbedding a (112*n) (54*n))
    (bottomCollar_inner_map_le a (112*n) (54*n)) D
  let φ₀ := embeddedRestrictionOpenHom (rectangleDualGraph a (112*n) (54*n))
    (bottomCollarInducedDualGraph a (112*n) (54*n))
    (generalRectangleDualBottomCollar_vertexEmbedding a (112*n) (54*n))
    (bottomCollar_inner_map_le a (112*n) (54*n)) D
  let φ₁ := embeddedRestrictionOpenHom (generalRectangleDualBottomCoreGraph a (112*n) (54*n))
    (rectangleDualGraph a (112*n) (54*n)) (Push.bottomCoreInclusion a (112*n) (54*n))
    (Push.bottomCoreGraph_map_le a (112*n) (54*n)) C
  let φ := φ₀.comp φ₁
  obtain ⟨u,v,p,hu,hv,hp⟩ := hD
  refine ⟨φ u,φ v,p.map φ,hu,?_,?_⟩
  · change v.val.val.1 = 56*(n:ℤ)
    change v.val.val.1 = -56*(n:ℤ) + ((112*n:ℕ):ℤ) at hv
    push_cast at hv
    omega
  · intro z hz
    have hs := SimpleGraph.Walk.support_map φ p
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (Eq.mp (congrArg (fun L => z ∈ L) hs) hz)
    have hb := hp x hx
    have hc := x.val.property
    change x.val.val ∈ PD.FK.latticeRectangle
      (-56*(n:ℤ)-1,-1) (112*n+1) (54*n+1) at hc
    rw [mem_latticeRectangle] at hc
    change -56*(n:ℤ)-1 ≤ x.val.val.1 ∧ x.val.val.1 ≤ 56*(n:ℤ) ∧
      0 ≤ x.val.val.2 ∧ x.val.val.2 ≤ (n:ℤ)-1
    change 0 ≤ x.val.val.2 ∧ x.val.val.2 ≤ 0+((n-1:ℕ):ℤ) at hb
    push_cast at hc
    omega

end
end PottsContinuity.RSW
