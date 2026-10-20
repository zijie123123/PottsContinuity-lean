module

public import PottsContinuity.Thm3.RSW.StripCentralRead
public import PottsContinuity.PD.Duality.RectangleDualAmbient

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality
noncomputable section
local instance stripReflectedCentralDualEdgeEq (n k : ℕ) :
    DecidableEq (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).edgeSet := Classical.decEq _

/-- The inverse physical reflection sends the face base (x,y) to
(x,2n-1-y), including the source extra bottom row. -/
def stripReflectedCentralDualEmbedding (n k : ℕ) (hn : 1 ≤ n) :
    RectangleDualVertex (-(k:ℤ)*n,0) (2*k*n) (2*n) ↪ stripVertices n where
  toFun v := ⟨(v.val.1,2*(n:ℤ)-1-v.val.2),by
    have hv : v.val ∈ PD.FK.latticeRectangle (-(k:ℤ)*n-1,-1) (2*k*n+1) (2*n+1) := v.property
    rw [mem_latticeRectangle] at hv
    change -(n:ℤ) ≤ 2*(n:ℤ)-1-v.val.2 ∧ 2*(n:ℤ)-1-v.val.2 ≤ 3*(n:ℤ)
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hv
    constructor <;> omega⟩
  inj' := by
    intro u v huv
    have hx := congrArg (fun z : stripVertices n => z.val.1) huv
    have hy := congrArg (fun z : stripVertices n => z.val.2) huv
    apply Subtype.ext
    exact Prod.ext hx (by dsimp at hy; omega)

/-- Each reflected actual finite dual edge is a physical strip bond. -/
theorem stripReflectedCentralDual_map_le (n k : ℕ) (hn : 1 ≤ n) :
    (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).map
      (stripReflectedCentralDualEmbedding n k hn) ≤ stripGraph n := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  have h := rectangleDualGraph_le_ambient (-(k:ℤ)*n,0) (2*k*n) (2*n) huv
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 at h
  change |u.val.1-v.val.1|+|(2*(n:ℤ)-1-u.val.2)-(2*(n:ℤ)-1-v.val.2)|=1
  have he : (2*(n:ℤ)-1-u.val.2)-(2*(n:ℤ)-1-v.val.2) = -(u.val.2-v.val.2) := by ring
  rw [he,abs_neg]
  exact h

/-- Read precisely the reflected primal bonds on the actual finite dual carrier. -/
def stripReflectedCentralDualConfiguration (n k : ℕ) (hn : 1 ≤ n)
    (ω : StripConfiguration n) :
    Configuration (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)) :=
  boolConfigurationEquiv _ (fun e => ω (embeddedEdgeEmbedding _ _
    (stripReflectedCentralDualEmbedding n k hn) (stripReflectedCentralDual_map_le n k hn) e))

/-- Every sampled edge of the reflected read maps to the SAME open strip bond. -/
def stripReflectedCentralDualOpenHom (n k : ℕ) (hn : 1 ≤ n) (ω : StripConfiguration n) :
    openGraph (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n))
      (stripReflectedCentralDualConfiguration n k hn ω) →g stripOpenGraph n ω where
  toFun := stripReflectedCentralDualEmbedding n k hn
  map_rel' := by
    classical
    intro u v huv
    rw [stripReflectedCentralDualConfiguration,openGraph_boolConfigurationEquiv] at huv
    obtain ⟨⟨hg,hs⟩,hne⟩ := huv
    rw [stripOpenGraph,SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨?_,?_⟩,(stripReflectedCentralDualEmbedding n k hn).injective.ne hne⟩
    · exact (stripGraph n).mem_edgeSet.mpr
        (stripReflectedCentralDual_map_le n k hn ((SimpleGraph.map_adj _ _ _ _).mpr ⟨u,v,
          (rectangleDualGraph (-(k:ℤ)*n,0) (2*k*n) (2*n)).mem_edgeSet.mp hg,rfl,rfl⟩))
    · exact hs

end
end PottsContinuity.RSW
