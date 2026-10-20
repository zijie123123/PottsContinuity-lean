module

public import PottsContinuity.Thm3.RSW.StripPrunedTopPorts

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section

/-- Physical reflection of the complete asymmetric strip rectangle into the
host dual face bases. Its image omits exactly the expanded top-port row. -/
def stripReflectedAsymmetricEmbedding (n M : ℕ) :
    RectangleVertex (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n) ↪
      RectangleDualVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) where
  toFun v := ⟨(v.val.1,2*(n:ℤ)-1-v.val.2),by
    have hv := (mem_latticeRectangle _ _ _ _).mp v.property
    change (v.val.1,2*(n:ℤ)-1-v.val.2) ∈
      PD.FK.latticeRectangle (-(M:ℤ)-1,-(n:ℤ)-1) (2*M+1) (4*n+1)
    rw [mem_latticeRectangle]
    push_cast at hv ⊢
    constructor <;> constructor <;> omega⟩
  inj' := by
    intro u v h
    have hx := congrArg (fun z => z.val.1) h
    have hy := congrArg (fun z => z.val.2) h
    apply Subtype.ext
    apply Prod.ext
    · exact hx
    · dsimp at hy
      omega

/-- Every embedded face stays strictly below the expanded top-port row. -/
theorem stripReflectedAsymmetricEmbedding_not_top (n M : ℕ)
    (v : RectangleVertex (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)) :
    (stripReflectedAsymmetricEmbedding n M v).val.2 ≠ 3*(n:ℤ) := by
  have hv := (mem_latticeRectangle _ _ _ _).mp v.property
  change 2*(n:ℤ)-1-v.val.2 ≠ 3*(n:ℤ)
  omega

/-- Exactly the non-top-port face vertices have a physical inverse in the
complete asymmetric rectangle. No interior or side vertex is omitted. -/
theorem stripReflectedAsymmetricEmbedding_range (n M : ℕ)
    (u : RectangleDualVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)) :
    u ∈ Set.range (stripReflectedAsymmetricEmbedding n M) ↔ u.val.2 ≠ 3*(n:ℤ) := by
  constructor
  · rintro ⟨v,rfl⟩
    exact stripReflectedAsymmetricEmbedding_not_top n M v
  · intro hu
    have hv : u.val ∈ PD.FK.latticeRectangle (-(M:ℤ)-1,-(n:ℤ)-1) (2*M+1) (4*n+1) := u.property
    rw [mem_latticeRectangle] at hv
    refine ⟨⟨(u.val.1,2*(n:ℤ)-1-u.val.2),?_⟩,?_⟩
    · rw [mem_latticeRectangle]
      push_cast at hv ⊢
      constructor <;> constructor <;> omega
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(n:ℤ)-1-(2*(n:ℤ)-1-u.val.2)=u.val.2
        ring

/-- Physical reflection preserves precisely the actual nearest-neighbor
adjacency in the ambient dual lattice. -/
theorem stripReflectedAsymmetricEmbedding_adj_iff (n M : ℕ)
    (u v : RectangleVertex (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)) :
    (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)).Adj u v ↔
      (rectangleDualAmbientGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).Adj
        (stripReflectedAsymmetricEmbedding n M u) (stripReflectedAsymmetricEmbedding n M v) := by
  change |u.val.1-v.val.1|+|u.val.2-v.val.2|=1 ↔
    |u.val.1-v.val.1|+|(2*(n:ℤ)-1-u.val.2)-(2*(n:ℤ)-1-v.val.2)|=1
  have heq : (2*(n:ℤ)-1-u.val.2)-(2*(n:ℤ)-1-v.val.2)= -(u.val.2-v.val.2) := by ring
  rw [heq,abs_neg]

/-- The complete reflected asymmetric graph lies in the actual dual ambient
lattice, with its full original support. -/
theorem stripReflectedAsymmetric_map_le_ambient (n M : ℕ) :
    (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)).map
      (stripReflectedAsymmetricEmbedding n M) ≤
    rectangleDualAmbientGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n) := by
  intro u v hadj
  rcases (SimpleGraph.map_adj _ _ _ _).mp hadj with ⟨x,y,hxy,rfl,rfl⟩
  exact (stripReflectedAsymmetricEmbedding_adj_iff n M x y).mp hxy

/-- Every retained actual dual edge lies in this reflected complete rectangle.
This is an actual physical graph inclusion, not a completed path assertion. -/
theorem stripPrunedDual_le_reflectedAsymmetric (n M : ℕ) :
    rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M) ≤
    (rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)).map
      (stripReflectedAsymmetricEmbedding n M) := by
  intro u v hadj
  obtain ⟨hfull,hu,hv⟩ := (stripPrunedDual_adj_iff_not_top n M u v).mp hadj
  obtain ⟨x,rfl⟩ := (stripReflectedAsymmetricEmbedding_range n M u).mpr hu
  obtain ⟨y,rfl⟩ := (stripReflectedAsymmetricEmbedding_range n M v).mpr hv
  apply (SimpleGraph.map_adj _ _ _ _).mpr
  exact ⟨x,y,(stripReflectedAsymmetricEmbedding_adj_iff n M x y).mpr
    (rectangleDualGraph_le_ambient _ _ _ hfull),rfl,rfl⟩

/-- Additional rectangle bonds join only vertices already in the actual host
exterior class, so their FK omission is covered by prewired-edge marginality. -/
theorem stripReflectedAsymmetric_extra_edge_prewired (n M : ℕ)
    (u v : RectangleDualVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n))
    (hadj : ((rectangleGraph (-(M:ℤ)-1,-(n:ℤ)) (2*M+1) (4*n)).map
      (stripReflectedAsymmetricEmbedding n M)).Adj u v)
    (hnot : ¬ (rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)).Adj u v) :
    (rectangleDualBoundaryCondition (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).partition.r u v := by
  have hambient := stripReflectedAsymmetric_map_le_ambient n M hadj
  rcases (SimpleGraph.map_adj _ _ _ _).mp hadj with ⟨x,y,hxy,rfl,rfl⟩
  have hnotfull : ¬ (rectangleDualGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)).Adj
      (stripReflectedAsymmetricEmbedding n M x) (stripReflectedAsymmetricEmbedding n M y) := by
    intro hfull
    exact hnot ((stripPrunedDual_adj_iff_not_top n M _ _).mpr
      ⟨hfull,stripReflectedAsymmetricEmbedding_not_top n M x,
        stripReflectedAsymmetricEmbedding_not_top n M y⟩)
  rw [rectangleDualBoundaryCondition_rel]
  exact Or.inr (rectangleDualAmbient_extraEdge_endpoints_boundary _ _ _ _ _ hambient hnotfull)

end
end PottsContinuity.RSW
