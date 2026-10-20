module

public import PottsContinuity.Thm3.RSW.StripTopRowEdgeRead

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK PD.Duality DualityExt
noncomputable section

section
variable (n M : ℕ)
local notation "Frame" => rectangleGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)
local notation "Dual" => rectangleDualGraph (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)
local notation "Face" => RectangleDualVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)
local notation "pruned" => rectangleSubgraphDualGraph (stripRectangleWithoutTop_map_le n M)
local notation "R" => stripRectangleTopRowState n M
local notation "Rstar" => rectangleSubgraphRemovedDualEdges (stripRectangleWithoutTop_map_le n M)
local notation "edgeMap" => rectangleDualEdgeEquiv (-(M:ℤ),-(n:ℤ)) (2*M) (4*n)

/-- The omitted dual bonds are exactly those crossing original top-row bonds. -/
theorem stripPruned_removedDualEdges_eq : Rstar=(R).map (edgeMap).toEmbedding := by
  unfold rectangleSubgraphRemovedDualEdges
  have hmap : (stripRectangleWithoutTopGraph n M).map
      (Function.Embedding.refl (RectangleVertex (-(M:ℤ),-(n:ℤ)) (2*M) (4*n))) =
      stripRectangleWithoutTopGraph n M := by
    ext u v
    simp only [SimpleGraph.map_adj,Function.Embedding.refl_apply]
    constructor
    · rintro ⟨x,y,hxy,rfl,rfl⟩
      exact hxy
    · intro h
      exact ⟨u,v,h,rfl,rfl⟩
  rw [hmap,stripRectangleWithoutTop_removedEdges]

private theorem removed_pair_iff_top (u v : Face) (hadj : (Dual).Adj u v) :
    s(u,v) ∈ openEdges Dual Rstar ↔ u.val.2=3*(n:ℤ) ∨ v.val.2=3*(n:ℤ) := by
  classical
  obtain ⟨e,he⟩ := (rectangleDualGraph_adj_iff _ _ _ u v).mp hadj
  let prim : (Frame).edgeSet := e.primalEdge
  have hval : (edgeMap prim).val=s(u,v) := by
    have hei : rectanglePrimalDualEdgeEquiv _ _ _ prim=e :=
      (rectanglePrimalDualEdgeEquiv _ _ _).apply_symm_apply e
    change (rectangleDualGraphEdgeEquiv _ _ _ (rectanglePrimalDualEdgeEquiv _ _ _ prim)).val=s(u,v)
    rw [hei]
    exact he.symm
  have hmem : s(u,v) ∈ openEdges Dual Rstar ↔ prim ∈ R := by
    rw [← hval,coe_mem_openEdges_iff,stripPruned_removedDualEdges_eq]
    constructor
    · intro h
      obtain ⟨f,hf,hfe⟩ := Finset.mem_map.mp h
      have hfe' := (edgeMap).injective hfe
      simpa only [hfe'] using hf
    · intro h
      exact Finset.mem_map.mpr ⟨prim,h,rfl⟩
  rw [hmem]
  change prim ∈ stripRectangleTopRowState n M ↔ _
  rw [mem_stripRectangleTopRowState_iff]
  have hheight : -(n:ℤ)+((4*n:ℕ):ℤ)=3*(n:ℤ) := by push_cast; ring
  constructor
  · intro h
    have h' : ∀ z ∈ prim.val, z.val.2= -(n:ℤ)+((4*n:ℕ):ℤ) := by
      simpa only [hheight] using h
    simpa only [hheight] using rectangleDual_top_row_crosses_top_port _ _ _ u v e he h'
  · rintro (hu | hv)
    · have harg : u.val.2= -(n:ℤ)+((4*n:ℕ):ℤ) := by simpa only [hheight] using hu
      have ht := rectangleDual_top_port_crosses_top_row _ _ _ u v e he harg
      simpa only [prim,hheight] using ht
    · have he' : s(v,u)=rectangleDualCarrierPair _ _ _ e :=
        (Sym2.eq_swap : s(v,u)=s(u,v)).trans he
      have harg : v.val.2= -(n:ℤ)+((4*n:ℕ):ℤ) := by simpa only [hheight] using hv
      have ht := rectangleDual_top_port_crosses_top_row _ _ _ v u e he' harg
      simpa only [prim,hheight] using ht

/-- Precisely the actual dual top-port incidence is deleted. The remaining
full host dual edges keep their original endpoints and states. -/
theorem stripPrunedDual_adj_iff_not_top (u v : Face) :
    (pruned).Adj u v ↔ (Dual).Adj u v ∧ u.val.2 ≠ 3*(n:ℤ) ∧ v.val.2 ≠ 3*(n:ℤ) := by
  change ((Dual).deleteEdges (openEdges Dual Rstar)).Adj u v ↔ _
  rw [SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨hadj,hnot⟩
    have hh := mt (removed_pair_iff_top n M u v hadj).mpr hnot
    exact ⟨hadj,(not_or.mp hh).1,(not_or.mp hh).2⟩
  · rintro ⟨hadj,hu,hv⟩
    refine ⟨hadj,?_⟩
    intro h
    exact (not_or.mpr ⟨hu,hv⟩) ((removed_pair_iff_top n M u v hadj).mp h)

end
end
end PottsContinuity.RSW
