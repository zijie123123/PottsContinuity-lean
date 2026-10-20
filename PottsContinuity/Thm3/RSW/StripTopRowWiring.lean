module

public import PottsContinuity.Thm3.RSW.StripWindow
public import PottsContinuity.PD.FK.DomainMarkov

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section
local instance stripTopRowEdgeFintype (n M : ℕ) :
    Fintype (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet := Fintype.ofFinite _

/-- The actual original top-row bonds, all opened as a finite boundary
state. The definition adds no virtual edge or exterior vertex. -/
def stripTopRowState (n M : ℕ) :
    Configuration (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))) := by
  classical
  exact Finset.univ.filter (fun e => ∀ v ∈ e.val, v ∈ stripWindowWiredVertices n M 0)

def topVertex (n M j : ℕ) (hj : j ≤ 2*M) : (stripWindow n M : Set (ℤ×ℤ)) :=
  ⟨((j:ℤ)-(M:ℤ),3*(n:ℤ)),by
    change ((j:ℤ)-(M:ℤ),3*(n:ℤ)) ∈ stripWindow n M
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc]
    constructor <;> constructor <;> omega⟩

private theorem topVertex_connected_zero (n M j : ℕ) (hj : j ≤ 2*M) :
    ActualConnected (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))
      (stripTopRowState n M) (topVertex n M 0 (by omega)) (topVertex n M j hj) := by
  classical
  induction j with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ j ih =>
    have hj' : j ≤ 2*M := by omega
    apply (ih hj').trans
    apply actualConnected_of_adj
    rw [openGraph_adj]
    have hadj : (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).Adj
        (topVertex n M j hj') (topVertex n M (j+1) hj) := by
      change |((j:ℤ)-(M:ℤ))-(((j+1:ℕ):ℤ)-(M:ℤ))|+|3*(n:ℤ)-3*(n:ℤ)|=1
      push_cast
      have heq : ((j:ℤ)-(M:ℤ))-((j:ℤ)+1-(M:ℤ))= -1 := by ring
      rw [heq,sub_self,abs_zero]
      norm_num
    refine ⟨⟨s(topVertex n M j hj',topVertex n M (j+1) hj),
      (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).mem_edgeSet.mpr hadj⟩,?_,rfl⟩
    change (⟨s(topVertex n M j hj',topVertex n M (j+1) hj),
      (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).mem_edgeSet.mpr hadj⟩ :
      (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ))).edgeSet) ∈ stripTopRowState n M
    simp only [stripTopRowState,Finset.mem_filter,Finset.mem_univ,true_and]
    intro v hv
    rcases Sym2.mem_iff'.mp hv with rfl | rfl <;>
      exact Or.inl rfl

/-- Every pair of actual top-row vertices is connected by the selected
original row bonds, including zero-width and zero-height windows. -/
theorem stripTopRowState_connects_top (n M : ℕ)
    (u v : (stripWindow n M : Set (ℤ×ℤ)))
    (hu : u ∈ stripWindowWiredVertices n M 0) (hv : v ∈ stripWindowWiredVertices n M 0) :
    ActualConnected (squareLattice.induce (stripWindow n M : Set (ℤ×ℤ)))
      (stripTopRowState n M) u v := by
  have hux : -(M:ℤ) ≤ u.val.1 ∧ u.val.1 ≤ M := by
    have h := u.property
    change u.val ∈ stripWindow n M at h
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc] at h
    exact h.1
  have hvx : -(M:ℤ) ≤ v.val.1 ∧ v.val.1 ≤ M := by
    have h := v.property
    change v.val ∈ stripWindow n M at h
    simp only [stripWindow,PottsContinuity.latticeRectangle,Finset.mem_product,Finset.mem_Icc] at h
    exact h.1
  have huy : u.val.2=3*(n:ℤ) := by simpa [stripWindowWiredVertices] using hu
  have hvy : v.val.2=3*(n:ℤ) := by simpa [stripWindowWiredVertices] using hv
  let j := (u.val.1+(M:ℤ)).toNat
  let k := (v.val.1+(M:ℤ)).toNat
  have hj : j ≤ 2*M := by dsimp [j]; omega
  have hk : k ≤ 2*M := by dsimp [k]; omega
  have hju : topVertex n M j hj=u := by
    apply Subtype.ext; apply Prod.ext
    · dsimp [topVertex,j]; omega
    · exact huy.symm
  have hkv : topVertex n M k hk=v := by
    apply Subtype.ext; apply Prod.ext
    · dsimp [topVertex,k]; omega
    · exact hvy.symm
  rw [← hju,← hkv]
  exact (topVertex_connected_zero n M j hj).symm.trans (topVertex_connected_zero n M k hk)

/-- Freezing precisely the actual top-row bonds open induces exactly the
source top-only partition. This is a finite combinatorial identity. -/
theorem stripTopRowState_frozen_partition (n M : ℕ) :
    (frozenBoundary (BoundaryCondition.free ∅) (stripTopRowState n M)).partition =
      (stripWindowBoundary n M 0).partition := by
  classical
  change componentSetoid _ (BoundaryCondition.free ∅) (stripTopRowState n M) = _
  rw [componentSetoid_free]
  apply le_antisymm
  · apply reachableSetoid_le_of_adj
    intro u v huv
    rw [openGraph_adj] at huv
    obtain ⟨e,he,heq⟩ := huv
    have hs := (Finset.mem_filter.mp he).2
    have hu := hs u (by rw [heq]; simp)
    have hv := hs v (by rw [heq]; simp)
    exact Or.inr ⟨hu,hv⟩
  · intro u v huv
    change u=v ∨ u ∈ stripWindowWiredVertices n M 0 ∧ v ∈ stripWindowWiredVertices n M 0 at huv
    rcases huv with rfl | ⟨hu,hv⟩
    · exact SimpleGraph.Reachable.refl _
    · exact stripTopRowState_connects_top n M u v hu hv

end
end PottsContinuity.RSW
