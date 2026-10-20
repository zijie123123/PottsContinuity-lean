module

public import PottsContinuity.Thm4Side.RevealConditionedHost
public import PottsContinuity.Thm4Side.SideExactLawSpecialization

@[expose] public section

namespace PottsContinuity.PlanarMixed.Thm4SideFactor
open PD.FK Thm4Side
noncomputable section

/-- Open auxiliary-state edges have no endpoint outside the original slit box. -/
theorem auxiliary_open_endpoint_mem_original (n : ℕ)
    (A : Configuration (FKC.FiniteFK.slitBoxGraph n))
    (e : (sideExactLawHostGraph n).edgeSet)
    (he : e ∈ slitBoxAuxiliaryArcRing n ∪ slitBoxAuxiliaryMapConfiguration n A)
    (z : sideExactLawHostVertex n) (hz : z ∈ e.val) :
    z.val ∈ FKC.latticeRectangle (-(n:ℤ),-(n:ℤ)) (2*n) (2*n) := by
  classical
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨u,v,hu,hv,hpair⟩ := (mem_slitBoxAuxiliaryArcRing_iff n e).mp he
    rw [hpair] at hz
    rcases (Sym2.mem_iff').mp hz with rfl | rfl
    · obtain ⟨a,ha,rfl⟩ := hu
      exact a.property
    · obtain ⟨a,ha,rfl⟩ := hv
      exact a.property
  · obtain ⟨c,hc,hce⟩ := Finset.mem_map.mp he
    have hp := congrArg Subtype.val hce
    have hz' : z ∈ Sym2.map (slitBoxAuxiliaryHostEmbedding n) c.val := by
      rw [← hp] at hz
      exact hz
    obtain ⟨a,ha,haz⟩ := Sym2.mem_map.mp hz'
    rw [← haz]
    exact a.property

/-- The right host exterior assigns closed state to every bond leaving the original box. -/
theorem right_removed_open_endpoint_mem_original (m : ℕ)
    (X : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (e : (sideExactLawHostGraph (16*m)).edgeSet)
    (he : e ∈ (slitRightDualRectangleHostRemovedState m X).val)
    (z : sideExactLawHostVertex (16*m)) (hz : z ∈ e.val) :
    z.val ∈ FKC.latticeRectangle (-((16*m:ℕ):ℤ),-((16*m:ℕ):ℤ))
      (2*(16*m)) (2*(16*m)) :=
  auxiliary_open_endpoint_mem_original (16*m)
    (Exploration.revealRecordConfiguration (slitRightDualRectangleReveal m) X).val e (by simpa only [slitRightDualRectangleHostRemovedState, Finset.mem_union] using he) z hz

/-- An edge of the embedded active source has only original-box endpoints. -/
theorem sideHost_mapped_endpoint_original (m : ℕ)
    (R : Configuration (FKC.FiniteFK.slitBoxGraph (16*m)))
    (c : (sideExactLawHostGraph (16*m)).edgeSet)
    (hc : c.val ∈ ((DualityExt.positiveActiveGraph (sideExactLawResidual m R)).map
      (sideExactLawHostEmbedding m R)).edgeSet)
    (z : sideExactLawHostVertex (16*m)) (hz : z ∈ c.val) :
    z.val ∈ FKC.latticeRectangle (-((16*m:ℕ):ℤ),-((16*m:ℕ):ℤ))
      (2*(16*m)) (2*(16*m)) := by
  rw [SimpleGraph.edgeSet_map] at hc
  obtain ⟨d,hd,hdc⟩ := hc
  rw [← hdc] at hz
  obtain ⟨u,hu,huz⟩ := Sym2.mem_map.mp hz
  rw [← huz]
  exact u.val.property

end
end PottsContinuity.PlanarMixed.Thm4SideFactor
