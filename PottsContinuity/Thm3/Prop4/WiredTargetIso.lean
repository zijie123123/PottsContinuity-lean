module

public import PottsContinuity.Thm3.Prop4.WiredTargetComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-! # Exact wired-target probability under a genuine graph isomorphism -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section

/-- Relabeling an actual graph preserves the whole root-to-wired-target probability. -/
theorem wired_target_probability_iso {V U : Type*} [Finite V] [Finite U]
    {G : SimpleGraph V} {H : SimpleGraph U} (e : G ≃g H)
    (θ : Parameters) (W : Set U) (x : V) :
    (measure G θ (BoundaryCondition.wired (e ⁻¹' W))
      (targetConnectionEvent x (e ⁻¹' W))).toReal =
    (measure H θ (BoundaryCondition.wired W) (targetConnectionEvent (e x) W)).toReal := by
  let f := e.toEquiv.toEmbedding
  let g := e.symm.toEquiv.toEmbedding
  have hf : G.map f ≤ H := by
    intro a b hab
    obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj f G a b).mp hab
    exact e.map_adj_iff.mpr huv
  have hg : H.map g ≤ G := by
    intro a b hab
    obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj g H a b).mp hab
    exact e.symm.map_adj_iff.mpr huv
  have hforward := embedded_wired_target_probability_le G H f hf θ W x
  have hback := embedded_wired_target_probability_le H G g hg θ (e ⁻¹' W) (e x)
  have hset : g ⁻¹' (e ⁻¹' W) = W := by
    ext u
    change e (e.symm u) ∈ W ↔ u ∈ W
    rw [e.apply_symm_apply]
  rw [hset] at hback
  have hroot : g (e x) = x := e.symm_apply_apply x
  rw [hroot] at hback
  exact le_antisymm hforward hback

end
end PottsContinuity.Thm3.Prop4
