module

public import PottsContinuity.Thm3.RSW.EmbeddedPath
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Actual edge extension from induced vertex regions

These maps retain the sampled original bonds and close every other bond.
They will be used for increasing events with cluster-confined witnesses.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section
variable {V : Type*} {G : SimpleGraph V}

/-- The literal vertex inclusion of an induced region. -/
def inducedVertexEmbedding (W : Set V) : W ↪ V := ⟨Subtype.val, Subtype.val_injective⟩

/-- The induced graph embeds into its ambient graph. -/
theorem inducedVertexEmbedding_map_le (W : Set V) :
    (G.induce W).map (inducedVertexEmbedding W) ≤ G := by
  intro a b hab
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ a b).mp hab
  exact huv

/-- Extend a sampled induced configuration by closed bonds. -/
def inducedConfigurationExtension (W : Set V) : Configuration (G.induce W) ↪ Configuration G :=
  embeddedConfigurationEmbedding (G.induce W) G (inducedVertexEmbedding W)
    (inducedVertexEmbedding_map_le W)

/-- Restrict to the actual bonds with both endpoints in W. -/
def inducedConfigurationRestriction (W : Set V) (A : Configuration G) :
    Configuration (G.induce W) :=
  embeddedConfigurationRestriction (G.induce W) G (inducedVertexEmbedding W)
    (inducedVertexEmbedding_map_le W) A

/-- Close all bonds outside the induced region, retaining the original carrier. -/
def inducedConfigurationErasure (W : Set V) (A : Configuration G) : Configuration G :=
  inducedConfigurationExtension W (inducedConfigurationRestriction W A)

/-- Extending a restriction only deletes sampled edges. -/
theorem inducedConfigurationErasure_subset (W : Set V) (A : Configuration G) :
    inducedConfigurationErasure W A ⊆ A :=
  embeddedConfigurationEmbedding_restriction_subset _ _ _ _ A

/-- Extension preserves the actual edge inclusion order. -/
theorem inducedConfigurationExtension_monotone (W : Set V) :
    Monotone (inducedConfigurationExtension (G := G) W) := by
  intro A B hAB
  change embeddedConfigurationEmbedding _ _ _ _ A ⊆ embeddedConfigurationEmbedding _ _ _ _ B
  simp only [embeddedConfigurationEmbedding_eq_map]
  exact Finset.map_subset_map.mpr hAB

/-- Any sampled edge whose two endpoints lie in W survives this erasure. -/
theorem mem_inducedConfigurationErasure (W : Set V) (A : Configuration G)
    (e : G.edgeSet) :
    e ∈ inducedConfigurationErasure W A ↔ e ∈ A ∧ ∀ v ∈ e.val, v ∈ W := by
  classical
  constructor
  · intro he
    refine ⟨inducedConfigurationErasure_subset W A he, ?_⟩
    change e ∈ embeddedConfigurationEmbedding _ _ _ _ _ at he
    rw [embeddedConfigurationEmbedding_eq_map] at he
    obtain ⟨d, _, rfl⟩ := Finset.mem_map.mp he
    intro v hv
    rw [embeddedEdgeEmbedding_coe] at hv
    change v ∈ Sym2.map (inducedVertexEmbedding W) d.val at hv
    rw [Sym2.mem_map] at hv
    obtain ⟨u, _, rfl⟩ := hv
    exact u.property
  · rintro ⟨he, hW⟩
    obtain ⟨⟨a,b⟩, hrep⟩ := Quot.exists_rep e.val
    have hab : e.val = s(a,b) := hrep.symm
    have hadj : G.Adj a b := G.mem_edgeSet.mp (hab ▸ e.property)
    have ha : a ∈ W := hW a (by simp [hab])
    have hb : b ∈ W := hW b (by simp [hab])
    let d : (G.induce W).edgeSet := ⟨s(⟨a,ha⟩,⟨b,hb⟩), hadj⟩
    have hd : embeddedEdgeEmbedding (G.induce W) G (inducedVertexEmbedding W)
        (inducedVertexEmbedding_map_le W) d = e := by
      apply Subtype.ext
      change s(a,b) = e.val
      exact hab.symm
    change e ∈ embeddedConfigurationEmbedding _ _ _ _ _
    rw [embeddedConfigurationEmbedding_eq_map]
    refine Finset.mem_map.mpr ⟨d, ?_, hd⟩
    change d ∈ embeddedConfigurationRestriction _ _ _ _ A
    rw [mem_embeddedConfigurationRestriction, hd]
    exact he

end
end PottsContinuity.RSW
