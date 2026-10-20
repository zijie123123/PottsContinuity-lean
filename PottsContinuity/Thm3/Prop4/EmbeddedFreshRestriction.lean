module

public import PottsContinuity.Thm3.Prop4.RawCentralReplayRetention

/-! # Literal restriction to any embedded graph of fresh original bonds -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK Push
noncomputable section
local instance embeddedFreshOriginalEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _
local instance embeddedFreshRemainingEq {V : Type*} (G : SimpleGraph V) (R : Configuration G) :
    DecidableEq (edgeRestriction G R).edgeSet := Classical.decEq _

/-- Reading fresh embedded original bonds directly agrees exactly with
first deleting the queried bonds and reading the resulting graph. -/
theorem embeddedFreshRestriction_eq_remaining
    {V W : Type*} [Finite V] [Finite W] (G : SimpleGraph V) (R : Configuration G)
    (H : SimpleGraph W) (f : W ↪ V) (hHM : H.map f ≤ edgeRestriction G R)
    (B : Configuration G) :
    embeddedConfigurationRestriction H G f (hHM.trans (edgeRestriction_le G R)) B =
      embeddedConfigurationRestriction H (edgeRestriction G R) f hHM
        ((edgeRestrictionConfigurationEquiv G R).symm ((configurationSplitEquiv G R B).1)) := by
  classical
  let C : Configuration (edgeRestriction G R) :=
    (edgeRestrictionConfigurationEquiv G R).symm ((configurationSplitEquiv G R B).1)
  have hs : (edgeRestrictionConfigurationEquiv G R C).val = B \ R := by
    rw [show C = (edgeRestrictionConfigurationEquiv G R).symm ((configurationSplitEquiv G R B).1) from rfl,
      Equiv.apply_symm_apply]
    rfl
  have hsmap : C.map (edgeRestrictionEdgeEmbedding G R) = B \ R :=
    (edgeRestrictionConfigurationEquiv_val G R _).symm.trans hs
  ext e
  let er := embeddedEdgeEmbedding H (edgeRestriction G R) f hHM e
  let eo := embeddedEdgeEmbedding H G f (hHM.trans (edgeRestriction_le G R)) e
  have heo : edgeRestrictionEdgeEmbedding G R er = eo := by
    apply Subtype.ext
    rfl
  have hn : eo ∉ R := by
    have heR := (edgeRestrictionEdgeEquiv G R er).property
    exact heo ▸ heR
  rw [mem_embeddedConfigurationRestriction,mem_embeddedConfigurationRestriction]
  change eo ∈ B ↔ er ∈ C
  have hm : er ∈ C ↔ eo ∈ B \ R := by
    rw [← hsmap,Finset.mem_map]
    constructor
    · intro he
      exact ⟨er,he,heo⟩
    · rintro ⟨d,hd,hde⟩
      have hd' : d = er := (edgeRestrictionEdgeEmbedding G R).injective (hde.trans heo.symm)
      exact hd' ▸ hd
  rw [hm,Finset.mem_sdiff]
  exact ⟨fun he => ⟨he,hn⟩,fun he => he.1⟩

end
end PottsContinuity.Thm3.Prop4
