-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverRefinedCorridorAvoidance.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedCornerInterior
public import PottsContinuity.FKC.Medial.ParafermionicCoverRefinedPairingRoutes
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK

/-- The closed vertex rectangle reserved for the central corridor argument. -/
def parafermionicCoverRefinedCentralRectangle (z : ParafermionicCoverVertex) : Prop :=
  -2 ≤ z.1.1 ∧ z.1.1 ≤ 3 ∧ -3 ≤ z.1.2 ∧ z.1.2 ≤ 2

theorem parafermionicCoverRefinedPortEmbedding_avoidsCentralRectangle
    (c : ParafermionicCoverPort) (layer : Bool) :
    ¬ parafermionicCoverRefinedCentralRectangle
      (parafermionicCoverRefinedPortEmbedding (c, layer)) := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;> cases layer <;>
    simp [parafermionicCoverRefinedCentralRectangle,
      parafermionicCoverRefinedPortEmbedding_horizontal,
      parafermionicCoverRefinedPortEmbedding_vertical] <;> omega

theorem parafermionicCoverRefinedClosedCapMiddle_avoidsCentralRectangle
    (c : ParafermionicCoverPort) :
    ¬ parafermionicCoverRefinedCentralRectangle
      (parafermionicCoverRefinedClosedCapMiddle c) := by
  rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
  cases ax <;> cases tip <;> cases side <;>
    simp [parafermionicCoverRefinedCentralRectangle,
      parafermionicCoverRefinedClosedCapMiddle_horizontal,
      parafermionicCoverRefinedClosedCapMiddle_vertical] <;> omega

theorem parafermionicCoverRefinedCornerWalk_support_avoidsCentralRectangle
    (c : ParafermionicCoverPort) {z : ParafermionicCoverVertex}
    (hz : z ∈ (parafermionicCoverRefinedCornerWalk c).support) :
    ¬ parafermionicCoverRefinedCentralRectangle z := by
  rw [parafermionicCoverRefinedCornerWalk_support] at hz
  simp only [List.mem_cons] at hz
  rcases hz with h | h | h | h | h
  · subst z
    exact parafermionicCoverRefinedPortEmbedding_avoidsCentralRectangle c true
  · subst z
    rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCentralRectangle,
        parafermionicCoverRefinedCornerMid₁,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverCornerPair,
        parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        LatticePort.cornerPair,
        ] <;> omega
  · subst z
    rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCentralRectangle,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverCornerPair,
        parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        LatticePort.cornerPair,
        ] <;> omega
  · subst z
    rcases c with ⟨⟨⟨⟨x, y⟩, ax⟩, tip, side⟩, k⟩
    cases ax <;> cases tip <;> cases side <;>
      simp [parafermionicCoverRefinedCentralRectangle,
        parafermionicCoverRefinedCornerMid₂,
        parafermionicCoverRefinedCornerElbow,
        parafermionicCoverCornerPair,
        parafermionicCoverRefinedPortEmbedding_horizontal,
        parafermionicCoverRefinedPortEmbedding_vertical,
        LatticePort.cornerPair,
        ] <;> omega
  · rcases h with h | hnil
    · subst z
      exact parafermionicCoverRefinedPortEmbedding_avoidsCentralRectangle
        (parafermionicCoverCornerPair c) true
    · simp at hnil

theorem parafermionicCoverRefinedCornerMid₁_avoidsCentralRectangle
    (c : ParafermionicCoverPort) :
    ¬ parafermionicCoverRefinedCentralRectangle
      (parafermionicCoverRefinedCornerMid₁ c) :=
  parafermionicCoverRefinedCornerWalk_support_avoidsCentralRectangle c (by
    rw [parafermionicCoverRefinedCornerWalk_support]
    simp)

theorem parafermionicCoverRefinedCornerElbow_avoidsCentralRectangle
    (c : ParafermionicCoverPort) :
    ¬ parafermionicCoverRefinedCentralRectangle
      (parafermionicCoverRefinedCornerElbow c) :=
  parafermionicCoverRefinedCornerWalk_support_avoidsCentralRectangle c (by
    rw [parafermionicCoverRefinedCornerWalk_support]
    simp)

theorem parafermionicCoverRefinedCornerMid₂_avoidsCentralRectangle
    (c : ParafermionicCoverPort) :
    ¬ parafermionicCoverRefinedCentralRectangle
      (parafermionicCoverRefinedCornerMid₂ c) :=
  parafermionicCoverRefinedCornerWalk_support_avoidsCentralRectangle c (by
    rw [parafermionicCoverRefinedCornerWalk_support]
    simp)

theorem parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
    {n : ℕ} (u : ParafermionicCoverFinitePort n × Bool) :
    ¬ parafermionicCoverRefinedCentralRectangle
      (parafermionicCoverRefinedPairingEmbedding u) := by
  rcases u with ⟨⟨c, hc⟩, layer⟩
  exact parafermionicCoverRefinedPortEmbedding_avoidsCentralRectangle c layer

theorem parafermionicCoverRefinedPairingRouteSupport_avoidsCentralRectangle
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (u v : ParafermionicCoverFinitePort n × Bool) {z : ParafermionicCoverVertex}
    (hz : z ∈ parafermionicCoverRefinedPairingRouteSupport n hn A u v) :
    ¬ parafermionicCoverRefinedCentralRectangle z := by
  rcases u with ⟨⟨c, hc⟩, bu⟩
  rcases v with ⟨⟨d, hd⟩, bv⟩
  cases bu <;> cases bv
  · by_cases hs : parafermionicCoverPortBondState
        (parafermionicCoverConfigurationExtensionState n A) c
    · simp [parafermionicCoverRefinedPairingRouteSupport, hs] at hz
      rcases hz with h | h
      · subst z
        exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
          (⟨⟨c, hc⟩, false⟩)
      · subst z
        exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
          (⟨⟨d, hd⟩, false⟩)
    · simp [parafermionicCoverRefinedPairingRouteSupport, hs] at hz
      rcases hz with h | h | h
      · subst z
        exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
          (⟨⟨c, hc⟩, false⟩)
      · subst z
        exact parafermionicCoverRefinedClosedCapMiddle_avoidsCentralRectangle c
      · subst z
        exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
          (⟨⟨d, hd⟩, false⟩)
  · simp [parafermionicCoverRefinedPairingRouteSupport] at hz
    rcases hz with h | h
    · subst z
      exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
        (⟨⟨c, hc⟩, false⟩)
    · subst z
      exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
        (⟨⟨d, hd⟩, true⟩)
  · simp [parafermionicCoverRefinedPairingRouteSupport] at hz
    rcases hz with h | h
    · subst z
      exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
        (⟨⟨c, hc⟩, true⟩)
    · subst z
      exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
        (⟨⟨d, hd⟩, false⟩)
  · simp [parafermionicCoverRefinedPairingRouteSupport] at hz
    rcases hz with h | h | h | h | h
    · subst z
      exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
        (⟨⟨c, hc⟩, true⟩)
    · subst z
      exact parafermionicCoverRefinedCornerMid₁_avoidsCentralRectangle c
    · subst z
      exact parafermionicCoverRefinedCornerElbow_avoidsCentralRectangle c
    · subst z
      exact parafermionicCoverRefinedCornerMid₂_avoidsCentralRectangle c
    · subst z
      exact parafermionicCoverRefinedPairingEmbedding_avoidsCentralRectangle
        (⟨⟨d, hd⟩, true⟩)

theorem parafermionicCoverRefinedPairingRoute_support_avoidsCentralRectangle
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    {u v : ParafermionicCoverFinitePort n × Bool}
    (h : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Adj u v)
    {z : ParafermionicCoverVertex}
    (hz : z ∈ (parafermionicCoverRefinedPairingRoute n hn A h).support) :
    ¬ parafermionicCoverRefinedCentralRectangle z := by
  rw [parafermionicCoverRefinedPairingRoute_support] at hz
  exact parafermionicCoverRefinedPairingRouteSupport_avoidsCentralRectangle
    n hn A u v hz

end PottsContinuity.FKC.Medial
