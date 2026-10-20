module

public import PottsContinuity.Thm3.Prop4.TiltedTwoCutReveal
public import PottsContinuity.Thm3.Prop4.TiltedFrozenInterval

/-! # The exact surviving-interval law on the genuine two-sided scan record -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance stoppedIntervalEdgeFintype (n M : ℕ) (t : ℝ) :
    Fintype (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance stoppedIntervalEdgeDecidableEq (n M : ℕ) (t : ℝ) :
    DecidableEq (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Successful two-sided cut exploration leaves exactly the intrinsic-top
law on its actual surviving interval. Selector stability, the random-domain
record and the closed-cut support property are all proved dependencies. -/
theorem law_filter_tiltedTwoCutRecord_map_interval_top (θ : PD.FK.Parameters)
    (n M : ℕ) (t : ℝ) (a b : ℤ) (K : ℕ) (side : Fin 2)
    (A₀ : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (i j : ℕ)
    (hL : (tiltedCutScan n M t (fun r => a+r) K A₀).2 = some i)
    (hR : (tiltedCutScan n M t (fun r => b-r) K A₀).2 = some j)
    (hinside : ∀ z ∈ tiltedInterval n M t (a+i+1) (b-j), z ∉ vertexBoundary (box M)) :
    ((PD.FK.law _ θ (tiltedWindowBoundary n M t side)).filter
      (Exploration.revealRecordEvent (tiltedTwoCutReveal n M t a b K) A₀)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent _
          (tiltedTwoCutReveal_stable n M t a b K) A₀]
        exact PD.FK.frozenStateEvent_support θ _ _ _)).map
      (PD.FK.embeddedConfigurationRestriction
        (squareLattice.induce (tiltedInterval n M t (a+i+1) (b-j) : Set (ℤ × ℤ)))
        (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)))
        (tiltedIntervalEmbedding n M t (a+i+1) (b-j))
        (tiltedInterval_map_le n M t (a+i+1) (b-j))) =
      PD.FK.law _ θ (tiltedIntervalTopBoundary n M t (a+i+1) (b-j)) := by
  let lo := a+(i : ℤ)+1
  let hi := b-(j : ℤ)
  let G := squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))
  let H := squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))
  let f := tiltedIntervalEmbedding n M t lo hi
  let R := PD.FK.subgraphRemovedEdges (H.map f) G
  let reveal := tiltedTwoCutReveal n M t a b K
  have hrev : reveal A₀ = R := by
    simp only [reveal,tiltedTwoCutReveal,tiltedTwoCutBounds,hL,hR]
    rfl
  let S : PD.FK.RemovedConfiguration G R := ⟨A₀ ∩ R,Finset.inter_subset_right⟩
  have hclosedL : Disjoint S.val (tiltedWindowCutEdges n M t (lo-1)) := by
    have h := (tiltedCutScan_hit n M t (fun r => a+r) K A₀ i hL).2
    have heq : lo-1 = a+(i : ℤ) := by dsimp [lo]; omega
    rw [heq]
    exact h.mono_left Finset.inter_subset_left
  have hclosedR : Disjoint S.val (tiltedWindowCutEdges n M t hi) :=
    ((tiltedCutScan_hit n M t (fun r => b-r) K A₀ j hR).2).mono_left Finset.inter_subset_left
  have hrecord : Exploration.revealRecordEvent reveal A₀ = PD.FK.frozenStateEvent R S := by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent reveal
      (tiltedTwoCutReveal_stable n M t a b K) A₀]
    ext A
    change A ∩ reveal A₀ = A₀ ∩ reveal A₀ ↔ A ∩ R = A₀ ∩ R
    rw [hrev]
  have hfilter : (PD.FK.law G θ (tiltedWindowBoundary n M t side)).filter
      (Exploration.revealRecordEvent reveal A₀)
      (by
        rw [hrecord]
        exact PD.FK.frozenStateEvent_support θ _ R S) =
      (PD.FK.law G θ (tiltedWindowBoundary n M t side)).filter
        (PD.FK.frozenStateEvent R S) (PD.FK.frozenStateEvent_support θ _ R S) := by
    congr 1
  change ((PD.FK.law G θ (tiltedWindowBoundary n M t side)).filter
    (Exploration.revealRecordEvent reveal A₀) _).map _ = _
  rw [hfilter]
  exact law_filter_frozen_map_tiltedInterval_eq_top θ n M t lo hi side hinside S hclosedL hclosedR

end

end PottsContinuity.Thm3.Prop4
