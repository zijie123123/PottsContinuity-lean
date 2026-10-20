module

public import PottsContinuity.Thm3.Push.UpperBandRecordCrossing
public import PottsContinuity.Thm3.Push.EmbeddedFilledDMP
public import PottsContinuity.Thm3.Push.EmbeddedRestrictionStates
public import PottsContinuity.FKC.FiniteFK.RevealRecordDisintegration
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK
noncomputable section
local instance embeddedBandRecordEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- The upper-band crossing is invariant on literal outer filled-record
fibers. The statistic records both the revealed original bond set and every
observed open/closed state, using the existing FKC record definition. -/
theorem embedded_upper_band_crossing_record_invariant {V : Type*} [Finite V]
    (a : LatticeVertex) (w H t : ℕ) (ht : t ≤ H) (G : SimpleGraph V)
    (f : RectangleVertex a w H ↪ V) (hRG : (rectangleGraph a w H).map f ≤ G)
    (A B : Configuration G)
    (hrecord : FKC.FiniteFK.revealRecordStatistic (embeddedFilledTopReveal a w H G f hRG) A =
      FKC.FiniteFK.revealRecordStatistic (embeddedFilledTopReveal a w H G f hRG) B) :
    (DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht)
      (embeddedConfigurationRestriction _ _ f hRG A) ∈
      rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t)) ↔
    (DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht)
      (embeddedConfigurationRestriction _ _ f hRG B) ∈
      rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t)) := by
  have hforward : ∀ X Y : Configuration G,
      FKC.FiniteFK.revealRecordStatistic (embeddedFilledTopReveal a w H G f hRG) X =
        FKC.FiniteFK.revealRecordStatistic (embeddedFilledTopReveal a w H G f hRG) Y →
      (DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht)
        (embeddedConfigurationRestriction _ _ f hRG X) ∈
        rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t)) →
      (DualityExt.rectangleConfigurationRestriction (rectangle_upper_band_subset a w H t ht)
        (embeddedConfigurationRestriction _ _ f hRG Y) ∈
        rectangleHorizontalCrossingEvent (a.1,a.2+(t : ℤ)) w (H-t)) := by
    intro X Y hXY hband
    have hR := congrArg Prod.fst hXY
    have hK := congrArg Prod.snd hXY
    change embeddedFilledTopReveal a w H G f hRG X = embeddedFilledTopReveal a w H G f hRG Y at hR
    change X ∩ embeddedFilledTopReveal a w H G f hRG X =
      Y ∩ embeddedFilledTopReveal a w H G f hRG Y at hK
    have hstates : Y ∩ embeddedFilledTopReveal a w H G f hRG X =
        X ∩ embeddedFilledTopReveal a w H G f hRG X := by
      calc
        Y ∩ embeddedFilledTopReveal a w H G f hRG X =
            Y ∩ embeddedFilledTopReveal a w H G f hRG Y := congrArg (fun R => Y ∩ R) hR
        _ = X ∩ embeddedFilledTopReveal a w H G f hRG X := hK.symm
    have hsmall := embedded_record_agreement_restrict _ _ f hRG
      (rectangleFilledTopReveal a w H (embeddedConfigurationRestriction _ _ f hRG X)) X Y hstates
    exact upper_band_crossing_on_filled_record a w H t ht _ _ hband hsmall
  exact ⟨hforward A B hrecord,hforward B A hrecord.symm⟩

end
end PottsContinuity.Push
