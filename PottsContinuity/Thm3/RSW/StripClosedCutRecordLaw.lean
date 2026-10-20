module

public import PottsContinuity.Thm3.RSW.StripIntervalFrozenLaw
public import PottsContinuity.Exploration.FiniteStoppingSetDMP
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutOpenSupport
public import PottsContinuity.FKC.FiniteFK.HorizontalStripCutWindowInterval
public import PottsContinuity.FKC.FiniteFK.HorizontalStripClosedCutRecordState
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

namespace PottsContinuity.RSW
open FKC.Medial FKC.FiniteFK
open PD.FK Exploration
noncomputable section

local instance pdClosedCutCondOuterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance pdClosedCutCondOuterEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripCutRectangle N n).edgeSet := Classical.decEq _
local instance pdClosedCutCondInnerEdgeFintype (a : ℤ) (w n : ℕ) :
    Fintype (FKC.rectangleGraph (a, 0) w (2 * n)).edgeSet := Fintype.ofFinite _

/-- On a successful two-sided closed-cut record, the actual outer FK PD.FK.law
conditioned on the complete scan record restricts to the selected interval
with exactly top-only wiring. The outer boundary is supported on the top and
vertical sides and dominates top-only wiring; the outer vertical sides are
outside the interval. -/
theorem stripClosedCutRecord_law_map_interval_topOnly
    (N n K : ℕ) (hKN : K ≤ N) (q : Parameters)
    (ξ : PD.FK.BoundaryCondition (FKC.RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)))
    (hξ : ξ.boundary ⊆ horizontalStripTopSidesSet N n)
    (hTop : (PD.FK.BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
      ξ.partition)
    (A₀ : PD.FK.Configuration (horizontalStripCutRectangle N n))
    {i j : ℕ}
    (hL : (horizontalStripLeftBlockScan N n K A₀).2 = some i)
    (hR : (horizontalStripRightBlockScan N n K A₀).2 = some j) :
    let lo : ℤ := -(N : ℤ) + (i : ℤ) + 1
    let hi : ℤ := (N : ℤ) - 1 - (j : ℤ)
    let w : ℕ := (hi - lo).toNat
    let G := horizontalStripCutRectangle N n
    let H := FKC.rectangleGraph (lo, 0) w (2 * n)
    let f : FKC.RectangleVertex (lo, 0) w (2 * n) ↪
        FKC.RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
      horizontalStripIntervalEmbedding
        (by have hs := horizontalStripClosedCutReveal_window_strict_outer_ends N n K A₀ hL hR
            have hc := horizontalStripClosedCutReveal_window_contains_center N n K A₀ hKN hL hR
            have hw : (w : ℤ) = hi - lo := by
              dsimp [w]
              rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo)]
            omega)
        (by have hs := horizontalStripClosedCutReveal_window_strict_outer_ends N n K A₀ hL hR
            have hc := horizontalStripClosedCutReveal_window_contains_center N n K A₀ hKN hL hR
            have hw : (w : ℤ) = hi - lo := by
              dsimp [w]
              rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo)]
            omega)
    let hGH : H.map f ≤ G := horizontalStripInterval_map_le
      (by have hs := horizontalStripClosedCutReveal_window_strict_outer_ends N n K A₀ hL hR
          have hc := horizontalStripClosedCutReveal_window_contains_center N n K A₀ hKN hL hR
          have hw : (w : ℤ) = hi - lo := by
            dsimp [w]
            rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo)]
          omega)
      (by have hs := horizontalStripClosedCutReveal_window_strict_outer_ends N n K A₀ hL hR
          have hc := horizontalStripClosedCutReveal_window_contains_center N n K A₀ hKN hL hR
          have hw : (w : ℤ) = hi - lo := by
            dsimp [w]
            rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo)]
          omega)
    ((PD.FK.law G q ξ).filter
      (Exploration.revealRecordEvent (fun A => horizontalStripClosedCutReveal N n K A) A₀)
      (by
        have hstable : ∀ C C', C' ∩ horizontalStripClosedCutReveal N n K C =
            C ∩ horizontalStripClosedCutReveal N n K C →
            horizontalStripClosedCutReveal N n K C' = horizontalStripClosedCutReveal N n K C := by
          intro C C' hAgree
          exact horizontalStripClosedCutReveal_eq_of_agree N n K C C' hKN hAgree
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent
          (fun A => horizontalStripClosedCutReveal N n K A) hstable A₀]
        exact PD.FK.frozenStateEvent_support q ξ _ _)).map
          (PD.FK.embeddedConfigurationRestriction H G f hGH) =
      PD.FK.law H q (PD.FK.BoundaryCondition.wired (horizontalStripIntervalTopWiredSet lo w n)) := by
  classical
  let lo : ℤ := -(N : ℤ) + (i : ℤ) + 1
  let hi : ℤ := (N : ℤ) - 1 - (j : ℤ)
  let w : ℕ := (hi - lo).toNat
  let G := horizontalStripCutRectangle N n
  let H := FKC.rectangleGraph (lo, 0) w (2 * n)
  have hcenter := horizontalStripClosedCutReveal_window_contains_center N n K A₀ hKN hL hR
  have hsEnds := horizontalStripClosedCutReveal_window_strict_outer_ends N n K A₀ hL hR
  have hw : (w : ℤ) = hi - lo := by
    dsimp [w]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo)]
  have hleft : -(N : ℤ) < lo := by dsimp [lo]; exact hsEnds.1
  have hright : lo + (w : ℤ) < N := by
    have hsum : lo + (hi - lo) = hi := by dsimp [lo, hi]; omega
    rw [hw, hsum]
    exact hsEnds.2
  have hloWeak : -(N : ℤ) ≤ lo := le_of_lt hleft
  have hhiWeak : hi ≤ N := le_of_lt hsEnds.2
  have hle : lo ≤ hi := by omega
  let f : FKC.RectangleVertex (lo, 0) w (2 * n) ↪
      FKC.RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    horizontalStripIntervalEmbedding hloWeak (by rw [hw]; omega)
  have hGH : H.map f ≤ G :=
    horizontalStripInterval_map_le hloWeak (by rw [hw]; omega)
  let reveal : PD.FK.Configuration G → PD.FK.Configuration G :=
    fun A => horizontalStripClosedCutReveal N n K A
  have hstable : ∀ C C', C' ∩ reveal C = C ∩ reveal C → reveal C' = reveal C := by
    intro C C' hAgree
    exact horizontalStripClosedCutReveal_eq_of_agree N n K C C' hKN hAgree
  change ((PD.FK.law G q ξ).filter
      (Exploration.revealRecordEvent reveal A₀)
      (by
        rw [Exploration.revealRecordEvent_eq_frozenStateEvent
          reveal hstable A₀]
        exact PD.FK.frozenStateEvent_support q ξ _ _)).map
          (PD.FK.embeddedConfigurationRestriction H G f hGH) =
      PD.FK.law H q (PD.FK.BoundaryCondition.wired (horizontalStripIntervalTopWiredSet lo w n))
  let embCut := horizontalStripCutWindowIntervalEmbedding
    (N := N) (n := n) (lo := lo) (hi := hi) hloWeak hhiWeak hle
  have hemb : f = embCut := by
    apply Function.Embedding.ext
    intro v
    apply Subtype.ext
    rfl
  let R : PD.FK.Configuration G := PD.FK.subgraphRemovedEdges (H.map f) G
  have hReveal : reveal A₀ = R := by
    calc
      reveal A₀ = horizontalStripCutWindowReveal N n lo hi := by
        simp [reveal, horizontalStripClosedCutReveal, hL, hR, lo, hi]
      _ = PD.FK.subgraphRemovedEdges
          ((FKC.rectangleGraph (lo, 0) (hi - lo).toNat (2 * n)).map embCut) G :=
            (horizontalStripCutWindowInterval_reveal_eq
              (N := N) (n := n) (lo := lo) (hi := hi) hloWeak hhiWeak hle).symm
      _ = R := by
        simp only [R, H, G]
        rw [← hemb]
  let Krec := Exploration.revealRecordConfiguration reveal A₀
  let Kstate : PD.FK.RemovedConfiguration G R :=
    ⟨A₀ ∩ R, by
      rw [← hReveal]
      exact Finset.inter_subset_right⟩
  have hKval : Kstate.val = Krec.val := by
    simp [Kstate, Krec, Exploration.revealRecordConfiguration, hReveal]
  have hRecordFrozen : Exploration.revealRecordEvent reveal A₀ = PD.FK.frozenStateEvent R Kstate := by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent reveal hstable A₀]
    ext C
    change C ∩ reveal A₀ = A₀ ∩ reveal A₀ ↔ C ∩ R = A₀ ∩ R
    simp [hReveal]
  have hK : ∀ ⦃e : G.edgeSet⦄, e ∈ Kstate.val →
      ∀ ⦃v : FKC.RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)⦄,
        v ∈ e.val → v ∉ Set.range f := by
    intro e he v hv
    have heA : e ∈ A₀ ∩ R := he
    have heA0 : e ∈ A₀ := (Finset.mem_inter.mp heA).1
    have heR : e ∈ reveal A₀ := by simpa [hReveal] using (Finset.mem_inter.mp heA).2
    have hout := horizontalStripClosedCutReveal_open_endpoints_outside
      N n K A₀ hL hR e heA0 heR v hv
    intro hvf
    have hvRange : v ∈ horizontalStripCutWindow N n lo hi := by
      rw [← horizontalStripCutWindowIntervalEmbedding_range
        (N := N) (n := n) (lo := lo) (hi := hi) hloWeak hhiWeak hle]
      rcases hvf with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      change embCut u = v
      calc
        embCut u = f u := congrArg (fun g => g u) hemb.symm
        _ = v := hu
    exact hout hvRange
  have hfiltered := stripInterval_frozen_law_eq_top
    lo w n N hleft hright q ξ hξ hTop Kstate hK
  have hrecordSupport : ∃ C ∈ Exploration.revealRecordEvent reveal A₀,
      C ∈ (PD.FK.law G q ξ).support := by
    rw [hRecordFrozen]
    exact PD.FK.frozenStateEvent_support q ξ R Kstate
  have hfrozenSupport : ∃ C ∈ PD.FK.frozenStateEvent R Kstate,
      C ∈ (PD.FK.law G q ξ).support := PD.FK.frozenStateEvent_support q ξ R Kstate
  have hfilter : (PD.FK.law G q ξ).filter (Exploration.revealRecordEvent reveal A₀) hrecordSupport =
      (PD.FK.law G q ξ).filter (PD.FK.frozenStateEvent R Kstate) hfrozenSupport := by
    congr 1
  rw [hfilter]
  exact hfiltered

end
end PottsContinuity.RSW
