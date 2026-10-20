module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.Foundations.Bridges
public import PottsContinuity.Infinite.Bridge
public import PottsContinuity.PD.RCInfinite.PercolationZeroOne
public import PottsContinuity.PD.Duality.CircuitEnclosure
public import PottsContinuity.PD.RCInfinite.GraphModification
public import PottsContinuity.PD.RCInfinite.OpeningPaths

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Easy

open PottsContinuity
open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.Medial
open PottsContinuity.PD.Duality

/-- If a wired infinite-volume limit has no infinite cluster at the origin,
translation invariance gives zero probability of an infinite cluster anywhere.
This is the first P1 consequence used in the circuit argument for P1 ⇒ P2. -/
theorem wired_no_infinite_cluster_event
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 1 μ)
    (hP1 : μ {ω | {x | (rcInfiniteOpenGraph ω).Reachable (0, 0) x}.Infinite} = 0) :
    μ PottsContinuity.PD.RCInfinite.infiniteClusterEvent = 0 := by
  cases Foundations.squareLattice_eq_PD
  let μPD : Measure PottsContinuity.PD.FK.LatticeConfiguration := μ
  have hμPD : PottsContinuity.PD.IsRCInfiniteVolumeLimit p q 1 μ :=
    PottsContinuity.Infinite.isRCInfiniteVolumeLimit_to_PD_box p q 1 μ hμ
  have hOrigin : μPD (PottsContinuity.PD.RCInfinite.infiniteAt (0, 0)) = 0 := by
    change μ {ω | {x | (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable
      (0, 0) x}.Infinite} = 0
    exact hP1
  have hZero : μPD (PottsContinuity.PD.RCInfinite.infiniteClusterEvent) = 0 := by
    rw [PottsContinuity.PD.RCInfinite.infiniteClusterEvent_eq_iUnion]
    apply measure_iUnion_null
    intro x
    rw [PottsContinuity.PD.RCInfinite.infiniteAt_measure_eq_origin
      p q hq 1 μPD hμPD x, hOrigin]
  exact hZero

/-- Under P1, almost surely every wired open cluster is finite. -/
theorem wired_all_clusters_finite_ae
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ)) (hq : 1 ≤ (q : ℝ))
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit p q 1 μ)
    (hP1 : μ {ω | {x | (rcInfiniteOpenGraph ω).Reachable (0, 0) x}.Infinite} = 0) :
    ∀ᵐ ω ∂μ, ∀ x : ℤ × ℤ,
      {y | (rcInfiniteOpenGraph ω).Reachable x y}.Finite := by
  cases Foundations.squareLattice_eq_PD
  have hzero := wired_no_infinite_cluster_event p q hq μ hμ hP1
  rw [ae_iff]
  change μ {ω | ¬ ∀ x : ℤ × ℤ,
    {y | (rcInfiniteOpenGraph ω).Reachable x y}.Finite} = 0
  have hset : {ω | ¬ ∀ x : ℤ × ℤ,
      {y | (rcInfiniteOpenGraph ω).Reachable x y}.Finite} =
      PottsContinuity.PD.RCInfinite.infiniteClusterEvent := by
    ext ω
    simp [PottsContinuity.PD.RCInfinite.infiniteClusterEvent,
      PottsContinuity.PD.RCInfinite.infiniteAt,
      PottsContinuity.PD.RCInfinite.cluster,
      Foundations.rcInfiniteOpenGraph_eq_PD]
    change (∃ a b : ℤ,
      {y | (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable (a, b) y}.Infinite) ↔
      (∃ a b : ℤ,
      {y | (PottsContinuity.PD.rcInfiniteOpenGraph ω).Reachable (a, b) y}.Infinite)
    rfl
  rw [hset]
  exact hzero

end PottsContinuity.Thm3.Easy
