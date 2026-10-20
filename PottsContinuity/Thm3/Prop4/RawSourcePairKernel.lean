module

public import PottsContinuity.Thm3.Prop4.RawBetweenBulk
public import PottsContinuity.Thm3.Prop4.MarkedUpperBoxTrace
public import PottsContinuity.Thm3.Prop4.RecordedExcursionWitnesses
public import PottsContinuity.Thm3.Prop4.ObservedBetweenTraceEvent
public import PottsContinuity.Thm3.Prop4.TubeExitRegions
public import PottsContinuity.PlanarTopology.AffineWalkBounds
public import PottsContinuity.PlanarTopology.AffinePathIntersection
public import PottsContinuity.BD12.RectangleOpenGraphs
public import PottsContinuity.Thm3.Prop4.FiniteStrictCore
public import PottsContinuity.Thm3.Prop4.FirstSeparatorPrefix
public import PottsContinuity.Thm3.Prop4.FrozenReplayComparison
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import PottsContinuity.PD.FK.ComponentBoundarySupport
public import PottsContinuity.Thm3.Prop4.StableRecordOriginalLaw
public import PottsContinuity.Thm3.RSW.StoppingAverage
public import PottsContinuity.Thm3.Prop4.TubeSquaredArmBound
public import PottsContinuity.Thm3.Prop4.TubeTraceHalfTurn
public import PottsContinuity.Thm3.Prop4.BoxTraceExcursionTransport
public import PottsContinuity.Thm3.Prop4.WidenedExcursionExponent
public import PottsContinuity.Thm3.Prop4.PairKernel

@[expose] public section

open MeasureTheory Filter Topology
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite
noncomputable section
attribute [local instance] configurationMeasurableSpace

/-- Eventual original-box pair estimate from the three primitive source-record
branches, using the unchanged raw record and proved full raw replay. -/
theorem source_pair_kernel_of_touch
    (q : Set.Ici (1 : ℝ)) (c₀ α ε : ℝ) (hc₀ : 0 < c₀) (hα : 0 < α)
    (hε : 0 < ε) (hε1 : ε < 1) (μ : Measure LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (RSW.selfDualParameters q).toP (RSW.selfDualParameters q).toQ 0 μ)
    (hdecay : ∀ m : ℕ, 1 ≤ m → RSW.oneArmProbability μ m ≤ Real.exp (-c₀*(m : ℝ)^α))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    ∃ A c : ℝ, ∃ N : ℕ, 0 < A ∧ 0 < c ∧ 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ u v : (box n : Set LatticeVertex),
      u.val.1 = -(n : ℤ) → v.val.1 = n →
      (measure _ (RSW.selfDualParameters q) (BoundaryCondition.free ∅)
        (connectivityEvent (squareLattice.induce (box n : Set LatticeVertex)) u v)).toReal ≤
        A*prop4PairKernel c ε (RSW.oneArmProbability μ) n := by
  obtain ⟨Ce,hCe,hexc⟩ := excursion_convolution_of_touch_and_source_witnesses q μ hμ hTouch
  obtain ⟨Ab,Cb,Nb,hAb,hCb,hNb,hbulk⟩ := between_trace_bulk_bound_of_touch
    q c₀ α ε hc₀ hα hε hε1.le μ hμ hdecay hTouch
  obtain ⟨Nr,hcut⟩ := eventually_atTop.mp (eventually_split_power_cutoff_admissible ε hε.le hε1)
  let D := max Ab 1
  let K := max Cb (2*Ce)
  have hD : 0 < D := zero_lt_one.trans_le (le_max_right _ _)
  have hK : 0 < K := hCb.trans_le (le_max_left _ _)
  refine ⟨D,K,max (max Nb Nr) 2,hD,hK,le_max_right _ _,?_⟩
  intro n hn u v hu hv
  have hnNb : Nb ≤ n := (le_max_left Nb Nr).trans ((le_max_left _ _).trans hn)
  have hnNr : Nr ≤ n := (le_max_right Nb Nr).trans ((le_max_left _ _).trans hn)
  obtain ⟨hn2,hr,hrn⟩ := hcut n hnNr
  have hn1 : 1 ≤ n := by omega
  obtain ⟨η,hη,_⟩ := exists_widened_excursion_exponent hn2 ε
  let lower := markedLowerBoxTrace n u v
  let upper := markedUpperBoxTrace n u v
  have hLower := markedLowerBoxTrace_has_recorded_excursion_witnesses hn1 η u v hu hv
  have hUpper := markedUpperBoxTrace_has_rotated_recorded_excursion_witnesses hn1 η u v hu hv
  have hscale : 4*(n : ℝ)^ε ≤ (n : ℝ)^η := hη.ge
  have hlowRect := hexc hn1 η ((n : ℝ)^ε) hr hrn hscale u.val v.val
    u.property v.property hu hv (boxTraceOnRectangle n lower) hLower
  have hfaces := tube_opposite_faces_neg_swap n u.val v.val hu hv
  have huppRect := hexc hn1 η ((n : ℝ)^ε) hr hrn hscale
    (boxHalfTurnIso n v).val (boxHalfTurnIso n u).val
    (boxHalfTurnIso n v).property (boxHalfTurnIso n u).property hfaces.1 hfaces.2
    (boxTraceOnRectangle n (halfTurnBoxTrace n upper)) hUpper
  have hlow := (lower_excursion_probability_le_rectangle_trace_excursion
    (RSW.selfDualParameters q) n η u v lower).trans hlowRect
  have hupp := (upperTubeExcursion_probability_eq_rotated_lower
    (RSW.selfDualParameters q) n η u v upper).trans_le
      ((lower_excursion_probability_le_rectangle_trace_excursion (RSW.selfDualParameters q)
        n η (boxHalfTurnIso n v) (boxHalfTurnIso n u) (halfTurnBoxTrace n upper)).trans huppRect)
  have hmid := hbulk n hnNb u v hu hv η hη
  have hsplit := connection_probability_le_tube_split_of_boxTraces (RSW.selfDualParameters q)
    hn1 η u v hu hv lower upper (BoundaryCondition.free ∅)
  have hsum := hsplit.trans (add_le_add (add_le_add hlow hupp) hmid)
  let a := RSW.oneArmProbability μ
  let S := splitArmSum a ((n : ℝ)^ε) (2*n)
  have hS : 0 ≤ S := splitArmSum_nonneg a (fun _ => ENNReal.toReal_nonneg) _ _
  have hdiag : Ab*Real.exp (Cb*(n : ℝ)^ε)*(a n)^2 ≤ D*(Real.exp (K*(n : ℝ)^ε)*(a n)^2) := by
    calc
      _ = Ab*(Real.exp (Cb*(n : ℝ)^ε)*(a n)^2) := by ring
      _ ≤ D*(Real.exp (K*(n : ℝ)^ε)*(a n)^2) :=
        mul_le_mul (le_max_left _ _) (mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg n) ε)))
          (sq_nonneg _)) (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hD.le
  have hcoeff : 2*Ce ≤ D*K := (le_max_right _ _).trans (le_mul_of_one_le_left hK.le (le_max_right _ _))
  have hconv : (2*Ce)*(n : ℝ)^6*S ≤ D*(K*(n : ℝ)^6*S) := by
    calc
      _ ≤ (D*K)*(n : ℝ)^6*S := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (Nat.cast_nonneg n) _)) hS
      _ = _ := by ring
  calc
    _ ≤ Ce*(n : ℝ)^6*S+Ce*(n : ℝ)^6*S+Ab*Real.exp (Cb*(n : ℝ)^ε)*(a n)^2 := hsum
    _ = Ab*Real.exp (Cb*(n : ℝ)^ε)*(a n)^2+(2*Ce)*(n : ℝ)^6*S := by ring
    _ ≤ D*(Real.exp (K*(n : ℝ)^ε)*(a n)^2)+D*(K*(n : ℝ)^6*S) := add_le_add hdiag hconv
    _ = D*prop4PairKernel K ε a n := by
      simp only [prop4PairKernel,S,splitArmSum]
      ring

end
end PottsContinuity.Thm3.Prop4
