-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripOriginAspectTwoLowerBound.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripOriginLowerBound
public import PottsContinuity.FKC.FiniteFK.ConnectionPathFiniteEnergy
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Int.Star
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Metrizable.Urysohn
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.FKC.Medial

open PottsContinuity.FKC.FiniteFK
noncomputable section

private theorem aspect_two_candidate_reciprocal_bound {h m : ℕ}
    (hh : 1 ≤ h) (hm : 2 ≤ m) :
    (1 / (5 * (h : ℝ)^2 * (m : ℝ)^2) : ℝ) ≤
      1 / (2 * ((2 * (h * m) + 1) * (h + 1) : ℕ)) := by
  have hR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have mR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hhm : (2 : ℝ) ≤ (h : ℝ) * m := by nlinarith
  have hfactor : 2 * (h : ℝ) * m + 1 ≤ (5 / 2) * (h : ℝ) * m := by
    nlinarith
  have hplus : (h : ℝ) + 1 ≤ 2 * h := by linarith
  have hden :
      2 * ((2 * ((h : ℝ) * m) + 1) * ((h : ℝ) + 1)) ≤
        5 * (h : ℝ)^2 * (m : ℝ)^2 := by
    have hleftnonneg : 0 ≤ 2 * (h : ℝ) * m + 1 := by positivity
    have hrightnonneg : 0 ≤ (h : ℝ) + 1 := by positivity
    have hfactorRnonneg : 0 ≤ (5 / 2) * (h : ℝ) * m := by positivity
    have hprod := mul_le_mul hfactor hplus hrightnonneg hfactorRnonneg
    have hmminus : 0 ≤ (m : ℝ) - 2 := by linarith
    have hmnonneg : 0 ≤ (m : ℝ) := by linarith
    have hprodnon := mul_nonneg (sq_nonneg (h : ℝ))
      (mul_nonneg hmnonneg hmminus)
    calc
      _ ≤ 2 * (((5 / 2) * (h : ℝ) * m) * (2 * h)) := by nlinarith [hprod]
      _ = 10 * (h : ℝ)^2 * m := by ring
      _ ≤ 5 * (h : ℝ)^2 * (m : ℝ)^2 := by nlinarith [hprodnon]
  have hdenpos : 0 < 5 * (h : ℝ)^2 * (m : ℝ)^2 := by positivity
  have hden' :
      (2 * ((2 * (h * m) + 1) * (h + 1) : ℕ) : ℝ) =
        2 * ((2 * ((h : ℝ) * m) + 1) * ((h : ℝ) + 1)) := by
    push_cast
    ring
  rw [hden']
  apply (div_le_div_iff₀ hdenpos (by positivity :
    0 < 2 * ((2 * ((h : ℝ) * m) + 1) * ((h : ℝ) + 1)))).2
  nlinarith

/-- The actual finite zero-tilt rectangle lower bound without the source aspect
condition `height ≤ halfwidth`. The median/candidate argument only needs positive
height and width at least two. -/
theorem horizontalStripOriginConnection_probability_lower_bound_aspect_two
    (q : PottsContinuity.FKC.ClusterWeight) {h m : ℕ}
    (hh : 1 ≤ h) (hm : 2 ≤ m) :
    (1 / (5 * (h : ℝ)^2 * (m : ℝ)^2) : ℝ) ≤
      (measure (rectangleGraph (-(m : ℤ), 0) (2*m) h) q
        (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m h))
        (horizontalStripOriginLocalConnectionEvent m h)).toReal := by
  obtain ⟨μ, hμ, _⟩ :=
    horizontalStripTopWired_common_limit_height_sublevel_le_origin q h (by omega)
  have hcanonical : μ = Classical.choose
      (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q h) := by
    let : NeBot (atTop : Filter ℕ) := atTop_neBot
    exact tendsto_nhds_unique hμ.1
      (Classical.choose_spec
        (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q h)).1
  have hheight := horizontalStripCanonicalHeight_probability_ge_half q h
  have hmedian :
      (1 / 2 : ℝ) ≤
        ((μ : Measure LatticeConfiguration)
          {ω | horizontalStripHeight h ω 0 ≤ h}).toReal := by
    simpa [hcanonical] using hheight
  have hsub := hμ.2 m (by omega)
  let C : ℝ := (2 * (h*m) + 1) * (h+1)
  have hCpos : 0 < C := by positivity
  have hfrac : (1 / (2*C)) ≤
      ((μ : Measure LatticeConfiguration)
        {ω | horizontalStripHeight h ω 0 ≤ h}).toReal / C := by
    calc
      1 / (2*C) = (1 / 2 : ℝ) / C := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hmedian (le_of_lt hCpos)
  have hrecip := aspect_two_candidate_reciprocal_bound hh hm
  have hrecipC :
      (1 / (5 * (h : ℝ)^2 * (m : ℝ)^2) : ℝ) ≤ 1 / (2*C) := by
    simpa [C, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hrecip
  change ((μ : Measure LatticeConfiguration)
      {ω | horizontalStripHeight h ω 0 ≤ h}).toReal / C ≤
    (measure (rectangleGraph (-(m : ℤ), 0) (2*m) h) q
      (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet m h))
      (horizontalStripOriginLocalConnectionEvent m h)).toReal at hsub
  exact le_trans hrecipC (le_trans hfrac hsub)

private theorem aspectTwo_heightTwo_halfwidthOne_lower_bound
    (q : PottsContinuity.FKC.ClusterWeight) :
    (1 / 20 : ℝ) ≤
      (measure (rectangleGraph (-1, 0) 2 2) q
        (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet 1 2))
        (horizontalStripOriginLocalConnectionEvent 1 2)).toReal := by
  let G : SimpleGraph (RectangleVertex (-1, 0) 2 2) := rectangleGraph (-1, 0) 2 2
  let x : RectangleVertex (-1, 0) 2 2 := ⟨(0, 0), by
    rw [mem_latticeRectangle]
    norm_num⟩
  let a : RectangleVertex (-1, 0) 2 2 := ⟨(0, 1), by
    rw [mem_latticeRectangle]
    norm_num⟩
  let t : RectangleVertex (-1, 0) 2 2 := ⟨(0, 2), by
    rw [mem_latticeRectangle]
    norm_num⟩
  have hat : G.Adj a t := by
    rw [rectangleGraph_adj_iff, squareLattice_adj_iff]
    exact Or.inr ⟨by norm_num, Or.inl (by norm_num)⟩
  have hxa : G.Adj x a := by
    rw [rectangleGraph_adj_iff, squareLattice_adj_iff]
    exact Or.inr ⟨by norm_num, Or.inl (by norm_num)⟩
  let p : G.Walk t x :=
    SimpleGraph.Walk.cons hat.symm
      (SimpleGraph.Walk.cons hxa.symm SimpleGraph.Walk.nil)
  have htopmem : t.val ∈ rectangleTopSide (-1, 0) 2 2 := by
    change (0, 2) ∈ rectangleTopSide (-1, 0) 2 2
    simp [rectangleTopSide, Finset.mem_filter, mem_latticeRectangle]
  have ht : t ∈ horizontalStripOriginLocalWiredSet 1 2 := by
    change t.val ∈ rectangleLeftSide (-1, 0) 2 2 ∪
      rectangleRightSide (-1, 0) 2 2 ∪ rectangleTopSide (-1, 0) 2 2
    exact Finset.mem_union.mpr (Or.inr htopmem)
  have hpath := actualConnection_probability_along_walk_finite_energy
    (q := q) (ξ := BoundaryCondition.wired
      (horizontalStripOriginLocalWiredSet 1 2)) (z := t) p
  have htopEvent :
      {A : Configuration G | ActualConnected G A t t} = Set.univ := by
    ext A
    simp [ActualConnected]
  have htopMeasure :
      (measure G q (BoundaryCondition.wired
        (horizontalStripOriginLocalWiredSet 1 2))
        {A : Configuration G | ActualConnected G A t t}).toReal = 1 := by
    rw [htopEvent, measure_univ]
    rfl
  have hconnSubset :
      {A : Configuration G | ActualConnected G A x t} ⊆
        horizontalStripOriginLocalConnectionEvent 1 2 := by
    intro A hA
    exact ⟨t, ht, by simpa [x, horizontalStripOriginLocalRoot] using hA⟩
  have hconn : (1 / (1 + loopWeight q)) ^ p.length * 1 ≤
      (measure G q (BoundaryCondition.wired
        (horizontalStripOriginLocalWiredSet 1 2))
        {A | ActualConnected G A x t}).toReal := by
    simpa [htopMeasure] using hpath
  have hmeasure :
      (measure G q (BoundaryCondition.wired
        (horizontalStripOriginLocalWiredSet 1 2))
        {A | ActualConnected G A x t}).toReal ≤
      (measure G q (BoundaryCondition.wired
        (horizontalStripOriginLocalWiredSet 1 2))
        (horizontalStripOriginLocalConnectionEvent 1 2)).toReal := by
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hconnSubset)
  have hε : (1 / 3 : ℝ) < 1 / (1 + loopWeight q) := by
    apply (lt_div_iff₀ (PottsContinuity.FKC.one_add_loopWeight_pos q)).2
    nlinarith [PottsContinuity.FKC.loopWeight_lt_two q]
  have hbound : (1 / 20 : ℝ) ≤ (1 / (1 + loopWeight q)) ^ 2 := by
    nlinarith [sq_nonneg (1 / (1 + loopWeight q) - (1 / 3 : ℝ)),
      PottsContinuity.FKC.loopWeight_lt_two q]
  have plen : p.length = 2 := by simp [p]
  rw [plen] at hconn
  calc
    (1 / 20 : ℝ) ≤ (1 / (1 + loopWeight q)) ^ 2 := hbound
    _ ≤ (measure G q (BoundaryCondition.wired
        (horizontalStripOriginLocalWiredSet 1 2))
        {A | ActualConnected G A x t}).toReal := by
      simpa [G, x, horizontalStripOriginLocalRoot, pow_two] using hconn
    _ ≤ (measure G q (BoundaryCondition.wired
        (horizontalStripOriginLocalWiredSet 1 2))
        (horizontalStripOriginLocalConnectionEvent 1 2)).toReal := hmeasure

/-- Source's full `height 2n, halfwidth n` zero-tilt rectangle input at the
`1/(20 n^4)` scale, with the smallest n handled by an actual two-edge path. -/
theorem horizontalStripOriginConnection_probability_lower_bound_height_two_n
    (q : PottsContinuity.FKC.ClusterWeight) {n : ℕ} (hn : 1 ≤ n) :
    (1 / (20 * (n : ℝ)^4) : ℝ) ≤
      (measure (rectangleGraph (-(n : ℤ), 0) (2*n) (2*n)) q
        (BoundaryCondition.wired (horizontalStripOriginLocalWiredSet n (2*n)))
        (horizontalStripOriginLocalConnectionEvent n (2*n))).toReal := by
  by_cases hn2 : 2 ≤ n
  · have h := horizontalStripOriginConnection_probability_lower_bound_aspect_two
      q (h := 2*n) (m := n) (by omega) hn2
    have hcast : (1 / (5 * (2*n : ℝ)^2 * (n : ℝ)^2) : ℝ) =
        1 / (20 * (n : ℝ)^4) := by ring
    simpa [hcast] using h
  · have hn1 : n = 1 := by omega
    subst n
    simpa using aspectTwo_heightTwo_halfwidthOne_lower_bound q

end
end PottsContinuity.FKC.Medial
