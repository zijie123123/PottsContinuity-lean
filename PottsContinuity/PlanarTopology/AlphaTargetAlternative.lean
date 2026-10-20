module

public import PottsContinuity.PlanarTopology.AlphaTargetDuality
public import PottsContinuity.PlanarTopology.AlphaConnectorEndpoints
public import PottsContinuity.PlanarTopology.RectangleCurveExclusion
public import Mathlib.Tactic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK PD.FK.Medial PD.FK.Curves
noncomputable section

/-- Actual primal connectivity between the two closed alpha arm targets. -/
def alphaTargetPrimalCrossing (k : ℕ)
    (A : Configuration (rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))) : Prop :=
  ∃ u : RectangleVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
    (u.val.2 = 64*(k : ℤ) ∧ -(k : ℤ) ≤ u.val.1 ∧ u.val.1 ≤ (k : ℤ)) ∧
    ∃ v : RectangleVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
      (v.val.2 = -64*(k : ℤ) ∧ -(k : ℤ) ≤ v.val.1 ∧ v.val.1 ≤ (k : ℤ)) ∧
      ActualConnected _ A u v

/-- Complementary dual connectivity with literal exterior face-base targets.
The physical locations are obtained by adding (1/2,1/2). -/
def alphaTargetDualCrossing (k : ℕ)
    (A : Configuration (rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))) : Prop :=
  ∃ b : RectangleDualVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
    b.val ∈ alphaLeftDualPorts k ∧
    ∃ d : RectangleDualVertex (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k),
      d.val ∈ alphaRightDualPorts k ∧
      (openGraph (rectangleDualGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))
        (rectangleDualConfiguration (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k) A)).Reachable b d

/-- The alpha-target primal and complementary dual crossings cannot coexist. -/
theorem alpha_target_crossings_exclusive (k : ℕ) (hk : 1 ≤ k)
    (A : Configuration (rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k)))
    (hP : alphaTargetPrimalCrossing k A) (hD : alphaTargetDualCrossing k A) : False := by
  obtain ⟨u,hu,v,hv,hconn⟩ := hP
  obtain ⟨r,_⟩ := hconn.exists_isPath
  let p := r.map (rectangleOpenGraphToSquare _ _ _ A)
  have htrace := rectangle_open_walk_trace_subset _ _ _ A r
  have hPB : ∀ z ∈ Set.range (latticePairCurve p),
      -65*(k : ℝ) ≤ z.1 ∧ z.1 ≤ 65*(k : ℝ) ∧
      -64*(k : ℝ) ≤ z.2 ∧ z.2 ≤ 64*(k : ℝ) := by
    apply latticePairCurve_bounds
    intro z hz
    obtain ⟨z',_,he⟩ := rectangleOpenWalk_mapped_support_preimage _ _ _ A r hz
    have hh := (mem_latticeRectangle _ z'.val (130*k) (128*k)).mp z'.property
    rw [he] at hh
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hh
    have h1 : -65*(k : ℤ) ≤ z.1 := hh.1.1
    have h2 : z.1 ≤ 65*(k : ℤ) := by omega
    have h3 : -64*(k : ℤ) ≤ z.2 := hh.2.1
    have h4 : z.2 ≤ 64*(k : ℤ) := by omega
    exact ⟨by exact_mod_cast h1,by exact_mod_cast h2,by exact_mod_cast h3,by exact_mod_cast h4⟩
  obtain ⟨b,hb,d,hd,⟨q⟩⟩ := hD
  have hne : b ≠ d := by
    intro he
    have hbd := congrArg Subtype.val he
    rw [hbd] at hb
    rcases hb with hb | hb <;> rcases hd with hd | hd <;> omega
  have hpos : 0 < q.length := by
    by_contra hn
    exact hne (SimpleGraph.Walk.eq_of_length_eq_zero (p := q) (by omega))
  let Q := clampedRectangleDualCurve _ _ _ A q
  have hQ : ∀ z ∈ Set.range (Q.map continuous_complexCoordinates),
      -65*(k : ℝ) ≤ z.1 ∧ z.1 ≤ 65*(k : ℝ) ∧
      -64*(k : ℝ) ≤ z.2 ∧ z.2 ≤ 64*(k : ℝ) := by
    rintro z ⟨θ,rfl⟩
    have hh := clampedRectangleDualCurve_mem _ _ _ A q θ
    simp only [Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_natCast,
      Nat.cast_mul,Nat.cast_ofNat] at hh
    change -65*(k : ℝ) ≤ (Q θ).re ∧ (Q θ).re ≤ 65*(k : ℝ) ∧
      -64*(k : ℝ) ≤ (Q θ).im ∧ (Q θ).im ≤ 64*(k : ℝ)
    change -65*(k : ℝ) ≤ (Q θ).re ∧ (Q θ).re ≤ -65*(k : ℝ)+130*k ∧
      -64*(k : ℝ) ≤ (Q θ).im ∧ (Q θ).im ≤ -64*(k : ℝ)+128*k at hh
    exact ⟨hh.1,by linarith [hh.2.1],hh.2.2.1,by linarith [hh.2.2.2]⟩
  have huY : (u.val.2 : ℝ) = 64*(k : ℝ) := by exact_mod_cast hu.1
  have hvY : (v.val.2 : ℝ) = -64*(k : ℝ) := by exact_mod_cast hv.1
  have huX : -(k : ℝ) ≤ (u.val.1 : ℝ) ∧ (u.val.1 : ℝ) ≤ k :=
    ⟨by exact_mod_cast hu.2.1,by exact_mod_cast hu.2.2⟩
  have hvX : -(k : ℝ) ≤ (v.val.1 : ℝ) ∧ (v.val.1 : ℝ) ≤ k :=
    ⟨by exact_mod_cast hv.2.1,by exact_mod_cast hv.2.2⟩
  obtain ⟨z,hzp,hzQ⟩ := continuous_three_arc_paths_intersect
    (-65*(k : ℝ)) (65*(k : ℝ)) (-64*(k : ℝ)) (64*(k : ℝ)) (-(k : ℝ)) (k : ℝ)
    (latticePairCurve p) (Q.map continuous_complexCoordinates) hPB hQ huY hvY huX hvX
    (alpha_clamped_left_endpoint k hk b.val hb) (alpha_clamped_right_endpoint k hk d.val hd)
  have hdis := latticePairCurve_disjoint p Q
    (clamped_dualCurve_disjoint_of_trace_subset _ _ _ A p htrace q hpos)
  exact Set.disjoint_left.mp hdis hzp hzQ

/-- The alpha-target primal event is exactly the complement of the literal
half-cell-correct dual boundary connection. -/
theorem alpha_target_crossing_iff_not_dual (k : ℕ) (hk : 1 ≤ k)
    (A : Configuration (rectangleGraph (-65*(k : ℤ),-64*(k : ℤ)) (130*k) (128*k))) :
    alphaTargetPrimalCrossing k A ↔ ¬alphaTargetDualCrossing k A := by
  classical
  constructor
  · exact fun hp hd => alpha_target_crossings_exclusive k hk A hp hd
  · intro hn
    by_contra hp
    exact hn (alpha_target_dual_exists k hk A hp)

end
end PottsContinuity.PlanarTopology
