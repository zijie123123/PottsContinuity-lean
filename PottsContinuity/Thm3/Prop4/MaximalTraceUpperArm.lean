module

public import PottsContinuity.Thm3.Prop4.MaximalUpperArmLowerBound
public import PottsContinuity.Thm3.Prop4.MaximalExcursionSupportingLine

/-!
# The actual Euclidean maximal event supplies its upper-arm comparison

A columnwise lower reveal lies below the genuine capsule tangent because
each original endpoint is below a trace vertex in the same column. The
maximizing event is unchanged; no parallel-chord hypothesis is introduced.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

open PD.FK
noncomputable section
attribute [local instance] configurationMeasurableSpace remainingConfigurationMeasurableSpace
local instance maximalTraceUpperEdgeEq (a : LatticeVertex) (w h : ℕ) :
    DecidableEq (rectangleGraph a w h).edgeSet := Classical.decEq _

/-- On the original maximal Euclidean event, a genuine columnwise lower
reveal gives the actual upper complementary star-port arm in every state.
Only touch and the explicit deterministic lower-reveal geometry are inputs. -/
theorem maximal_trace_upper_arm_lower_of_touch_and_column_reveal {Ω : Type*}
    (q : Set.Ici (1 : ℝ)) {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (u v : LatticeVertex)
    (huB : u ∈ box n) (hvB : v ∈ box n) (huX : u.1 = -(n : ℤ)) (hvX : v.1 = n)
    (trace : Ω → Finset LatticeVertex) (ω : Ω) (htrace : ∀ w ∈ trace ω, w ∈ box n)
    (huT : u ∈ trace ω) (hvT : v ∈ trace ω) (z : LatticeVertex)
    (hz : ω ∈ maximalTubeExcursionEvent n ε u v trace z)
    (R : Configuration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)))
    (B : RemovedConfiguration (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) R)
    (hR : ∀ e ∈ R,
      (∃ w ∈ trace ω,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).source.2 ≤ w.2) ∧
      (∃ w ∈ trace ω,
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.1 = w.1 ∧
        (rectanglePrimalEdgeBond (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) e).target.2 ≤ w.2))
    (hTouch : ∀ k l : ℕ, 1 ≤ k → k ≤ l → ∀ s : ℝ, s ∈ Set.Icc (-1 : ℝ) 1 →
      1/(20*(k : ℝ)^2*(l : ℝ)^2) ≤ tiltedTouchProbability (RSW.selfDualParameters q) k l s) :
    1/(20*((4*n+4 : ℕ) : ℝ)^2*((4*n+4 : ℕ) : ℝ)^2) ≤
      ((frozenFiberLaw (RSW.selfDualParameters q) (BoundaryCondition.free ∅) R B).toMeasure
        {A | A.val ∪ B.val ∈ sampledRectangleDualArmEvent (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
          (sampledStarFacePorts (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
            ⟨z,by rw [PlanarTopology.latticeRectangle_neg_eq_box];
                  exact (Finset.mem_filter.mp hz.1).1⟩)
          (PlanarTopology.rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u v)
          (fun _ => True)}).toReal := by
  obtain ⟨t,c,ht,hzc,hAll⟩ := maximal_euclidean_excursion_below_admissible_line hn ε u v
    huB hvB huX hvX trace ω htrace z hz
  have hBelow : ∀ a : LatticeVertex,
      (∃ w ∈ trace ω, a.1 = w.1 ∧ a.2 ≤ w.2) → tiltedHeight t a ≤ tiltedHeight t z := by
    rintro a ⟨w,hw,hx,hy⟩
    have hw' := hAll w hw
    have hyR : (a.2 : ℝ) ≤ w.2 := by exact_mod_cast hy
    dsimp [tiltedHeight]
    rw [hx]
    linarith only [hw',hyR,hzc]
  exact maximal_upper_star_arm_lower_of_touch q hn u v z huB hvB
    (Finset.mem_filter.mp hz.1).1 huX hvX (Finset.mem_filter.mp hz.1).2.2
    t (abs_le.mp ht) (hBelow u ⟨u,huT,rfl,le_rfl⟩) (hBelow v ⟨v,hvT,rfl,le_rfl⟩) R B
    (fun e he => ⟨hBelow _ (hR e he).1,hBelow _ (hR e he).2⟩) hTouch

end
end PottsContinuity.Thm3.Prop4
