-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/DisjointBlockEventAvoidance.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteConditionalEventBounds
public import Mathlib.Tactic
public import Mathlib.Data.Finset.Lattice.Basic
public import Mathlib.Data.Finset.SDiff

@[expose] public section

open MeasureTheory
noncomputable section

namespace PottsContinuity.FKC.FiniteFK

local instance disjointBlockConfigurationMeasurableSpace {Ω : Type*} [Fintype Ω] [DecidableEq Ω] :
    MeasurableSpace (Finset Ω) := ⊤
local instance disjointBlockConfigurationMeasurableSingleton {Ω : Type*} [Fintype Ω] [DecidableEq Ω] :
    MeasurableSingletonClass (Finset Ω) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Avoiding every event indexed by `J`. -/
def disjointBlockAvoidanceSet {Ω ι : Type*} [Fintype Ω]
    (E : ι → Set (Finset Ω)) (J : Finset ι) : Set (Finset Ω) :=
  {A | ∀ i ∈ J, A ∉ E i}

theorem disjointBlock_event_avoidance_bound
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : PMF (Finset Ω)) (hp : ∀ A, p A ≠ 0)
    (F : ι → Finset Ω) (E : ι → Set (Finset Ω)) (J : Finset ι)
    (c : ι → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hlocal : ∀ i A B, A ∩ F i = B ∩ F i → (A ∈ E i ↔ B ∈ E i))
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hcond : ∀ i (y : Set.range (fun A : Finset Ω => A \ F i)),
      c i ≤ ((finiteStatisticConditionalPMF p hp (fun A : Finset Ω => A \ F i) y).toMeasure (E i)).toReal) :
    (p.toMeasure (disjointBlockAvoidanceSet E J)).toReal ≤
      ∏ i ∈ J, (1 - c i) := by
  classical
  let Avoid := disjointBlockAvoidanceSet E
  have hmain (J : Finset ι) :
      (p.toMeasure (Avoid J)).toReal ≤ ∏ i ∈ J, (1 - c i) := by
    induction J using Finset.induction_on with
    | empty =>
        simp [Avoid, disjointBlockAvoidanceSet]
    | @insert i J hi ih =>
        let S : Set (Finset Ω) := Avoid J
        have hstable : ∀ A B,
            (fun C : Finset Ω => C \ F i) A = (fun C => C \ F i) B →
              (A ∈ S ↔ B ∈ S) := by
          intro A B hout
          have hinter (j : ι) (hji : j ≠ i) : A ∩ F j = B ∩ F j := by
            have hnot (x : Ω) (hx : x ∈ F j) : x ∉ F i := by
              intro hxi
              exact (Finset.disjoint_left.mp (hdisj i j (Ne.symm hji))) hxi hx
            apply Finset.ext
            intro x
            simp only [Finset.mem_inter]
            constructor
            · rintro ⟨hxA, hxj⟩
              have hxout : x ∈ A \ F i := Finset.mem_sdiff.mpr ⟨hxA, hnot x hxj⟩
              have hxoutB : x ∈ B \ F i := by simpa [hout] using hxout
              exact ⟨(Finset.mem_sdiff.mp hxoutB).1, hxj⟩
            · rintro ⟨hxB, hxj⟩
              have hxout : x ∈ B \ F i := Finset.mem_sdiff.mpr ⟨hxB, hnot x hxj⟩
              have hxoutA : x ∈ A \ F i := by simpa [hout] using hxout
              exact ⟨(Finset.mem_sdiff.mp hxoutA).1, hxj⟩
          change (∀ j ∈ J, A ∉ E j) ↔ (∀ j ∈ J, B ∉ E j)
          constructor
          · intro hA j hj
            have hji : j ≠ i := by
              intro hEq
              subst j
              exact hi hj
            rw [← hlocal j A B (hinter j hji)]
            exact hA j hj
          · intro hB j hj
            have hji : j ≠ i := by
              intro hEq
              subst j
              exact hi hj
            rw [hlocal j A B (hinter j hji)]
            exact hB j hj
        have hstep := finiteConditional_event_complement_upper_bound
          p hp (fun A : Finset Ω => A \ F i) S (E i) (c i) hstable
          (hc0 i) (hc1 i) (hcond i)
        have hset : Avoid (insert i J) = S \ E i := by
          ext A
          simp [Avoid, S, disjointBlockAvoidanceSet, and_comm]
        rw [hset]
        calc
          (p.toMeasure (S \ E i)).toReal ≤ (1 - c i) * (p.toMeasure S).toReal := hstep
          _ ≤ (1 - c i) * ∏ j ∈ J, (1 - c j) :=
            mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr (hc1 i))
          _ = ∏ j ∈ insert i J, (1 - c j) := by simp [Finset.prod_insert, hi]
  exact hmain J

end PottsContinuity.FKC.FiniteFK
