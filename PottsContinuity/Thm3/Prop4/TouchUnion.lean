module

public import PottsContinuity.Thm3.Prop4.TouchIsolation
public import PottsContinuity.Thm3.Prop4.TiltedCandidates

/-!
# The corrected finite union and averaging step for Lemma 6

DCST, TeX lines 1601–1610. The deterministic covering and geometric count are
proved for the actual source height and event A. Conditional probability helpers
keep the mixed-duality half bound and explored-strip comparison explicit as
hypotheses; they are not Lemma 6 itself.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

/-- Actual A(z), with an ambient-membership proof rather than a default root. -/
def tiltedIsolationAt (N n m : ℕ) (t : ℝ) (z : ℤ × ℤ) : Set (TiltedConfiguration N t) :=
  {ω | ∃ hz : z ∈ tiltedStripVertices N t, tiltedTouchIsolationEvent N n m t ω ⟨z,hz⟩}

/-- The source low-height event is covered by A(z) over the corrected finite set. -/
theorem low_height_subset_touchIsolation_union (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) (htm : ∃ a : ℤ, t*(m : ℝ) = a) :
    {ω : TiltedConfiguration (2*n) t |
      lowestTopConnectedHeight (2*n) (by omega) t ω 0 ≤ n} ⊆
      ⋃ z ∈ tiltedCandidates n (n*m^2) t, tiltedIsolationAt (2*n) n m t z := by
  intro ω hω
  obtain ⟨k, hk, hFk, hmin⟩ := lowestTopConnectedHeight_local_minimum n m hn hm t htm ω hω
  have hz := local_minimum_vertex_mem_candidates n m hn t ω k hk hFk
  obtain ⟨hx, hxA⟩ := local_minimum_implies_touchIsolation n m hn t ht ω k hFk hmin
  exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨hz, hx, hxA⟩⟩

/-- The actual candidate set is nonempty, including all small scales. -/
theorem tiltedCandidates_nonempty (n R : ℕ) (t : ℝ) :
    (tiltedCandidates n R t).Nonempty := by
  refine ⟨(0,0), (mem_tiltedCandidates _ _ _ _).mpr ?_⟩
  simp [tiltedStripVertices, tiltedHeight]

end PottsContinuity.Thm3.Prop4
