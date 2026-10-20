module

public import PottsContinuity.Thm3.RSW.StripNormalizedPatternRead
public import PottsContinuity.FKC.FiniteFK.CylinderConvergenceCriterion

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory Filter Topology
noncomputable section

/-- The literal finite all-open event on original strip bonds. -/
def stripCoordinateAllOpen (n : ℕ) (A : Finset (stripGraph n).edgeSet) : Set (StripConfiguration n) :=
  {ω | ∀ e ∈ A, ω e=true}

/-- Extend actual strip states by closed bonds on the shared plane carrier.
This is only a fixed carrier embedding; original strip states are unchanged. -/
def stripNormalizedClosedExtension (n : ℕ) (ω : StripConfiguration n) : FKC.LatticeConfiguration :=
  Function.extend (stripNormalizedEmbedding n).mapEdgeSet ω (fun _ => false)

/-- Read the original strip coordinates back from their fixed plane labels. -/
def stripNormalizedPlaneRestriction (n : ℕ) (η : FKC.LatticeConfiguration) : StripConfiguration n :=
  fun e => η ((stripNormalizedEmbedding n).mapEdgeSet e)

/-- Each original strip coordinate is preserved exactly by closed extension. -/
theorem stripNormalizedClosedExtension_apply (n : ℕ) (ω : StripConfiguration n)
    (e : (stripGraph n).edgeSet) :
    stripNormalizedClosedExtension n ω ((stripNormalizedEmbedding n).mapEdgeSet e)=ω e :=
  (stripNormalizedEmbedding n).mapEdgeSet.injective.extend_apply ω (fun _ => false) e

/-- Closed extension is continuous on the natural product state spaces. -/
theorem stripNormalizedClosedExtension_continuous (n : ℕ) :
    Continuous (stripNormalizedClosedExtension n) := by
  classical
  apply continuous_pi
  intro e
  by_cases he : e ∈ Set.range (stripNormalizedEmbedding n).mapEdgeSet
  · obtain ⟨f,rfl⟩ := he
    simpa only [stripNormalizedClosedExtension_apply] using
      (continuous_apply f : Continuous (fun ω : StripConfiguration n => ω f))
  · have hzero : (fun ω => stripNormalizedClosedExtension n ω e) = fun _ => false := by
      funext ω
      exact Function.extend_apply' ω (fun _ => false) e he
    rw [hzero]
    exact continuous_const

/-- The coordinate restriction back to the strip is continuous. -/
theorem stripNormalizedPlaneRestriction_continuous (n : ℕ) :
    Continuous (stripNormalizedPlaneRestriction n) :=
  continuous_pi fun e => continuous_apply ((stripNormalizedEmbedding n).mapEdgeSet e)

/-- The two continuous carrier maps preserve every strip probability law. -/
theorem stripNormalized_probability_roundtrip (n : ℕ) (μ : ProbabilityMeasure (StripConfiguration n)) :
    (μ.map (stripNormalizedClosedExtension n)).map (stripNormalizedPlaneRestriction n)=μ := by
  apply Subtype.ext
  change (μ.toMeasure.map (stripNormalizedClosedExtension n)).map
    (stripNormalizedPlaneRestriction n)=μ.toMeasure
  rw [Measure.map_map (stripNormalizedPlaneRestriction_continuous n).measurable
    (stripNormalizedClosedExtension_continuous n).measurable]
  have heq : stripNormalizedPlaneRestriction n ∘ stripNormalizedClosedExtension n = id := by
    funext ω e
    exact stripNormalizedClosedExtension_apply n ω e
  rw [heq,Measure.map_id]

/-- Weak convergence on the actual strip follows from all original finite
all-open coordinates. The proof uses the shared plane criterion. -/
theorem stripProbabilityMeasures_tendsto_of_allOpen_coordinates
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (μs : ι → ProbabilityMeasure (StripConfiguration n)) (μ : ProbabilityMeasure (StripConfiguration n))
    (hcoord : ∀ A : Finset (stripGraph n).edgeSet,
      Tendsto (fun i => μs i (stripCoordinateAllOpen n A)) l (𝓝 (μ (stripCoordinateAllOpen n A)))) :
    Tendsto μs l (𝓝 μ) := by
  classical
  let g := (stripNormalizedEmbedding n).mapEdgeSet
  have hc := stripNormalizedClosedExtension_continuous n
  have hplane : Tendsto (fun i => (μs i).map (stripNormalizedClosedExtension n)) l
      (𝓝 (μ.map (stripNormalizedClosedExtension n))) := by
    apply (FKC.FiniteFK.probabilityMeasures_tendsto_iff_allOpen_coordinates _ _).mpr
    intro F
    by_cases hF : ∀ e ∈ F, e ∈ Set.range g
    · let A := F.preimage g g.injective.injOn
      have hsets : (stripNormalizedClosedExtension n) ⁻¹' FKC.LatticeConfiguration.allOpen F =
          stripCoordinateAllOpen n A := by
        ext ω
        constructor
        · intro h e he
          have heF : g e ∈ F := Finset.mem_preimage.mp he
          simpa only [g,stripNormalizedClosedExtension_apply] using h (g e) heF
        · intro h e he
          obtain ⟨f,rfl⟩ := hF e he
          rw [stripNormalizedClosedExtension_apply]
          exact h f (Finset.mem_preimage.mpr he)
      have hmap (ν : ProbabilityMeasure (StripConfiguration n)) :
          ν.map (stripNormalizedClosedExtension n) (FKC.LatticeConfiguration.allOpen F)=
            ν (stripCoordinateAllOpen n A) := by
        rw [ProbabilityMeasure.map_apply ν hc.measurable.aemeasurable
          (FKC.LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet,hsets]
      simp_rw [hmap]
      exact hcoord A
    · push Not at hF
      obtain ⟨e,heF,heRange⟩ := hF
      have hempty : (stripNormalizedClosedExtension n) ⁻¹' FKC.LatticeConfiguration.allOpen F=∅ := by
        ext ω
        constructor
        · intro h
          have hh := h e heF
          have hfalse : stripNormalizedClosedExtension n ω e=false :=
            Function.extend_apply' ω (fun _ => false) e heRange
          rw [hfalse] at hh
          exact Bool.false_ne_true hh
        · simp
      have hmap (ν : ProbabilityMeasure (StripConfiguration n)) :
          ν.map (stripNormalizedClosedExtension n) (FKC.LatticeConfiguration.allOpen F)=0 := by
        rw [ProbabilityMeasure.map_apply ν hc.measurable.aemeasurable
          (FKC.LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet,hempty]
        simp
      simp_rw [hmap]
      exact tendsto_const_nhds
  have hback := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hplane
    (stripNormalizedPlaneRestriction_continuous n)
  simpa only [stripNormalized_probability_roundtrip] using hback

end
end PottsContinuity.RSW
