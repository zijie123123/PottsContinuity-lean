module

public import PottsContinuity.Thm3.Prop4.SourceBoxRawCoreProbability
public import PottsContinuity.Thm3.Prop4.RawMarkedBetweenTransfer

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite Push Exploration
noncomputable section
attribute [local instance] configurationMeasurableSpace
local instance rawBetweenCoreLowerEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- Record averaging on the source between-traces event. The multiplier is
the actual finite wired strict-core probability. No replay or middle-domain
interface is left in this probability inequality. -/
theorem between_trace_core_probability_mul_le_confined
    (n : ℕ) (hn : 1 ≤ n) (η : ℝ)
    (u v : (box n : Set LatticeVertex)) (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (t b : ℝ) (ht : |t| ≤ 1) (hut : (u.val.2 : ℝ) = t*u.val.1+b) (hvt : (v.val.2 : ℝ) = t*v.val.1+b)
    (θ : Parameters) :
    (PD.FK.measure (finiteLatticeGraph (box n)) θ (frozenBoundaryCondition (box n) 1)
      (inducedStrictInteriorTubeCrossingEvent (box n) n ((n : ℝ)^η) u.val v.val t b)).toReal *
    (PD.FK.measure (finiteLatticeGraph (box n)) θ (BoundaryCondition.free ∅)
      (betweenTubeTraceEvent n η u v (markedLowerBoxTrace n u v) (markedUpperBoxTrace n u v))).toReal ≤
    (PD.FK.measure (finiteLatticeGraph (box n)) θ (BoundaryCondition.free ∅)
      {B | ∃ p : (openGraph (finiteLatticeGraph (box n)) B).Walk u v,
        ∀ z ∈ p.support, z.val ∈ radiusTube n ((n : ℝ)^η) u.val v.val}).toReal := by
  let E := betweenTubeTraceEvent n η u v (markedLowerBoxTrace n u v) (markedUpperBoxTrace n u v)
  let T := (RSW.stoppingObservationMap (markedJointBoxRawReveal n u v)) '' E
  let H : Set (Configuration (finiteLatticeGraph (box n))) :=
    {B | ∃ p : (openGraph (finiteLatticeGraph (box n)) B).Walk u v,
      ∀ z ∈ p.support, z.val ∈ radiusTube n ((n : ℝ)^η) u.val v.val}
  have heq : E = (RSW.stoppingObservationMap (markedJointBoxRawReveal n u v)) ⁻¹' T :=
    markedJointRaw_between_event_eq_observation_preimage n hn η u v hu hv
  have hH : IsUpperSet H := by
    rintro B C hBC ⟨p,hp⟩
    refine ⟨p.mapLe (openGraph_mono hBC),?_⟩
    simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hp
  change _ * (PD.FK.measure (finiteLatticeGraph (box n)) θ (BoundaryCondition.free ∅) E).toReal ≤ _
  rw [heq]
  apply RSW.stopped_event_lower_of_record_bounds θ (BoundaryCondition.free ∅)
    (markedJointBoxRawReveal n u v) (markedJointBoxRawReveal_stable n u v) H T
  intro A hAT
  have hAE : A ∈ E := by
    change A ∈ (RSW.stoppingObservationMap (markedJointBoxRawReveal n u v)) ⁻¹' T at hAT
    exact heq.symm ▸ hAT
  have hdir : u.val.1 < v.val.1 := by rw [hu,hv]; omega
  apply sourceBox_raw_record_core_probability_le_confined n hn ((n : ℝ)^η)
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) η) u v hu hv t b ht hut hvt A θ hAE.1
  · intro z hz
    rcases hAE.2.1 z hz with hlo | hT
    · exact Or.inr ((tubeLineOffset_nonpos_iff_deviation u.val v.val z.val t b hut hvt hdir).mp
        (le_of_lt (Finset.mem_filter.mp hlo).2.2))
    · exact Or.inl hT
  · intro z hz
    rcases hAE.2.2 z hz with hup | hT
    · exact Or.inr ((tubeLineOffset_nonneg_iff_deviation u.val v.val z.val t b hut hvt hdir).mp
        (le_of_lt (Finset.mem_filter.mp hup).2.2))
    · exact Or.inl hT

end
end PottsContinuity.Thm3.Prop4
