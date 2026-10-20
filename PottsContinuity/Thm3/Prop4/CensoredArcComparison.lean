module

public import PottsContinuity.Thm3.Prop4.CensoredArcConnection
public import PottsContinuity.Thm3.Prop4.CensoredComplementLaw
public import PottsContinuity.Thm3.Prop4.InducedConnectionTransport
public import PottsContinuity.Thm3.Prop4.WiredTargetComparison
public import PottsContinuity.Thm3.RSW.StoppingUpper

/-!
# Direct finite-domain comparison for the source isolation event

Explore exterior clusters in the graph censored at the target wired arc.
The exact stopped law, proved arc partition domination and first-hit retention
replace a lowest-dual-path selector for this finite comparison.
-/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance censoredComparisonEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Actual arc connection together with the source's universal no-escape clause. -/
def finiteArcIsolationEvent (D W : Set V) (x : V) : Set (Configuration G) :=
  targetConnectionEvent x W ∩ {A | ∀ y : V, y ∉ D →
    ∀ p : (openGraph G A).Walk x y, ∃ z ∈ p.support, z ∈ W}

/-- The isolation event in any finite ambient domain costs at most a connection
in the target induced domain with just its prescribed arc wired. Boundary
conditions outside that domain are arbitrary. -/
theorem finite_arc_isolation_probability_le (θ : Parameters) (D W : Set V)
    (hWD : W ⊆ D) (ξ : BoundaryCondition V) (hξ : ξ.boundary ⊆ Dᶜ ∪ W) (x : D) :
    (measure G θ ξ (finiteArcIsolationEvent D W x.val)).toReal ≤
      (measure (G.induce D) θ (BoundaryCondition.wired (Subtype.val ⁻¹' W))
        (targetConnectionEvent x (Subtype.val ⁻¹' W))).toReal := by
  classical
  let reveal := censoredSeedReveal (arcCensoredGraph_le G W) Dᶜ
  let E := finiteArcIsolationEvent (G := G) D W x.val
  let c := (measure (G.induce D) θ (BoundaryCondition.wired (Subtype.val ⁻¹' W))
    (targetConnectionEvent x (Subtype.val ⁻¹' W))).toReal
  have hstable := censoredSeedReveal_stable (arcCensoredGraph_le G W) Dᶜ
  apply RSW.stopped_event_upper_of_record_bounds θ ξ reveal hstable E c
  intro A₀
  let hs : ∃ A ∈ Exploration.revealRecordEvent reveal A₀, A ∈ (law G θ ξ).support := by
    rw [Exploration.revealRecordEvent_eq_frozenStateEvent reveal hstable A₀]
    exact frozenStateEvent_support θ ξ _ _
  let ρ := (law G θ ξ).filter (Exploration.revealRecordEvent reveal A₀) hs
  let C := censoredSeedComplement (arcCensoredGraph_le G W) Dᶜ A₀
  have hCD : C ⊆ D := censoredArc_complement_subset_domain W D A₀
  have hSW : Disjoint Dᶜ W := Set.disjoint_left.mpr (fun _ hD hW => hD (hWD hW))
  have hWC : W ⊆ C := by
    intro w hw hc
    exact censoredArc_cluster_disjoint W Dᶜ hSW A₀ hc hw
  have hexclude : ∀ A ∈ E, A ∈ Exploration.revealRecordEvent reveal A₀ → x.val ∈ C := by
    intro A hA hrecord
    have hno := no_escape_excludes_censoredSeedCluster G W D A x.val hWD hA.2
    change x.val ∉ censoredSeedCluster (arcCensoredGraph_le G W) Dᶜ A₀
    rw [← censoredSeedCluster_eq_of_agreement (arcCensoredGraph_le G W) Dᶜ A₀ A hrecord.2]
    exact hno
  by_cases hx : x.val ∈ C
  · let xC : C := ⟨x.val,hx⟩
    let S : Set (Configuration (G.induce C)) :=
      targetConnectionEvent xC (RSW.inducedVertexEmbedding C ⁻¹' W)
    let η := isolatedExtensionPullbackBoundary (RSW.inducedVertexEmbedding C)
      (frozenBoundary ξ (Exploration.revealRecordConfiguration reveal A₀).val)
    have hmap := congrArg (fun p : PMF (Configuration (G.induce C)) => p.toMeasure S)
      (law_filter_censoredSeedRecord_map_complement θ ξ (arcCensoredGraph_le G W) Dᶜ A₀)
    change (ρ.map (RSW.inducedConfigurationRestriction C)).toMeasure S =
      measure (G.induce C) θ η S at hmap
    rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at hmap
    have hsub : ρ.toMeasure E ≤ ρ.toMeasure {A | RSW.inducedConfigurationRestriction C A ∈ S} := by
      apply ρ.toMeasure_mono MeasurableSpace.measurableSet_top
      intro A hA
      have hr := ((PMF.mem_support_filter_iff hs).mp hA.2).1
      have hsurvive := censoredArc_target_survives_record W Dᶜ hSW A₀ A x.val hr hx hA.1.1
      exact (inducedErasure_target_iff C W hWC A xC).mp hsurvive
    have hpart : η.partition ≤ (BoundaryCondition.wired (RSW.inducedVertexEmbedding C ⁻¹' W)).partition :=
      censoredArc_frozen_partition_le_wired W D hWD ξ hξ A₀
    let f : C ↪ D := ⟨fun z => ⟨z.val,hCD z.property⟩,fun a b h => Subtype.ext (congrArg (fun z : D => z.val) h)⟩
    have hG : (G.induce C).map f ≤ G.induce D := by
      intro a b hab
      obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj f _ a b).mp hab
      exact huv
    have hcompare := embedded_wired_target_probability_le (G.induce C) (G.induce D) f hG θ
      (Subtype.val ⁻¹' W) xC
    change (ρ.toMeasure E).toReal ≤ c
    calc
      _ ≤ (ρ.toMeasure {A | RSW.inducedConfigurationRestriction C A ∈ S}).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) hsub
      _ = (measure (G.induce C) θ η S).toReal := congrArg ENNReal.toReal hmap
      _ ≤ (measure (G.induce C) θ
          (BoundaryCondition.wired (RSW.inducedVertexEmbedding C ⁻¹' W)) S).toReal :=
        measure_boundary_comparison θ η _ hpart S (targetConnectionEvent_upper _ _)
      _ ≤ c := hcompare
  · have hzero : ρ.toMeasure E ≤ ρ.toMeasure ∅ := by
      apply ρ.toMeasure_mono MeasurableSpace.measurableSet_top
      intro A hA
      have hr := ((PMF.mem_support_filter_iff hs).mp hA.2).1
      exact False.elim (hx (hexclude A hA.1 hr))
    change (ρ.toMeasure E).toReal ≤ c
    have hle : (ρ.toMeasure E).toReal ≤ 0 := by
      have h := ENNReal.toReal_mono (measure_ne_top _ _) hzero
      simpa only [measure_empty,ENNReal.toReal_zero] using h
    exact hle.trans ENNReal.toReal_nonneg

end
end PottsContinuity.Thm3.Prop4
