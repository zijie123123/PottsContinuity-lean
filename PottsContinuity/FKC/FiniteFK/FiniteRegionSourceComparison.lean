-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteRegionSourceComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteRegionSourceEvent
public import PottsContinuity.FKC.FiniteFK.WiredAvoidingRecordConnection
public import PottsContinuity.FKC.FiniteFK.WiredAvoidingRegionComparison
public import PottsContinuity.FKC.FiniteFK.RevealRecordEventDisintegration
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory FiniteProbability
open scoped BigOperators

noncomputable section

attribute [local instance] configurationMeasurableSpace

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance sourceCmpConfigFintype : Fintype (Configuration G) := Fintype.ofFinite _
local instance sourceCmpConfigNonempty : Nonempty (Configuration G) := ⟨∅⟩
local instance sourceCmpConfigDiscrete : DiscreteMeasurableSpace (Configuration G) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance sourceCmpEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance sourceCmpEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

local instance sourceCmpRegionConfigFintype (H : Set V) :
    Fintype (Configuration (G.induce H)) := Fintype.ofFinite _
local instance sourceCmpRegionConfigNonempty (H : Set V) :
    Nonempty (Configuration (G.induce H)) := ⟨∅⟩
local instance sourceCmpRegionConfigDiscrete (H : Set V) :
    DiscreteMeasurableSpace (Configuration (G.induce H)) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance sourceCmpRegionEdgeFintype (H : Set V) :
    Fintype (G.induce H).edgeSet := Fintype.ofFinite _
local instance sourceCmpRegionEdgeDecidableEq (H : Set V) :
    DecidableEq (G.induce H).edgeSet := Classical.decEq _

/-- Actual connectivity to the wired set inside the finite region. -/
def finiteRegionWiredConnectionEvent (H W : Set V) (x : {v : V // v ∈ H}) :
    Set (Configuration (G.induce H)) :=
  {B | ∃ y : {v : V // v ∈ H}, y.val ∈ W ∧
    ActualConnected (G.induce H) B x y}

def sourceCmpOpenGraphRestrictionHom
    {V₁ V₂ : Type*} {G₁ : SimpleGraph V₁} {G₂ : SimpleGraph V₂}
    (f : V₁ ↪ V₂) (hG : G₁.map f ≤ G₂) (B : Configuration G₂) :
    openGraph G₁ (embeddedConfigurationRestriction G₁ G₂ f hG B) →g openGraph G₂ B where
  toFun := f
  map_rel' := by
    intro u v huv
    rw [openGraph_adj] at huv ⊢
    rcases huv with ⟨e, he, heval⟩
    refine ⟨embeddedEdgeEmbedding G₁ G₂ f hG e,
      (mem_embeddedConfigurationRestriction G₁ G₂ f hG B e).mp he, ?_⟩
    simp [embeddedEdgeEmbedding_coe, heval]

private theorem sourceCmp_restriction_connection_in_region
    (H W : Set V) (hWH : W ⊆ H) (A₀ : Configuration G)
    {x : V} (hxH : x ∈ H)
    (hxC : x ∈ wiredAvoidingComplementSet G W
      (wiredAvoidingRegionSeeds H) A₀)
    (B : Configuration (G.induce H))
    (hconn : ∃ y : wiredAvoidingComplementSet G W
        (wiredAvoidingRegionSeeds H) A₀,
      y.val ∈ W ∧ ActualConnected
        (G.induce (wiredAvoidingComplementSet G W
          (wiredAvoidingRegionSeeds H) A₀))
        (embeddedConfigurationRestriction
          (G.induce (wiredAvoidingComplementSet G W
            (wiredAvoidingRegionSeeds H) A₀)) (G.induce H)
          (wiredAvoidingRegionEmbedding H W hWH A₀)
          (wiredAvoidingRegionGraph_map_le H W hWH A₀) B)
        ⟨x, hxC⟩ y) :
    B ∈ finiteRegionWiredConnectionEvent (G := G) H W ⟨x, hxH⟩ := by
  let C := wiredAvoidingComplementSet G W (wiredAvoidingRegionSeeds H) A₀
  let f := wiredAvoidingRegionEmbedding H W hWH A₀
  let G₀ := G.induce C
  let G₁ := G.induce H
  let hG₀₁ := wiredAvoidingRegionGraph_map_le H W hWH A₀
  rcases hconn with ⟨y, hyW, hyconn⟩
  obtain ⟨p⟩ := (actualConnected_iff_walk G₀
    (embeddedConfigurationRestriction G₀ G₁ f hG₀₁ B)
    ⟨x, hxC⟩ y).mp hyconn
  have hp : (openGraph G₁ B).Reachable (f ⟨x, hxC⟩) (f y) := by
    exact (p.map (sourceCmpOpenGraphRestrictionHom f hG₀₁ B)).reachable
  have hfx : f ⟨x, hxC⟩ = ⟨x, hxH⟩ := by
    apply Subtype.ext
    rfl
  have hfyH : f y = ⟨y.val, hWH hyW⟩ := by
    apply Subtype.ext
    rfl
  have hconnH : ActualConnected G₁ B ⟨x, hxH⟩ ⟨y.val, hWH hyW⟩ := by
    rw [ActualConnected]
    simpa [hfx, hfyH] using hp
  exact ⟨⟨y.val, hWH hyW⟩, hyW, hconnH⟩

private theorem sourceCmp_filter_eq_of_fiber_eq
    {α : Type*} (p : PMF α) {s t : Set α} (hst : s = t)
    (hs : ∃ a ∈ s, a ∈ p.support) (ht : ∃ a ∈ t, a ∈ p.support) :
    p.filter s hs = p.filter t ht := by
  subst t
  have hproof : hs = ht := Subsingleton.elim _ _
  subst ht
  rfl

/-- The actual finite source event is bounded by the FK probability of reaching
its wired set inside the region, under the original boundary support condition. -/
theorem finiteRegionSourceEvent_probability_le_wiredRegion
    (q : ClusterWeight) (ξ : BoundaryCondition V) (H W : Set V)
    (hWH : W ⊆ H) (hξ : ξ.boundary ⊆ Hᶜ ∪ W)
    (x : V) (hxH : x ∈ H) :
    (measure G q ξ (finiteRegionSourceEvent H W x)).toReal ≤
      (measure (G.induce H) q
        (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
        (finiteRegionWiredConnectionEvent H W ⟨x, hxH⟩)).toReal := by
  classical
  let reveal := wiredAvoidingClusterReveal G W (wiredAvoidingRegionSeeds H)
  let r := revealRecordStatistic reveal
  let E := finiteRegionSourceEvent (G := G) H W x
  let p := law G q ξ
  let marginal := p.map (Set.rangeFactorization r)
  let sourceCmpRangeFintype : Fintype (Set.range r) := Fintype.ofFinite _
  have hp : ∀ A, p A ≠ 0 := fun A => (law_pos G q ξ A).ne'
  have hsum := law_toMeasure_event_toReal_eq_sum_revealRecord q ξ reveal E
  have hterm (y : Set.range r) :
      (marginal y).toReal *
        ((p.filter {A | r A = y.1}
          (by
            obtain ⟨A₀, hA₀⟩ := y.2
            exact ⟨A₀, hA₀, hp A₀⟩)).toMeasure E).toReal ≤
      (marginal y).toReal *
        (measure (G.induce H) q
          (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
          (finiteRegionWiredConnectionEvent H W ⟨x, hxH⟩)).toReal := by
    obtain ⟨A₀, hy⟩ := y.2
    have hyRecord : A₀ ∈ revealRecordEvent G reveal A₀ := by
      rw [← revealRecordStatistic_fiber_eq reveal A₀]
      exact rfl
    have hrecordSupport : ∃ A ∈ revealRecordEvent G reveal A₀, A ∈ p.support := by
      exact ⟨A₀, hyRecord, (p.mem_support_iff A₀).2 (hp A₀)⟩
    have hfiber : {A | r A = y.1} = revealRecordEvent G reveal A₀ := by
      ext A
      change (r A = y.1) ↔ A ∈ revealRecordEvent G reveal A₀
      rw [← revealRecordStatistic_fiber_eq reveal A₀]
      change (r A = y.1) ↔ r A = r A₀
      constructor
      · intro h
        exact h.trans hy.symm
      · intro h
        exact h.trans hy
    have hfilter : p.filter {A | r A = y.1}
        (by
          obtain ⟨A₀', hA₀'⟩ := y.2
          exact ⟨A₀', hA₀', hp A₀'⟩) =
        p.filter (revealRecordEvent G reveal A₀) hrecordSupport :=
      sourceCmp_filter_eq_of_fiber_eq p hfiber _ _
    by_cases hxC : x ∈ wiredAvoidingClusterSet G W
        (wiredAvoidingRegionSeeds H) A₀
    · have hdisj : Disjoint (p.filter (revealRecordEvent G reveal A₀)
          hrecordSupport).support E := by
        rw [PMF.support_filter]
        apply Set.disjoint_left.mpr
        intro A ⟨hrec, hps⟩ hE
        have hclusterA : x ∈ wiredAvoidingClusterSet G W
            (wiredAvoidingRegionSeeds H) A := by
          rw [wiredAvoidingClusterSet_eq_of_record W
            (wiredAvoidingRegionSeeds H) A₀ A hrec]
          exact hxC
        have hsource := (finiteRegionSourceEvent_mem_iff H W x A).mp hE
        exact hsource.2 hclusterA
      have hzero := (PMF.toMeasure_apply_eq_zero_iff _ (MeasurableSet.of_discrete)).2 hdisj
      have hcondzero : ((p.filter (revealRecordEvent G reveal A₀)
          hrecordSupport).toMeasure E).toReal = 0 := by
        rw [hzero]
        exact ENNReal.toReal_zero
      rw [hfilter, hcondzero]
      simp only [mul_zero]
      exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · let C := wiredAvoidingComplementSet G W
        (wiredAvoidingRegionSeeds H) A₀
      let G₀ := G.induce C
      let f₀ := wiredAvoidingComplementEmbedding G W
        (wiredAvoidingRegionSeeds H) A₀
      let hG₀ := wiredAvoidingComplementGraph_le (G := G) W
        (wiredAvoidingRegionSeeds H) A₀
      let D : Set (Configuration G₀) :=
        {B | ∃ y₀ : C, y₀.val ∈ W ∧ ActualConnected G₀ B ⟨x, hxC⟩ y₀}
      have hDupper : IsUpperSet D := by
        intro A B hAB hA
        rcases hA with ⟨y₀, hyW, hconn⟩
        exact ⟨y₀, hyW, actualConnected_mono hAB hconn⟩
      let hrecSupport : ∃ A ∈ revealRecordEvent G reveal A₀, A ∈ p.support := by
        rw [revealRecordEvent_eq_frozenStateEvent G reveal
          (fun A B hAB => wiredAvoidingClusterReveal_consistent W
            (wiredAvoidingRegionSeeds H) A B hAB) A₀]
        exact frozenStateEvent_support q ξ (reveal A₀)
          (revealRecordConfiguration G reveal A₀)
      have hmap : (p.filter (revealRecordEvent G reveal A₀) hrecSupport).map
          (embeddedConfigurationRestriction G₀ G f₀ hG₀) =
          law G₀ q (isolatedExtensionPullbackBoundary f₀
            (frozenBoundary ξ (revealRecordConfiguration G reveal A₀).val)) := by
        simpa [p, G₀, C, f₀, hG₀, reveal] using
          law_filter_wiredAvoidingClusterRecord_map_complement q ξ W
            (wiredAvoidingRegionSeeds H) A₀
      have hsubset : E ∩ revealRecordEvent G reveal A₀ ⊆
          (embeddedConfigurationRestriction G₀ G f₀ hG₀) ⁻¹' D := by
        intro A hA
        rcases hA with ⟨hE, hrec⟩
        have hconnOrig : ∃ w₀ : V, w₀ ∈ W ∧ ActualConnected G A x w₀ :=
          ((finiteRegionSourceEvent_mem_iff H W x A).mp hE).1
        have hxA : x ∉ wiredAvoidingClusterSet G W
            (wiredAvoidingRegionSeeds H) A := by
          have hset := wiredAvoidingClusterSet_eq_of_record W
            (wiredAvoidingRegionSeeds H) A₀ A hrec
          rw [hset]
          exact hxC
        have hconnComp := (wiredAvoidingConnection_toW_iff_record_complement W
          (wiredAvoidingRegionSeeds H) A₀ A hrec hxC).mp hconnOrig
        exact hconnComp
      have hmeasureSource :
          ((p.filter (revealRecordEvent G reveal A₀) hrecSupport).toMeasure E).toReal ≤
            (((p.filter (revealRecordEvent G reveal A₀) hrecSupport).map
              (embeddedConfigurationRestriction G₀ G f₀ hG₀)).toMeasure D).toReal := by
        have hsupp := PMF.toMeasure_apply_inter_support
          (p := p.filter (revealRecordEvent G reveal A₀) hrecSupport)
          (MeasurableSet.of_discrete (s := E))
        apply ENNReal.toReal_mono
        · exact ne_of_lt (measure_lt_top
            ((p.filter (revealRecordEvent G reveal A₀) hrecordSupport).map
              (embeddedConfigurationRestriction G₀ G f₀ hG₀)).toMeasure D)
        calc
          (p.filter (revealRecordEvent G reveal A₀) hrecSupport).toMeasure E =
              (p.filter (revealRecordEvent G reveal A₀) hrecSupport).toMeasure
                (E ∩ (p.filter (revealRecordEvent G reveal A₀) hrecSupport).support) := by
                  simpa [Set.inter_comm] using hsupp.symm
          _ ≤ (p.filter (revealRecordEvent G reveal A₀) hrecSupport).toMeasure
                ((embeddedConfigurationRestriction G₀ G f₀ hG₀) ⁻¹' D) :=
                measure_mono (by
                  intro A hA
                  exact hsubset ⟨hA.1, (PMF.mem_support_filter_iff (h := hrecSupport)).mp hA.2 |>.1⟩)
          _ = ((p.filter (revealRecordEvent G reveal A₀) hrecSupport).map
                (embeddedConfigurationRestriction G₀ G f₀ hG₀)).toMeasure D := by
                rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top
                  (MeasurableSet.of_discrete (s := D))]
      have hbound := wiredAvoidingComplement_conditioned_event_probability_le_regionWired
        q ξ H W hWH hξ A₀ D hDupper
      let fH := wiredAvoidingRegionEmbedding H W hWH A₀
      let hGH := wiredAvoidingRegionGraph_map_le H W hWH A₀
      have hpullback :
          {B | embeddedConfigurationRestriction G₀ (G.induce H) fH hGH B ∈ D} ⊆
            finiteRegionWiredConnectionEvent (G := G) H W ⟨x, hxH⟩ := by
        intro B hB
        rcases hB with ⟨y₀, hyW, hconn⟩
        exact sourceCmp_restriction_connection_in_region H W hWH A₀ hxH hxC B
          ⟨y₀, hyW, hconn⟩
      have hbound' :
          (measure G₀ q
            (isolatedExtensionPullbackBoundary f₀
              (frozenBoundary ξ (revealRecordConfiguration G reveal A₀).val)) D).toReal ≤
          (measure (G.induce H) q
            (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
            {B | embeddedConfigurationRestriction G₀ (G.induce H) fH hGH B ∈ D}).toReal := by
        change ((law G₀ q
          (isolatedExtensionPullbackBoundary f₀
            (frozenBoundary ξ (revealRecordConfiguration G reveal A₀).val))).toMeasure D).toReal ≤ _
        rw [← hmap]
        simpa [measure, G₀, C, f₀, hG₀, fH, hGH] using hbound
      have hregion :
          (measure (G.induce H) q
            (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
            {B | embeddedConfigurationRestriction G₀ (G.induce H) fH hGH B ∈ D}).toReal ≤
          (measure (G.induce H) q
            (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
            (finiteRegionWiredConnectionEvent H W ⟨x, hxH⟩)).toReal := by
        apply ENNReal.toReal_mono
        · exact ne_of_lt (measure_lt_top _ _)
        · exact measure_mono hpullback
      have hbound'' :
          (((p.filter (revealRecordEvent G reveal A₀) hrecSupport).map
            (embeddedConfigurationRestriction G₀ G f₀ hG₀)).toMeasure D).toReal ≤
          (measure (G.induce H) q
            (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
            (finiteRegionWiredConnectionEvent H W ⟨x, hxH⟩)).toReal := by
        have hmapMeasure :
            (((p.filter (revealRecordEvent G reveal A₀) hrecSupport).map
              (embeddedConfigurationRestriction G₀ G f₀ hG₀)).toMeasure D).toReal =
              (measure G₀ q
                (isolatedExtensionPullbackBoundary f₀
                  (frozenBoundary ξ (revealRecordConfiguration G reveal A₀).val)) D).toReal := by
          rw [hmap]
          rfl
        rw [hmapMeasure]
        exact le_trans hbound' hregion
      have hcond :
          ((p.filter {A | r A = y.1}
            (by
              obtain ⟨A₀', hA₀'⟩ := y.2
              exact ⟨A₀', hA₀', hp A₀'⟩)).toMeasure E).toReal ≤
          (measure (G.induce H) q
            (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
          (finiteRegionWiredConnectionEvent (G := G) H W ⟨x, hxH⟩)).toReal := by
        rw [hfilter]
        exact le_trans hmeasureSource hbound''
      exact mul_le_mul_of_nonneg_left hcond ENNReal.toReal_nonneg
  calc
    (measure G q ξ E).toReal =
      ∑ y : Set.range r,
        (marginal y).toReal *
          ((p.filter {A | r A = y.1}
            (by
              obtain ⟨A₀, hA₀⟩ := y.2
              exact ⟨A₀, hA₀, hp A₀⟩)).toMeasure E).toReal := by
        simpa [measure, p, r, marginal, E] using hsum
    _ ≤ ∑ y : Set.range r,
        (marginal y).toReal *
          (measure (G.induce H) q
            (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
            (finiteRegionWiredConnectionEvent H W ⟨x, hxH⟩)).toReal := by
        apply Finset.sum_le_sum
        intro y hy
        exact hterm y
    _ = (measure (G.induce H) q
          (BoundaryCondition.wired {v : {v : V // v ∈ H} | v.val ∈ W})
          (finiteRegionWiredConnectionEvent H W ⟨x, hxH⟩)).toReal := by
        rw [← Finset.sum_mul, sum_mass_toReal]
        ring

end
end PottsContinuity.FKC.FiniteFK
