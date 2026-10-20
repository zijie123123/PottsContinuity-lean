module

public import PottsContinuity.Thm3.RSW.SeedComplementGeometry
public import PottsContinuity.Thm3.RSW.StoppingUpper

/-!
# Free localization of a confined actual cluster

For an arbitrary finite graph and vertex region W, the free probability that
x and y are connected and their actual cluster stays inside W is at most their
free connection probability in the induced graph on W. The exploration reveals
all clusters from Wᶜ, whose unexposed complement has the free law. This supplies
the localization step of DCST Lemma 5 without planar dual-circuit selection.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK Exploration
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance clusterLocalizationVertexFintype : Fintype V := Fintype.ofFinite V
local instance clusterLocalizationEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- An actual connection together with confinement of its whole cluster. -/
def confinedConnectionEvent (G : SimpleGraph V) (W : Set V) (x y : V) :
    Set (Configuration G) :=
  {A | ActualConnected G A x y ∧ ∀ z, ActualConnected G A x z → z ∈ W}

/-- Actual free connection probabilities are monotone between induced regions. -/
theorem free_induced_connection_probability_mono (θ : Parameters)
    (C W : Set V) (hCW : C ⊆ W) (x y : C) :
    (measure (G.induce C) θ (BoundaryCondition.free ∅)
      {A | ActualConnected (G.induce C) A x y}).toReal ≤
    (measure (G.induce W) θ (BoundaryCondition.free ∅)
      {A | ActualConnected (G.induce W) A ⟨x.val, hCW x.property⟩
        ⟨y.val, hCW y.property⟩}).toReal := by
  let f : C ↪ W := ⟨fun v => ⟨v.val, hCW v.property⟩,
    fun a b h => Subtype.ext (congrArg (fun z : W => z.val) h)⟩
  have hmap : (G.induce C).map f ≤ G.induce W := by
    intro a b hab
    obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj f _ a b).mp hab
    exact huv
  exact embedded_free_connection_probability_le_allq f hmap θ x y

/-- The confined connection probability on any attained exterior-seed record
is bounded by the same free probability in W, independently of the record. -/
theorem confinedConnection_record_probability_le (θ : Parameters) (W : Set V)
    (A₀ : Configuration G) (x y : W) :
    (((law G θ (BoundaryCondition.free Wᶜ)).filter
      (revealRecordEvent (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent
          (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset)
          (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
            (∅ : Set V) Wᶜ.toFinset A B h) A₀]
        exact frozenStateEvent_support θ (BoundaryCondition.free Wᶜ) _ _)).toMeasure
          (confinedConnectionEvent G W x.val y.val)).toReal ≤
      (measure (G.induce W) θ (BoundaryCondition.free ∅)
        {B | ActualConnected (G.induce W) B x y}).toReal := by
  let ξ := BoundaryCondition.free Wᶜ
  let reveal := FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset
  let C := FKC.FiniteFK.wiredAvoidingComplementSet G ∅ Wᶜ.toFinset A₀
  let hs : ∃ B ∈ revealRecordEvent reveal A₀, B ∈ (law G θ ξ).support := by
    rw [revealRecordEvent_eq_frozenStateEvent reveal
      (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
        (∅ : Set V) Wᶜ.toFinset A B h) A₀]
    exact frozenStateEvent_support θ ξ _ _
  let ρ := (law G θ ξ).filter (revealRecordEvent reveal A₀) hs
  change (ρ.toMeasure (confinedConnectionEvent G W x.val y.val)).toReal ≤ _
  by_cases hxy : x.val ∈ C ∧ y.val ∈ C
  · let xc : C := ⟨x.val, hxy.1⟩
    let yc : C := ⟨y.val, hxy.2⟩
    have hprob := boundarySeedRecord_connection_probability_allq θ ξ A₀ xc yc
    calc
      (ρ.toMeasure (confinedConnectionEvent G W x.val y.val)).toReal ≤
          (ρ.toMeasure {B | ActualConnected G B x.val y.val}).toReal :=
        measureReal_mono (fun _ h => h.1)
      _ = (measure (G.induce C) θ (BoundaryCondition.free ∅)
          {B | ActualConnected (G.induce C) B xc yc}).toReal :=
        congrArg ENNReal.toReal hprob
      _ ≤ _ := free_induced_connection_probability_mono θ C W
        (exteriorSeedComplement_subset W A₀) xc yc
  · have hzero : ρ.toMeasure (confinedConnectionEvent G W x.val y.val) = 0 := by
      apply (PMF.toMeasure_apply_eq_zero_iff _ MeasurableSpace.measurableSet_top).mpr
      apply Set.disjoint_left.mpr
      intro A hA hconf
      have hrec := ((PMF.mem_support_filter_iff hs).mp hA).1
      exact hxy (confinedConnection_mem_exteriorSeedRecord W A₀ A hrec x.val y.val
        hconf.1 hconf.2)
    rw [hzero, ENNReal.toReal_zero]
    exact ENNReal.toReal_nonneg

/-- Localization of a confined actual cluster under the genuine free finite FK
law. It holds for every finite graph, independent 0<p<1, and every real q≥1. -/
theorem free_confinedConnection_probability_le (θ : Parameters) (W : Set V) (x y : W) :
    (measure G θ (BoundaryCondition.free ∅)
      (confinedConnectionEvent G W x.val y.val)).toReal ≤
    (measure (G.induce W) θ (BoundaryCondition.free ∅)
      {A | ActualConnected (G.induce W) A x y}).toReal := by
  have h := stopped_event_upper_of_record_bounds θ (BoundaryCondition.free Wᶜ)
    (FKC.FiniteFK.wiredAvoidingClusterReveal G ∅ Wᶜ.toFinset)
    (fun A B h => FKC.FiniteFK.wiredAvoidingClusterReveal_consistent
      (∅ : Set V) Wᶜ.toFinset A B h)
    (confinedConnectionEvent G W x.val y.val)
    (measure (G.induce W) θ (BoundaryCondition.free ∅)
      {A | ActualConnected (G.induce W) A x y}).toReal
    (fun A₀ => confinedConnection_record_probability_le (G := G) θ W A₀ x y)
  have hlaw : law G θ (BoundaryCondition.free ∅) = law G θ (BoundaryCondition.free Wᶜ) :=
    law_eq_of_boundary_partition_eq θ _ _ rfl
  change ((law G θ (BoundaryCondition.free ∅)).toMeasure _).toReal ≤ _
  rw [hlaw]
  exact h

end
end PottsContinuity.RSW
