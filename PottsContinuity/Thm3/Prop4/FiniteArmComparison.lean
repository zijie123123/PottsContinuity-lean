module

public import PottsContinuity.Thm3.Prop4.ClusterConnection
public import PottsContinuity.Infinite.FiniteGraphComparison
public import PottsContinuity.Thm3.RSW.ArmOpen
public import PottsContinuity.PD.RCInfinite.ClusterEvents

/-! # Finite embedded free target events bounded by the actual infinite arm -/

@[expose] public section

open MeasureTheory
namespace PottsContinuity.Thm3.Prop4
open PD.FK
noncomputable section
variable {V : Type*} [Finite V] (G : SimpleGraph V)
local instance finiteArmEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance finiteArmEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
attribute [local instance] configurationMeasurableSpace

/-- Reading the actual original edges of a finite embedded graph retains every
open path in the genuine infinite open graph. -/
def finiteRestrictionOpenHom (f : V ↪ (ℤ × ℤ)) (hG : G.map f ≤ squareLattice)
    (ω : squareLattice.edgeSet → Bool) :
    openGraph G (Infinite.latticeGraphRestriction G f hG ω) →g
      PottsContinuity.rcInfiniteOpenGraph ω where
  toFun := f
  map_rel' := by
    intro a b hab
    obtain ⟨e,he,heval⟩ := (openGraph_adj G _ a b).mp hab
    have hopen : ω (embeddedEdgeEmbedding G squareLattice f hG e) = true :=
      (Finset.mem_filter.mp he).2
    let ef := embeddedEdgeEmbedding G squareLattice f hG e
    have hef : ef.val = s(f a,f b) := by
      change Sym2.map f e.val = _
      rw [heval,Sym2.map_mk]
    have hmem : s(f a,f b) ∈ squareLattice.edgeSet := hef ▸ ef.property
    have heq : ef = ⟨s(f a,f b),hmem⟩ := Subtype.ext hef
    have htrue : ω ⟨s(f a,f b),hmem⟩ = true := by
      change ω ef = true at hopen
      simpa only [heq] using hopen
    change (SimpleGraph.fromEdgeSet {d | ∃ h : d ∈ squareLattice.edgeSet,
      ω ⟨d,h⟩ = true}).Adj (f a) (f b)
    rw [SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨hmem,htrue⟩,?_⟩
    have hadj : G.Adj a b := G.mem_edgeSet.mp (heval ▸ e.property)
    exact fun h => hadj.ne (f.injective h)

/-- All target points map to the same frozen boundary and the root maps to
zero, so the whole target event is bounded at once, with no endpoint sum. -/
theorem finite_free_target_le_infinite_arm (θ : Parameters)
    (f : V ↪ (ℤ × ℤ)) (hG : G.map f ≤ squareLattice) (u : V) (T : Set V) (r : ℕ)
    (hu : f u = (0,0))
    (hT : ∀ z ∈ T, f z ∈ PottsContinuity.vertexBoundary (PottsContinuity.box r))
    (μ : Measure (PottsContinuity.squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ) :
    (measure G θ (BoundaryCondition.free ∅) (targetConnectionEvent u T)).toReal ≤
      RSW.oneArmProbability μ r := by
  let : IsProbabilityMeasure μ := hμ.1
  have hθ : Infinite.pdParameters θ.toP θ.toQ (edgeParameter_pos θ)
      (edgeParameter_lt_one θ) θ.property = θ := by cases θ; rfl
  have hcmp := Infinite.finite_graph_free_le_infinite_local θ.toP θ.toQ
    (edgeParameter_pos θ) (edgeParameter_lt_one θ) θ.property G f hG
    (targetConnectionEvent u T) (targetConnectionEvent_upper u T) μ hμ
  rw [hθ] at hcmp
  apply hcmp.trans
  change μ.real (Infinite.latticeGraphEvent G f hG (targetConnectionEvent u T)) ≤
    μ.real (RSW.infiniteArmEvent r)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨z,hz,hconn⟩ := hω
  have hmap := SimpleGraph.Reachable.map (finiteRestrictionOpenHom G f hG ω) hconn
  change (PottsContinuity.rcInfiniteOpenGraph ω).Reachable (f u) (f z) at hmap
  rw [hu] at hmap
  exact ⟨f z,hT z hz,hmap⟩

end
end PottsContinuity.Thm3.Prop4
