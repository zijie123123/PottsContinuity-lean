module

public import PottsContinuity.Infinite.ComparisonStatements
public import PottsContinuity.PD.RCInfinite.CylinderApproximation
public import PottsContinuity.PD.RCInfinite.SubgraphExhaustion

@[expose] public section

open MeasureTheory Filter Topology

namespace PottsContinuity.Infinite

open PottsContinuity
open PottsContinuity.PD
open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability
open PottsContinuity.PD.RCInfinite

noncomputable section

local instance finiteGraphEdgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _
local instance finiteGraphEdgeDecidableEq {V : Type*} [Finite V]
    (G : SimpleGraph V) : DecidableEq G.edgeSet := Classical.decEq _
local instance finiteBoxEdgeFintype (c : LatticeVertex) (r : ℕ) :
    Fintype (boxGraph c r).edgeSet := Fintype.ofFinite _
local instance finiteBoxEdgeDecidableEq (c : LatticeVertex) (r : ℕ) :
    DecidableEq (boxGraph c r).edgeSet := Classical.decEq _
attribute [local instance] configurationMeasurableSpace

/-- Read a finite embedded lattice graph from an infinite configuration. -/
def latticeGraphRestriction {V : Type*} [Finite V] (G : SimpleGraph V)
    (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (ω : LatticeConfiguration) : Configuration G := by
  classical
  exact Finset.univ.filter fun e =>
    ω (embeddedEdgeEmbedding G squareLattice f hG e) = true

/-- The whole-lattice event induced by an event on an embedded finite graph. -/
def latticeGraphEvent {V : Type*} [Finite V] (G : SimpleGraph V)
    (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (A : Set (Configuration G)) : Set LatticeConfiguration :=
  {ω | latticeGraphRestriction G f hG ω ∈ A}

theorem latticeGraphEvent_isCylinder {V : Type*} [Finite V]
    (G : SimpleGraph V) (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (A : Set (Configuration G)) : IsCylinder (latticeGraphEvent G f hG A) := by
  classical
  refine ⟨Finset.univ.map (embeddedEdgeEmbedding G squareLattice f hG), ?_⟩
  intro ω η hω
  have hrestr : latticeGraphRestriction G f hG ω =
      latticeGraphRestriction G f hG η := by
    apply Finset.ext
    intro e
    simp only [latticeGraphRestriction, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hω (embeddedEdgeEmbedding G squareLattice f hG e)
      (Finset.mem_map.mpr ⟨e, Finset.mem_univ _, rfl⟩)
  simp [latticeGraphEvent, hrestr]

def boxVertexEmbedding_of_mem {V : Type*} [Finite V]
    (f : V ↪ LatticeVertex) (r : ℕ)
    (hV : ∀ v, f v ∈ latticeBox (0, 0) r) :
    V ↪ BoxVertex (0, 0) r where
  toFun v := ⟨f v, hV v⟩
  inj' := by
    intro x y h
    apply f.injective
    exact congrArg (fun z : BoxVertex (0, 0) r => z.val) h

private theorem graph_map_boxGraph_of_mem {V : Type*} [Finite V]
    (G : SimpleGraph V) (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (r : ℕ) (hV : ∀ v, f v ∈ latticeBox (0, 0) r) :
    G.map (boxVertexEmbedding_of_mem f r hV) ≤ boxGraph (0, 0) r := by
  let fb := boxVertexEmbedding_of_mem f r hV
  intro x y hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj fb G x y).mp hxy
  have hmap : (G.map f).Adj (f u) (f v) :=
    (SimpleGraph.map_adj f G (f u) (f v)).mpr ⟨u, v, huv, rfl, rfl⟩
  have hadj : squareLattice.Adj (f u) (f v) := hG hmap
  change squareLattice.Adj (fb u).val (fb v).val
  exact hadj

theorem boxEdgeEmbedding_compatible_finiteGraph {V : Type*} [Finite V]
    (G : SimpleGraph V) (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (r : ℕ) (hV : ∀ v, f v ∈ latticeBox (0, 0) r)
    (fb : V ↪ BoxVertex (0, 0) r := boxVertexEmbedding_of_mem f r hV)
    (hfb : ∀ v, (fb v).val = f v)
    (hGH : G.map fb ≤ boxGraph (0, 0) r) (e : G.edgeSet) :
    boxEdgeEmbedding (0, 0) r
        (embeddedEdgeEmbedding G (boxGraph (0, 0) r) fb hGH e) =
      embeddedEdgeEmbedding G squareLattice f hG e := by
  apply Subtype.ext
  change Sym2.map (fun x : BoxVertex (0, 0) r => x.val)
      (Sym2.map fb e.val) = Sym2.map f e.val
  rw [Sym2.map_map]
  have hfun : ((fun x : BoxVertex (0, 0) r => x.val) ∘ fb) = f := by
    funext x
    exact hfb x
  rw [hfun]

theorem latticeGraphRestriction_boxExtension {V : Type*} [Finite V]
    (G : SimpleGraph V) (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (i : Fin 2) (r : ℕ) (hV : ∀ v, f v ∈ latticeBox (0, 0) r)
    (fb : V ↪ BoxVertex (0, 0) r := boxVertexEmbedding_of_mem f r hV)
    (hfb : ∀ v, (fb v).val = f v)
    (hGH : G.map fb ≤ boxGraph (0, 0) r)
    (C : Configuration (boxGraph (0, 0) r)) :
    latticeGraphRestriction G f hG (boxExtension i (0, 0) r C) =
      embeddedConfigurationRestriction G (boxGraph (0, 0) r) fb hGH C := by
  classical
  apply Finset.ext
  intro e
  have hcompat := boxEdgeEmbedding_compatible_finiteGraph G f hG r hV fb hfb hGH e
  simp only [latticeGraphRestriction, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_embeddedConfigurationRestriction]
  rw [← hcompat, boxExtension_at]
  simp

private theorem finiteGraph_free_event_le_box {V : Type*} [Finite V]
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (G : SimpleGraph V) (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (A : Set (Configuration G)) (hA : IsUpperSet A)
    (r : ℕ) (hV : ∀ v, f v ∈ latticeBox (0, 0) r) :
    (measure G (pdParameters p q hp0 hp1 hq) (BoundaryCondition.free ∅) A).toReal ≤
      (boxMeasure (pdParameters p q hp0 hp1 hq) 0 (0, 0) r :
        Measure LatticeConfiguration).real (latticeGraphEvent G f hG A) := by
  let fb := boxVertexEmbedding_of_mem f r hV
  have hGH : G.map fb ≤ boxGraph (0, 0) r :=
    graph_map_boxGraph_of_mem G f hG r hV
  let ev : Set (Configuration G) := A
  have hevUpper : IsUpperSet ev := hA
  let ind : Configuration G → ℝ := ev.indicator (fun _ => 1)
  have hind0 : ∀ C, 0 ≤ ind C := by
    intro C
    by_cases hC : C ∈ ev <;> simp [ind, hC]
  have hindMono : Monotone ind := by
    intro C D hCD
    by_cases hC : C ∈ ev
    · have hD := hevUpper hCD hC
      simp [ind, hC, hD]
    · simp only [ind, Set.indicator_of_notMem hC]
      exact hind0 D
  have hcmp := embedded_free_expectation_le G (boxGraph (0, 0) r) fb hGH
    (pdParameters p q hp0 hp1 hq) ∅ ∅ ind hind0 hindMono
  have hmeasureG : (measure G (pdParameters p q hp0 hp1 hq)
      (BoundaryCondition.free ∅) ev).toReal =
      expectation (law G (pdParameters p q hp0 hp1 hq)
        (BoundaryCondition.free ∅)) ind :=
    pmf_measureReal_eq_expectation _ _
  let outEvent : Set (Configuration (boxGraph (0, 0) r)) :=
    (embeddedConfigurationRestriction G (boxGraph (0, 0) r) fb hGH) ⁻¹' ev
  have hmeasureBox :
      (measure (boxGraph (0, 0) r) (pdParameters p q hp0 hp1 hq)
        (BoundaryCondition.free ∅) outEvent).toReal =
      expectation (law (boxGraph (0, 0) r) (pdParameters p q hp0 hp1 hq)
        (BoundaryCondition.free ∅)) (outEvent.indicator (fun _ => (1 : ℝ))) :=
    pmf_measureReal_eq_expectation _ _
  have hpoint : ∀ C : Configuration (boxGraph (0, 0) r),
      ind (embeddedConfigurationRestriction G (boxGraph (0, 0) r) fb hGH C) =
        (outEvent.indicator (fun _ => (1 : ℝ))) C := by
    intro C
    rfl
  have hexpect : expectation (law (boxGraph (0, 0) r)
      (pdParameters p q hp0 hp1 hq) (BoundaryCondition.free ∅))
      (fun C => ind (embeddedConfigurationRestriction G (boxGraph (0, 0) r) fb hGH C)) =
      expectation (law (boxGraph (0, 0) r) (pdParameters p q hp0 hp1 hq)
        (BoundaryCondition.free ∅)) (outEvent.indicator (fun _ => (1 : ℝ))) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro C hC
    change ((law (boxGraph (0, 0) r) (pdParameters p q hp0 hp1 hq)
      (BoundaryCondition.free ∅) C).toReal) *
        ind (embeddedConfigurationRestriction G (boxGraph (0, 0) r) fb hGH C) =
      ((law (boxGraph (0, 0) r) (pdParameters p q hp0 hp1 hq)
        (BoundaryCondition.free ∅) C).toReal) *
        (outEvent.indicator (fun _ => (1 : ℝ))) C
    exact congrArg (fun x => ((law (boxGraph (0, 0) r)
      (pdParameters p q hp0 hp1 hq) (BoundaryCondition.free ∅) C).toReal) * x) (hpoint C)
  have hboxEvent : (boxExtension 0 (0, 0) r) ⁻¹'
      latticeGraphEvent G f hG ev =
      outEvent := by
    ext C
    change latticeGraphRestriction G f hG (boxExtension 0 (0, 0) r C) ∈ ev ↔
      embeddedConfigurationRestriction G (boxGraph (0, 0) r) fb hGH C ∈ ev
    have hfb : ∀ v, (fb v).val = f v := fun _ => rfl
    rw [latticeGraphRestriction_boxExtension G f hG 0 r hV fb hfb hGH]
  have hboxEval :
      (boxMeasure (pdParameters p q hp0 hp1 hq) 0 (0, 0) r :
        Measure LatticeConfiguration).real (latticeGraphEvent G f hG ev) =
      (measure (boxGraph (0, 0) r) (pdParameters p q hp0 hp1 hq)
        (BoundaryCondition.free ∅) outEvent).toReal := by
    rw [Measure.real_def, boxMeasure_apply (pdParameters p q hp0 hp1 hq) 0 (0, 0) r
      (latticeGraphEvent_isCylinder G f hG ev).measurableSet, hboxEvent]
    rfl
  calc
    (measure G (pdParameters p q hp0 hp1 hq) (BoundaryCondition.free ∅) ev).toReal =
        expectation (law G (pdParameters p q hp0 hp1 hq)
          (BoundaryCondition.free ∅)) ind := hmeasureG
    _ ≤ expectation (law (boxGraph (0, 0) r) (pdParameters p q hp0 hp1 hq)
          (BoundaryCondition.free ∅))
        (fun C => ind (embeddedConfigurationRestriction G (boxGraph (0, 0) r) fb hGH C)) := hcmp
    _ = (measure (boxGraph (0, 0) r) (pdParameters p q hp0 hp1 hq)
          (BoundaryCondition.free ∅)
          ((embeddedConfigurationRestriction G (boxGraph (0, 0) r) fb hGH) ⁻¹' ev)).toReal :=
      hexpect.trans hmeasureBox.symm
    _ = _ := hboxEval.symm

theorem finite_graph_free_le_infinite_local {V : Type*} [Finite V]
    (p : Set.Icc (0 : ℝ) 1) (q : Set.Ioi (0 : ℝ))
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hq : 1 ≤ (q : ℝ))
    (G : SimpleGraph V) (f : V ↪ LatticeVertex) (hG : G.map f ≤ squareLattice)
    (A : Set (Configuration G)) (hA : IsUpperSet A)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit p q 0 μ) :
    (measure G (pdParameters p q hp0 hp1 hq) (BoundaryCondition.free ∅) A).toReal ≤
      μ.real (latticeGraphEvent G f hG A) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let θ := pdParameters p q hp0 hp1 hq
  let E := latticeGraphEvent G f hG A
  let S : Finset LatticeVertex := Finset.univ.image f
  let r₀ := subgraphBoxRadius S
  have hSbox : ∀ v, f v ∈ latticeBox (0, 0) r₀ := by
    intro v
    exact subgraph_subset_boxRadius S
      (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
  have hμPD : PottsContinuity.PD.IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ := by
    change PottsContinuity.PD.IsRCInfiniteVolumeLimit
      (pdParameters p q hp0 hp1 hq).toP (pdParameters p q hp0 hp1 hq).toQ 0 μ
    simpa only [pdParameters_toP, pdParameters_toQ] using
      isRCInfiniteVolumeLimit_to_PD_box p q 0 μ hμ
  have hlimit := tendsto_cylinder_probability θ 0 μ hμPD
    (latticeGraphEvent_isCylinder G f hG A)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlimit
  filter_upwards [eventually_ge_atTop r₀] with r hr
  have hV : ∀ v, f v ∈ latticeBox (0, 0) r := by
    intro v
    exact latticeBox_mono (0, 0) hr (hSbox v)
  simpa [θ, E] using finiteGraph_free_event_le_box p q hp0 hp1 hq G f hG A hA r hV

end
end PottsContinuity.Infinite
