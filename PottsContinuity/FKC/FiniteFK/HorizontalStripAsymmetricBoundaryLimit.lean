-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripAsymmetricBoundaryLimit.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripAsymmetricTopLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripBoundaryLimit
public import PottsContinuity.FKC.FiniteFK.HorizontalStripConditionalBoundary
public import PottsContinuity.FKC.FiniteFK.EmbeddedMarginalLaw
public import PottsContinuity.FKC.FiniteFK.Expectation
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents
public import PottsContinuity.FKC.FiniteFK.ClusterBoundaryDomination
public import PottsContinuity.FKC.FiniteFK.RectangleFlowDimension
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.Tactic

@[expose] public section

open Filter MeasureTheory Topology

namespace PottsContinuity.FKC.Medial
open PottsContinuity.FKC.FiniteFK
open FiniteProbability
noncomputable section

attribute [local instance] configurationMeasurableSpace

local instance asymSidesAnyConfigFintype {V : Type*} [Finite V] (G : SimpleGraph V) :
    Fintype (Configuration G) := Fintype.ofFinite _

local instance asymSidesEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripAsymmetricRectangle N n).edgeSet := Fintype.ofFinite _
local instance asymSidesOuterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance asymSidesOuterEdgeDecidableEq (N n : ℕ) :
    DecidableEq (horizontalStripAsymmetricRectangle N n).edgeSet := Classical.decEq _

private theorem rectanglePrimalEdgeToSquareEdge_val_local (a : LatticeVertex) (w h : ℕ)
    (e : (rectangleGraph a w h).edgeSet) :
    (rectanglePrimalEdgeToSquareEdge a w h e).val =
      Sym2.map (fun z : RectangleVertex a w h => z.val) e.val := rfl

def horizontalStripAsymmetricTopSidesSet (N n : ℕ) :
    Set (RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) :=
  {v | v.val.2 = (2 * n : ℤ) ∨ v.val.1 = -((N + 1 : ℕ) : ℤ) ∨
    v.val.1 = (N : ℤ)}

def horizontalStripAsymmetricTopSidesBoundary (N n : ℕ) :
    BoundaryCondition (RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) :=
  BoundaryCondition.wired (horizontalStripAsymmetricTopSidesSet N n)

def horizontalStripAsymmetricTopSidesProbabilityMeasure (q : ClusterWeight)
    (N n : ℕ) : ProbabilityMeasure LatticeConfiguration := by
  let G := horizontalStripAsymmetricRectangle N n
  let ξ := horizontalStripAsymmetricTopSidesBoundary N n
  let ν : PMF LatticeConfiguration :=
    (law G q ξ).map (horizontalStripAsymmetricPlaneExtension N n)
  exact ⟨ν.toMeasure, PMF.toMeasure.isProbabilityMeasure _⟩

theorem horizontalStripAsymmetricTopSidesProbabilityMeasure_apply_preimage
    (q : ClusterWeight) (N n : ℕ) (s : Set LatticeConfiguration) (hs : MeasurableSet s) :
    (horizontalStripAsymmetricTopSidesProbabilityMeasure q N n : Measure LatticeConfiguration) s =
      measure (horizontalStripAsymmetricRectangle N n) q
        (horizontalStripAsymmetricTopSidesBoundary N n)
        {A | horizontalStripAsymmetricPlaneExtension N n A ∈ s} := by
  change ((law (horizontalStripAsymmetricRectangle N n) q
      (horizontalStripAsymmetricTopSidesBoundary N n)).map
    (horizontalStripAsymmetricPlaneExtension N n)).toMeasure s = _
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hs]
  rfl

theorem horizontalStripAsymmetricTopSidesProbabilityMeasure_allOpen
    (q : ClusterWeight) (N n : ℕ) (F : Finset squareLattice.edgeSet) :
    (horizontalStripAsymmetricTopSidesProbabilityMeasure q N n : Measure LatticeConfiguration)
      (LatticeConfiguration.allOpen F) =
    measure (horizontalStripAsymmetricRectangle N n) q
      (horizontalStripAsymmetricTopSidesBoundary N n)
      (horizontalStripIntervalCylinderEvent (-((N + 1 : ℕ) : ℤ)) (2 * N + 1) n F) := by
  rw [horizontalStripAsymmetricTopSidesProbabilityMeasure_apply_preimage q N n
    (LatticeConfiguration.allOpen F)
    (LatticeConfiguration.allOpen_isClopen F).isOpen.measurableSet]
  congr 1
  ext A
  simp only [LatticeConfiguration.allOpen, Set.mem_ofPred_eq,
    horizontalStripAsymmetricPlaneExtension, horizontalStripIntervalCylinderEvent,
    horizontalStripAsymmetricRectangle, Finset.subset_iff,
    decide_eq_true_eq]

local instance asymSidesCenterEdgeFintype (N n : ℕ) :
    Fintype (horizontalStripCutRectangle N n).edgeSet := Fintype.ofFinite _
local instance asymSidesConfigFintype (N n : ℕ) :
    Fintype (Configuration (horizontalStripAsymmetricRectangle N n)) := Fintype.ofFinite _
local instance asymSidesCenterConfigFintype (N n : ℕ) :
    Fintype (Configuration (horizontalStripCutRectangle N n)) := Fintype.ofFinite _

private theorem measure_toReal_eq_expectation_local
    {V : Type*} [Finite V] {G : SimpleGraph V} (q : ClusterWeight)
    (ξ : BoundaryCondition V) (S : Set (Configuration G)) :
    (measure G q ξ S).toReal =
      expectation (law G q ξ) (S.indicator (fun _ => (1 : ℝ))) := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : Fintype (Configuration G) := Fintype.ofFinite _
  rw [measure_toReal_eq_indicator_sum]
  unfold expectation
  apply Finset.sum_congr
  · ext A
    simp only [Finset.mem_univ]
  · intro A hA
    simp [law_apply, ENNReal.toReal_ofReal (configurationProbability_pos G q ξ A).le]

private theorem embedded_marginal_probability_le_of_frozen_partition
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
    (hGH : G.map f ≤ H) (q : ClusterWeight) (ξ : BoundaryCondition W)
    (η : BoundaryCondition V)
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤ η.partition)
    (S : Set (Configuration G)) (hS : IsUpperSet S) :
    (measure H q ξ {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal ≤
      (measure G q η S).toReal := by
  classical
  let : Fintype G.edgeSet := Fintype.ofFinite _
  let : Fintype H.edgeSet := Fintype.ofFinite _
  let : Fintype (Configuration G) := Fintype.ofFinite _
  let : Fintype (Configuration H) := Fintype.ofFinite _
  let : Fintype (RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :=
    Fintype.ofFinite _
  let ρ := embeddedConfigurationRestriction G H f hGH
  let φ := S.indicator (fun _ => (1 : ℝ))
  let p := law H q ξ
  let Klaw := frozenMarginalLaw q ξ (subgraphRemovedEdges (G.map f) H)
  let Q := fun K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H) =>
    law G q (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val))
  have houter :
      (measure H q ξ {A | ρ A ∈ S}).toReal = expectation p (fun A => φ (ρ A)) := by
    rw [measure_toReal_eq_expectation_local]
    change expectation (law H q ξ) ({A | ρ A ∈ S}.indicator (fun _ => (1 : ℝ))) =
      expectation (law H q ξ) (fun A => φ (ρ A))
    congr 1
  have hmap : p.map ρ = Klaw.bind Q := by
    dsimp [p, Klaw, Q, ρ]
    exact law_embeddedConfigurationRestriction_eq_bind_frozenMarginal G H f hGH q ξ
  have hcond (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
      expectation (Q K) φ ≤ expectation (law G q η) φ := by
    have h := measure_boundary_comparison q
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) η (hpart K) S hS
    change expectation (law G q
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)))
      (S.indicator (fun _ => (1 : ℝ))) ≤
      expectation (law G q η) (S.indicator (fun _ => (1 : ℝ)))
    rw [← measure_toReal_eq_expectation_local q
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S,
      ← measure_toReal_eq_expectation_local q η S]
    exact h
  have htarget := measure_toReal_eq_expectation_local q η S
  calc
    (measure H q ξ {A | ρ A ∈ S}).toReal = expectation p (fun A => φ (ρ A)) := houter
    _ = expectation (p.map ρ) φ := by rw [expectation_map]
    _ = expectation (Klaw.bind Q) φ := by rw [hmap]
    _ ≤ expectation Klaw (fun _ => expectation (law G q η) φ) := by
      rw [expectation_bind]
      apply expectation_mono
      intro K
      exact hcond K
    _ = expectation (law G q η) φ := by rw [expectation_const]
    _ = (measure G q η S).toReal := htarget.symm

 theorem asymSides_contains_centered (N n : ℕ) :
    latticeRectangle (-(N : ℤ), 0) (2 * N) (2 * n) ⊆
      latticeRectangle (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n) := by
  intro v hv
  rw [mem_latticeRectangle] at hv ⊢
  rcases hv with ⟨⟨hlo, hhi⟩, hy⟩
  constructor
  · constructor <;> omega
  · exact hy

def asymSidesCenterEmbedding (N n : ℕ) :
    RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) ↪
      RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n) :=
  rectangleVertexEmbedding (asymSides_contains_centered N n)

@[simp] private theorem asymSidesCenterEmbedding_val (N n : ℕ)
    (v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n)) :
    (asymSidesCenterEmbedding N n v).val = v.val := rfl

private theorem asymSidesCenter_map_le (N n : ℕ) :
    (horizontalStripCutRectangle N n).map
      (asymSidesCenterEmbedding N n) ≤
        rectangleGraph (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) := by
  change (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).map
      (asymSidesCenterEmbedding N n) ≤
    rectangleGraph (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)
  exact rectangleGraph_map_rectangleVertexEmbedding (asymSides_contains_centered N n)

private theorem asymSides_removedEdge_endpoints_zone (N n : ℕ)
    (e : (horizontalStripAsymmetricRectangle N n).edgeSet)
    (he : e.val ∉ ((rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).map
      (asymSidesCenterEmbedding N n)).edgeSet) :
    ∀ ⦃u : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)⦄,
      u ∈ e.val → u.val.1 = -((N + 1 : ℕ) : ℤ) ∨ u.val.1 = -(N : ℤ) := by
  classical
  let p := e.val.out
  have hrepr : s(p.1, p.2) = e.val := Quot.out_eq _
  have hadj : (horizontalStripAsymmetricRectangle N n).Adj p.1 p.2 := by
    apply (horizontalStripAsymmetricRectangle N n).mem_edgeSet.mp
    rw [hrepr]
    exact e.property
  have hsq := (rectangleGraph_adj_iff _ _ _ _ _).mp hadj
  have hp1 := p.1.property
  have hp2 := p.2.property
  rw [mem_latticeRectangle] at hp1 hp2
  have hbounds1 : -((N + 1 : ℕ) : ℤ) ≤ p.1.val.1 ∧
      p.1.val.1 ≤ (N : ℤ) ∧ 0 ≤ p.1.val.2 ∧ p.1.val.2 ≤ (2 * n : ℤ) := by
    rcases hp1 with ⟨⟨hlo, hhi⟩, ⟨hylo, hyhi⟩⟩
    constructor
    · exact hlo
    · constructor
      · push_cast at hhi ⊢; omega
      · exact ⟨hylo, by push_cast at hyhi ⊢; omega⟩
  have hbounds2 : -((N + 1 : ℕ) : ℤ) ≤ p.2.val.1 ∧
      p.2.val.1 ≤ (N : ℤ) ∧ 0 ≤ p.2.val.2 ∧ p.2.val.2 ≤ (2 * n : ℤ) := by
    rcases hp2 with ⟨⟨hlo, hhi⟩, ⟨hylo, hyhi⟩⟩
    constructor
    · exact hlo
    · constructor
      · push_cast at hhi ⊢; omega
      · exact ⟨hylo, by push_cast at hyhi ⊢; omega⟩
  have hnotboth : ¬ (-(N : ℤ) ≤ p.1.val.1 ∧ -(N : ℤ) ≤ p.2.val.1) := by
    intro hboth
    let u : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
      ⟨p.1.val, by
        rw [mem_latticeRectangle]
        constructor
        · constructor <;> omega
        · constructor <;> omega⟩
    let v : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
      ⟨p.2.val, by
        rw [mem_latticeRectangle]
        constructor
        · constructor <;> omega
        · constructor <;> omega⟩
    have hin : (rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).Adj u v := by
      apply (rectangleGraph_adj_iff (-(N : ℤ), 0) (2 * N) (2 * n) u v).2
      exact hsq
    have hmap : ((rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).map
        (asymSidesCenterEmbedding N n)).Adj
          (asymSidesCenterEmbedding N n u) (asymSidesCenterEmbedding N n v) :=
      (SimpleGraph.map_adj _ _ _ _).mpr ⟨u, v, hin, rfl, rfl⟩
    have he' : e.val = s(asymSidesCenterEmbedding N n u,
        asymSidesCenterEmbedding N n v) := by
      rw [← hrepr]
      apply (Sym2.eq_iff).2
      left
      constructor <;> apply Subtype.ext <;> rfl
    exact he (by
      rw [he']
      exact ((rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).map
        (asymSidesCenterEmbedding N n)).mem_edgeSet.mpr hmap)
  have hNm1 : -((N + 1 : ℕ) : ℤ) = -(N : ℤ) - 1 := by push_cast; omega
  have hcoords : p.1.val.1 = -(N : ℤ) - 1 ∨ p.1.val.1 = -(N : ℤ) := by
    by_cases hleft : p.1.val.1 < -(N : ℤ)
    · exact Or.inl (by omega)
    · have hright : -(N : ℤ) ≤ p.1.val.1 := le_of_not_gt hleft
      have hleft2 : p.2.val.1 < -(N : ℤ) := by
        by_contra h
        exact hnotboth ⟨hright, le_of_not_gt h⟩
      rcases hsq with ⟨hhor, hy⟩ | ⟨hx, hvert⟩
      · rcases hhor with h | h <;> exact Or.inr (by omega)
      · exact Or.inr (by omega)
  have hcoords' : p.2.val.1 = -(N : ℤ) - 1 ∨ p.2.val.1 = -(N : ℤ) := by
    by_cases hleft : p.2.val.1 < -(N : ℤ)
    · exact Or.inl (by omega)
    · have hright : -(N : ℤ) ≤ p.2.val.1 := le_of_not_gt hleft
      have hleft1 : p.1.val.1 < -(N : ℤ) := by
        by_contra h
        exact hnotboth ⟨le_of_not_gt h, hright⟩
      rcases hsq with ⟨hhor, hy⟩ | ⟨hx, hvert⟩
      · rcases hhor with h | h <;> exact Or.inr (by omega)
      · exact Or.inr (by omega)
  have hmember (u : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n))
      (hu : u ∈ e.val) : u.val = p.1.val ∨ u.val = p.2.val := by
    rw [← hrepr] at hu
    rcases (Sym2.mem_iff').mp hu with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  intro u hu
  rcases hmember u hu with h | h
  · rcases hcoords with hcoord | hcoord
    · left
      rw [h, hcoord]
      omega
    · right
      rw [h, hcoord]
  · rcases hcoords' with hcoord | hcoord
    · left
      rw [h, hcoord]
      omega
    · right
      rw [h, hcoord]

private theorem asymSides_frozen_partition_le_centerSides (N n : ℕ)
    (K : RemovedConfiguration (horizontalStripAsymmetricRectangle N n)
      (subgraphRemovedEdges
        ((rectangleGraph (-(N : ℤ), 0) (2 * N) (2 * n)).map
          (asymSidesCenterEmbedding N n))
        (horizontalStripAsymmetricRectangle N n))) :
    (isolatedExtensionPullbackBoundary (asymSidesCenterEmbedding N n)
      (frozenBoundary (horizontalStripAsymmetricTopSidesBoundary N n) K.val)).partition ≤
      (horizontalStripTopSidesBoundary N n).partition := by
  classical
  let ξ := horizontalStripAsymmetricTopSidesBoundary N n
  let D : Set (RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) :=
    {v | v.val.1 = -((N + 1 : ℕ) : ℤ) ∨ v.val.1 = -(N : ℤ)}
  have hcomp := componentSetoid_le_wired_union_of_edge_endpoints ξ D K.val (by
    intro e he u hu
    have hnot := (mem_subgraphRemovedEdges e).mp (K.property he)
    exact asymSides_removedEdge_endpoints_zone N n e hnot hu)
  intro u v huv
  have houter := hcomp huv
  rcases (BoundaryCondition.wired_rel _ _ _).mp houter with hEq | ⟨huOuter, hvOuter⟩
  · exact Or.inl ((asymSidesCenterEmbedding N n).injective hEq)
  · right
    constructor
    · change asymSidesCenterEmbedding N n u ∈ ξ.boundary ∪ D at huOuter
      rcases huOuter with hξ | hD
      · change (asymSidesCenterEmbedding N n u).val.2 = _ ∨
          (asymSidesCenterEmbedding N n u).val.1 = -((N + 1 : ℕ) : ℤ) ∨
          (asymSidesCenterEmbedding N n u).val.1 = (N : ℤ) at hξ
        simp only [asymSidesCenterEmbedding_val] at hξ
        rcases hξ with hy | hleft | hright
        · exact Or.inl hy
        · have hlow := u.property
          rw [mem_latticeRectangle] at hlow
          exact False.elim (by omega)
        · exact Or.inr (Or.inr hright)
      · change (asymSidesCenterEmbedding N n u).val.1 = -((N + 1 : ℕ) : ℤ) ∨
          (asymSidesCenterEmbedding N n u).val.1 = -(N : ℤ) at hD
        simp only [asymSidesCenterEmbedding_val] at hD
        rcases hD with h | h
        · exfalso
          have := u.property
          rw [mem_latticeRectangle] at this
          omega
        · exact Or.inr (Or.inl h)
    · change asymSidesCenterEmbedding N n v ∈ ξ.boundary ∪ D at hvOuter
      rcases hvOuter with hξ | hD
      · change (asymSidesCenterEmbedding N n v).val.2 = _ ∨
          (asymSidesCenterEmbedding N n v).val.1 = -((N + 1 : ℕ) : ℤ) ∨
          (asymSidesCenterEmbedding N n v).val.1 = (N : ℤ) at hξ
        simp only [asymSidesCenterEmbedding_val] at hξ
        rcases hξ with hy | hleft | hright
        · exact Or.inl hy
        · have hlow := v.property
          rw [mem_latticeRectangle] at hlow
          exact False.elim (by omega)
        · exact Or.inr (Or.inr hright)
      · change (asymSidesCenterEmbedding N n v).val.1 = -((N + 1 : ℕ) : ℤ) ∨
          (asymSidesCenterEmbedding N n v).val.1 = -(N : ℤ) at hD
        simp only [asymSidesCenterEmbedding_val] at hD
        rcases hD with h | h
        · exfalso
          have := v.property
          rw [mem_latticeRectangle] at this
          omega
        · exact Or.inr (Or.inl h)

def horizontalStripAsymmetricTopSidesProbabilityMeasures (q : ClusterWeight) (n : ℕ) :
    ℕ → ProbabilityMeasure LatticeConfiguration :=
  fun N => horizontalStripAsymmetricTopSidesProbabilityMeasure q N n

def horizontalStripCenterTopSidesProbabilityMeasures (q : ClusterWeight) (n : ℕ) :
    ℕ → ProbabilityMeasure LatticeConfiguration :=
  fun N => horizontalStripRectangleProbabilityMeasure q N n
    (horizontalStripTopSidesBoundary N n)

private theorem asymSides_centerTopSides_tendsto
    (q : ClusterWeight) (n : ℕ) (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    Tendsto (horizontalStripCenterTopSidesProbabilityMeasures q n) atTop (𝓝 μ) := by
  apply horizontalStripBoundaryProbabilityMeasures_tendsto_of_topWired q n
    (fun N => horizontalStripTopSidesBoundary N n) (by
      intro N
      exact fun _ hx => hx) (by
      intro N
      change (BoundaryCondition.wired (horizontalStripTopWiredSet N n)).partition ≤
        (BoundaryCondition.wired (horizontalStripTopSidesSet N n)).partition
      intro u v huv
      rw [BoundaryCondition.wired_rel] at huv ⊢
      rcases huv with heq | ⟨hu, hv⟩
      · exact Or.inl heq
      · exact Or.inr ⟨Or.inl hu, Or.inl hv⟩) μ hμ

private theorem asymSides_centerCylinder_upper (N n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    IsUpperSet (horizontalStripRectangleCylinderEvent N n F) := by
  intro A B hAB hA
  exact hA.trans (Finset.image_mono _ hAB)

private theorem asymSides_innerEdge_compatible (N n : ℕ)
    (e : (horizontalStripCutRectangle N n).edgeSet) :
    rectanglePrimalEdgeToSquareEdge (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n)
        (embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
          (rectangleGraph (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n))
          (asymSidesCenterEmbedding N n)
          (asymSidesCenter_map_le N n) e) =
      horizontalStripRectangleOriginalEdge N n e := by
  apply Subtype.ext
  change (rectanglePrimalEdgeToSquareEdge (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n)
        (embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
          (rectangleGraph (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n))
          (asymSidesCenterEmbedding N n)
          (asymSidesCenter_map_le N n) e)).val =
      (horizontalStripRectangleOriginalEdge N n e).val
  rw [rectanglePrimalEdgeToSquareEdge_val_local, horizontalStripRectangleOriginalEdge_val,
    embeddedEdgeEmbedding_coe]
  change Sym2.map (fun z : RectangleVertex (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n) => z.val)
      (Sym2.map (asymSidesCenterEmbedding N n) e.val) =
    Sym2.map (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z.val) e.val
  rw [Sym2.map_map]
  congr 1

private theorem asymSides_restrictionCylinder_subset (N n : ℕ)
    (F : Finset squareLattice.edgeSet) :
    {A : Configuration (horizontalStripAsymmetricRectangle N n) |
      embeddedConfigurationRestriction (horizontalStripCutRectangle N n)
        (horizontalStripAsymmetricRectangle N n) (asymSidesCenterEmbedding N n)
        (asymSidesCenter_map_le N n) A ∈ horizontalStripRectangleCylinderEvent N n F} ⊆
    horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F := by
  intro A hA e he
  obtain ⟨e₀, he₀, hEq⟩ := Finset.mem_image.mp (hA he)
  have he₀A : embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
      (horizontalStripAsymmetricRectangle N n) (asymSidesCenterEmbedding N n)
      (asymSidesCenter_map_le N n) e₀ ∈ A :=
    (mem_embeddedConfigurationRestriction _ _ _ _ A _).mp he₀
  refine Finset.mem_image.mpr ⟨embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
      (horizontalStripAsymmetricRectangle N n) (asymSidesCenterEmbedding N n)
      (asymSidesCenter_map_le N n) e₀, he₀A, ?_⟩
  exact (asymSides_innerEdge_compatible N n e₀).trans hEq

private theorem asymSides_restrictionCylinder_iff_of_support (N n : ℕ)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge N n))
    (A : Configuration (horizontalStripAsymmetricRectangle N n)) :
    A ∈ horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F ↔
      embeddedConfigurationRestriction (horizontalStripCutRectangle N n)
        (horizontalStripAsymmetricRectangle N n) (asymSidesCenterEmbedding N n)
        (asymSidesCenter_map_le N n) A ∈ horizontalStripRectangleCylinderEvent N n F := by
  constructor
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp (hA he)
    have hcompat := asymSides_innerEdge_compatible N n x
    have hyx : embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
        (horizontalStripAsymmetricRectangle N n) (asymSidesCenterEmbedding N n)
        (asymSidesCenter_map_le N n) x = y := by
      apply Subtype.ext
      have heq := congrArg Subtype.val (hcompat.trans (by simpa only [hx] using hye.symm))
      change Sym2.map (fun z : RectangleVertex (-(N + 1 : ℤ), 0)
          (2 * N + 1) (2 * n) => z.val)
          (embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
            (horizontalStripAsymmetricRectangle N n) (asymSidesCenterEmbedding N n)
            (asymSidesCenter_map_le N n) x).val =
        Sym2.map (fun z : RectangleVertex (-(N + 1 : ℤ), 0)
          (2 * N + 1) (2 * n) => z.val) y.val at heq
      exact Sym2.map.injective Subtype.val_injective heq
    have hy' : embeddedEdgeEmbedding (horizontalStripCutRectangle N n)
        (horizontalStripAsymmetricRectangle N n) (asymSidesCenterEmbedding N n)
        (asymSidesCenter_map_le N n) x ∈ A := by rw [hyx]; exact hy
    have hr := (mem_embeddedConfigurationRestriction _ _ _ _ A x).mpr hy'
    exact Finset.mem_image.mpr ⟨x, hr, hx⟩
  · exact fun hA => asymSides_restrictionCylinder_subset N n F hA

private theorem asymSides_support_implies_center_support (N n : ℕ)
    (F : Finset squareLattice.edgeSet)
    (hF : ∃ A : Configuration (horizontalStripAsymmetricRectangle N n),
      A ∈ horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F) :
    ∃ K : ℕ, ∀ e ∈ F,
      e ∈ Set.range (horizontalStripRectangleOriginalEdge K n) := by
  classical
  let inc : RectangleVertex (-((N + 1 : ℕ) : ℤ), 0) (2 * N + 1) (2 * n) ↪
      RectangleVertex (-((N + 1 : ℕ) : ℤ), 0) (2 * (N + 1)) (2 * n) :=
    rectangleVertexEmbedding (by
      intro v hv
      rw [mem_latticeRectangle] at hv ⊢
      rcases hv with ⟨⟨hlo, hhi⟩, hy⟩
      refine ⟨⟨hlo, ?_⟩, hy⟩
      push_cast at hhi ⊢
      omega)
  have hmap : (horizontalStripAsymmetricRectangle N n).map inc ≤
      rectangleGraph (-((N + 1 : ℕ) : ℤ), 0) (2 * (N + 1)) (2 * n) := by
    change (rectangleGraph (-((N + 1 : ℕ) : ℤ), 0) (2 * N + 1) (2 * n)).map inc ≤ _
    exact rectangleGraph_map_rectangleVertexEmbedding (by
      intro v hv
      rw [mem_latticeRectangle] at hv ⊢
      rcases hv with ⟨⟨hlo, hhi⟩, hy⟩
      refine ⟨⟨hlo, ?_⟩, hy⟩
      push_cast at hhi ⊢
      omega)
  obtain ⟨A, hA⟩ := hF
  refine ⟨N + 1, ?_⟩
  intro e he
  have hmem : e ∈ A.image (rectanglePrimalEdgeToSquareEdge (-(N + 1 : ℤ), 0)
      (2 * N + 1) (2 * n)) := by
    simpa [horizontalStripIntervalCylinderEvent] using hA he
  obtain ⟨x, hxA, hxe⟩ := Finset.mem_image.mp hmem
  let y := embeddedEdgeEmbedding (horizontalStripAsymmetricRectangle N n)
      (rectangleGraph (-((N + 1 : ℕ) : ℤ), 0) (2 * (N + 1)) (2 * n)) inc hmap x
  have hcompat : rectanglePrimalEdgeToSquareEdge (-((N + 1 : ℕ) : ℤ), 0)
        (2 * (N + 1)) (2 * n) y =
      rectanglePrimalEdgeToSquareEdge (-(N + 1 : ℤ), 0) (2 * N + 1) (2 * n) x := by
    apply Subtype.ext
    change Sym2.map (fun z : RectangleVertex (-((N + 1 : ℕ) : ℤ), 0)
        (2 * (N + 1)) (2 * n) => z.val)
        (Sym2.map inc x.val) =
      Sym2.map (fun z : RectangleVertex (-(N + 1 : ℤ), 0)
        (2 * N + 1) (2 * n) => z.val) x.val
    rw [Sym2.map_map]
    congr 1
  exact ⟨y, hcompat.trans hxe⟩

private theorem asymSides_interval_empty_of_no_center_support (N n : ℕ)
    (F : Finset squareLattice.edgeSet)
    (hNo : ¬ ∃ K : ℕ, ∀ e ∈ F,
      e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)) :
    horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F = ∅ := by
  ext A
  constructor
  · intro hA
    exact False.elim (hNo (asymSides_support_implies_center_support N n F ⟨A, hA⟩))
  · simp

private theorem horizontalStripOriginalEdge_range_mono {K N n : ℕ} (hKN : K ≤ N)
    (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)) :
    ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge N n) := by
  intro e he
  obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
  let f : RectangleVertex (-(K : ℤ), 0) (2 * K) (2 * n) ↪
      RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) :=
    rectangleVertexEmbedding (horizontalStripRectangle_subset (n := n) hKN)
  have hmap : (horizontalStripCutRectangle K n).map f ≤ horizontalStripCutRectangle N n :=
    rectangleGraph_map_rectangleVertexEmbedding (horizontalStripRectangle_subset (n := n) hKN)
  let y := embeddedEdgeEmbedding (horizontalStripCutRectangle K n)
      (horizontalStripCutRectangle N n) f hmap x
  have hcompat : horizontalStripRectangleOriginalEdge N n y =
      horizontalStripRectangleOriginalEdge K n x := by
    apply Subtype.ext
    rw [horizontalStripRectangleOriginalEdge_val, horizontalStripRectangleOriginalEdge_val,
      embeddedEdgeEmbedding_coe]
    change Sym2.map (fun z : RectangleVertex (-(N : ℤ), 0) (2 * N) (2 * n) => z.val)
        (Sym2.map f x.val) =
      Sym2.map (fun z : RectangleVertex (-(K : ℤ), 0) (2 * K) (2 * n) => z.val) x.val
    rw [Sym2.map_map]
    congr 1
  exact ⟨y, hcompat.trans hx⟩

private theorem asymSides_measure_toReal_eq_coe
    (μ : ProbabilityMeasure LatticeConfiguration) (s : Set LatticeConfiguration) :
    ((μ s : NNReal) : ℝ) = ((μ : Measure LatticeConfiguration) s).toReal := by
  let z : ENNReal := (μ : Measure LatticeConfiguration) s
  have htop : z ≠ (⊤ : ENNReal) := measure_ne_top _ _
  have hcoe := ENNReal.coe_toNNReal htop
  change (z.toNNReal : ℝ) = z.toReal
  calc
    (z.toNNReal : ℝ) = (z.toNNReal : ENNReal).toReal := by simp
    _ = z.toReal := congrArg ENNReal.toReal hcoe

theorem horizontalStripAsymmetricTopSides_allOpen_lower_centered
    (q : ClusterWeight) (N n : ℕ) (F : Finset squareLattice.edgeSet) :
    (measure (horizontalStripCutRectangle N n) q (horizontalStripTopWiredBoundary N n)
      (horizontalStripRectangleCylinderEvent N n F)).toReal ≤
    (measure (horizontalStripAsymmetricRectangle N n) q
      (horizontalStripAsymmetricTopSidesBoundary N n)
      (horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F)).toReal := by
  have h1 := horizontalStripAsymmetricInterval_allOpen_lower_centered q N n F
  have htopPart : (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ))
      (2 * N + 1) n).partition ≤ (horizontalStripAsymmetricTopSidesBoundary N n).partition := by
    change (BoundaryCondition.wired (horizontalStripIntervalTopWiredSet
        (-(N + 1 : ℕ)) (2 * N + 1) n)).partition ≤
      (BoundaryCondition.wired (horizontalStripAsymmetricTopSidesSet N n)).partition
    intro u v huv
    rw [BoundaryCondition.wired_rel] at huv ⊢
    rcases huv with h | ⟨hu, hv⟩
    · exact Or.inl h
    · exact Or.inr ⟨Or.inl hu, Or.inl hv⟩
  have h2 : (measure (horizontalStripAsymmetricRectangle N n) q
      (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
      (horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F)).toReal ≤
    (measure (horizontalStripAsymmetricRectangle N n) q
      (horizontalStripAsymmetricTopSidesBoundary N n)
      (horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F)).toReal :=
    PottsContinuity.FKC.FiniteFK.measure_boundary_comparison q
      (horizontalStripIntervalTopWiredBoundary (-(N + 1 : ℕ)) (2 * N + 1) n)
      (horizontalStripAsymmetricTopSidesBoundary N n) htopPart
      (horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F)
      (by
        intro A B hAB hA
        exact hA.trans (Finset.image_mono _ hAB))
  have h1R := ENNReal.toReal_mono (measure_ne_top _ _) h1
  exact h1R.trans (by simpa [horizontalStripAsymmetricRectangle] using h2)

theorem horizontalStripAsymmetricTopSides_allOpen_upper_centered
    (q : ClusterWeight) (N n : ℕ) (F : Finset squareLattice.edgeSet)
    (hFN : ∀ e ∈ F, e ∈ Set.range (horizontalStripRectangleOriginalEdge N n)) :
    (measure (horizontalStripAsymmetricRectangle N n) q
      (horizontalStripAsymmetricTopSidesBoundary N n)
      (horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F)).toReal ≤
    (measure (horizontalStripCutRectangle N n) q (horizontalStripTopSidesBoundary N n)
      (horizontalStripRectangleCylinderEvent N n F)).toReal := by
  have hpart := asymSides_frozen_partition_le_centerSides N n
  have h := embedded_marginal_probability_le_of_frozen_partition
      (horizontalStripCutRectangle N n) (horizontalStripAsymmetricRectangle N n)
      (asymSidesCenterEmbedding N n) (asymSidesCenter_map_le N n) q
      (horizontalStripAsymmetricTopSidesBoundary N n) (horizontalStripTopSidesBoundary N n)
      hpart (horizontalStripRectangleCylinderEvent N n F)
      (asymSides_centerCylinder_upper N n F)
  have heq : {A : Configuration (horizontalStripAsymmetricRectangle N n) |
      embeddedConfigurationRestriction (horizontalStripCutRectangle N n)
        (horizontalStripAsymmetricRectangle N n) (asymSidesCenterEmbedding N n)
        (asymSidesCenter_map_le N n) A ∈ horizontalStripRectangleCylinderEvent N n F} =
      horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F := by
    ext A
    exact (asymSides_restrictionCylinder_iff_of_support N n F hFN A).symm
  simpa only [heq] using h

theorem horizontalStripAsymmetricTopSidesProbabilityMeasures_allOpen_tendsto
    (q : ClusterWeight) (n : ℕ)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ))
    (F : Finset squareLattice.edgeSet) :
    Tendsto (fun N => horizontalStripAsymmetricTopSidesProbabilityMeasures q n N
      (LatticeConfiguration.allOpen F)) atTop (𝓝 (μ (LatticeConfiguration.allOpen F))) := by
  by_cases hNo : ¬ ∃ K : ℕ, ∀ e ∈ F,
      e ∈ Set.range (horizontalStripRectangleOriginalEdge K n)
  · have hμzero := horizontalStripTopWiredLimit_allOpen_eq_zero_of_no_finiteSupport
      q n F μ hμ hNo
    have hzero : ∀ N, horizontalStripAsymmetricTopSidesProbabilityMeasures q n N
        (LatticeConfiguration.allOpen F) = 0 := by
      intro N
      change ((horizontalStripAsymmetricTopSidesProbabilityMeasure q N n :
        Measure LatticeConfiguration) (LatticeConfiguration.allOpen F)).toNNReal = 0
      rw [horizontalStripAsymmetricTopSidesProbabilityMeasure_allOpen]
      have hempty := asymSides_interval_empty_of_no_center_support N n F hNo
      have hempty' : horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ))
          (2 * N + 1) n F = (∅ : Set (Configuration
            (rectangleGraph (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)))) := hempty
      change (measure (horizontalStripAsymmetricRectangle N n) q
        (horizontalStripAsymmetricTopSidesBoundary N n)
        (horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F)).toNNReal = 0
      change (measure (rectangleGraph (-(N + 1 : ℕ), 0) (2 * N + 1) (2 * n)) q
        (horizontalStripAsymmetricTopSidesBoundary N n)
        (horizontalStripIntervalCylinderEvent (-(N + 1 : ℕ)) (2 * N + 1) n F)).toNNReal = 0
      rw [hempty]
      rw [measure_empty]
      simp
    rw [hμzero]
    have heq : (fun N => horizontalStripAsymmetricTopSidesProbabilityMeasures q n N
        (LatticeConfiguration.allOpen F)) = fun _ => (0 : NNReal) := by
      funext N
      exact hzero N
    rw [heq]
    exact tendsto_const_nhds
  · obtain ⟨K, hK⟩ := not_not.mp hNo
    have hcenterLo : Tendsto
        (fun N => horizontalStripTopWiredProbabilityMeasures q n N
          (LatticeConfiguration.allOpen F)) atTop (𝓝 (μ (LatticeConfiguration.allOpen F))) :=
      LatticeConfiguration.tendsto_allOpen_of_weak hμ F
    have hcenterHi : Tendsto
        (fun N => horizontalStripCenterTopSidesProbabilityMeasures q n N
          (LatticeConfiguration.allOpen F)) atTop
          (𝓝 (μ (LatticeConfiguration.allOpen F))) :=
      LatticeConfiguration.tendsto_allOpen_of_weak
        (asymSides_centerTopSides_tendsto q n μ hμ) F
    have hcenterLoR := NNReal.tendsto_coe.mpr hcenterLo
    have hcenterHiR := NNReal.tendsto_coe.mpr hcenterHi
    have hlow : ∀ᶠ N : ℕ in atTop,
        ((horizontalStripTopWiredProbabilityMeasures q n N
          (LatticeConfiguration.allOpen F) : NNReal) : ℝ) ≤
        ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N
          (LatticeConfiguration.allOpen F) : NNReal) : ℝ) := by
      filter_upwards with N
      have h := horizontalStripAsymmetricTopSides_allOpen_lower_centered q N n F
      have hR := h
      rw [← horizontalStripRectangleProbabilityMeasure_allOpen,
        ← horizontalStripAsymmetricTopSidesProbabilityMeasure_allOpen] at hR
      rw [← asymSides_measure_toReal_eq_coe, ← asymSides_measure_toReal_eq_coe] at hR
      exact hR
    have hhigh : ∀ᶠ N : ℕ in atTop,
        ((horizontalStripAsymmetricTopSidesProbabilityMeasures q n N
          (LatticeConfiguration.allOpen F) : NNReal) : ℝ) ≤
        ((horizontalStripCenterTopSidesProbabilityMeasures q n N
          (LatticeConfiguration.allOpen F) : NNReal) : ℝ) := by
      filter_upwards [Filter.eventually_atTop.2 ⟨K, fun N hKN => hKN⟩] with N hKN
      have h := horizontalStripAsymmetricTopSides_allOpen_upper_centered q N n F
        (horizontalStripOriginalEdge_range_mono hKN F hK)
      have hR := h
      rw [← horizontalStripAsymmetricTopSidesProbabilityMeasure_allOpen,
        ← horizontalStripRectangleProbabilityMeasure_allOpen] at hR
      rw [← asymSides_measure_toReal_eq_coe, ← asymSides_measure_toReal_eq_coe] at hR
      exact hR
    have hreal := tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hcenterLoR hcenterHiR hlow hhigh
    exact NNReal.tendsto_coe.mp hreal

theorem horizontalStripAsymmetricTopSidesProbabilityMeasures_tendsto
    (q : ClusterWeight) (n : ℕ)
    (μ : ProbabilityMeasure LatticeConfiguration)
    (hμ : Tendsto (horizontalStripTopWiredProbabilityMeasures q n) atTop (𝓝 μ)) :
    Tendsto (horizontalStripAsymmetricTopSidesProbabilityMeasures q n) atTop (𝓝 μ) := by
  apply (probabilityMeasures_tendsto_iff_allOpen_coordinates
    (horizontalStripAsymmetricTopSidesProbabilityMeasures q n) μ).2
  intro F
  exact horizontalStripAsymmetricTopSidesProbabilityMeasures_allOpen_tendsto q n μ hμ F

theorem horizontalStripAsymmetricTopSidesProbabilityMeasures_tendsto_canonical
    (q : ClusterWeight) (n : ℕ) :
    Tendsto (horizontalStripAsymmetricTopSidesProbabilityMeasures q n) atTop
      (𝓝 (Classical.choose (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n))) := by
  have hμ := (Classical.choose_spec
    (horizontalStripTopWiredProbabilityMeasures_existsUnique_limit q n)).1
  exact horizontalStripAsymmetricTopSidesProbabilityMeasures_tendsto q n _ hμ

end
end PottsContinuity.FKC.Medial
