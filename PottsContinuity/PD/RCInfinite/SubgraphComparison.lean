-- Adapted from the development version of the author's PottsDiscontinuity formalization (see
-- `related_formalizations` in formalization.yaml), file `PottsDiscontinuity/RCInfinite/SubgraphComparison.lean`, which
-- the public repository https://github.com/zijie123123/PottsDiscontinuity-lean does not contain; module
-- and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.PD.FK.EmbeddedClosedInteriorOuterComparison
public import PottsContinuity.PD.FK.FrozenLimitBridge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

open MeasureTheory Set

namespace PottsContinuity.PD.RCInfinite
open FK
open FK.FiniteProbability
noncomputable section
open scoped Classical

/-- The induced lattice graph on a finite vertex set. -/
abbrev finiteLatticeGraph (S : Finset LatticeVertex) :=
  squareLattice.induce (S : Set LatticeVertex)

local instance finiteSubgraphEdgeFintype (S : Finset LatticeVertex) :
    Fintype (finiteLatticeGraph S).edgeSet := Fintype.ofFinite _
local instance finiteSubgraphEdgeDecidableEq (S : Finset LatticeVertex) :
    DecidableEq (finiteLatticeGraph S).edgeSet := Classical.decEq _

/-- Inclusion of two finite induced lattice vertex carriers. -/
def finiteLatticeVertexEmbedding {S T : Finset LatticeVertex} (hST : S ⊆ T) :
    (S : Set LatticeVertex) ↪ (T : Set LatticeVertex) where
  toFun x := ⟨x.val, hST x.property⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : (T : Set LatticeVertex) => z.val) h

theorem finiteLatticeGraph_map_le {S T : Finset LatticeVertex} (hST : S ⊆ T) :
    (finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hST) ≤ finiteLatticeGraph T := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨a, b, hab, rfl, rfl⟩
  exact hab

/-- The finite configurations for which every edge in `F` is open. -/
def finiteSubgraphOpenEvent (S : Finset LatticeVertex)
    (F : Finset squareLattice.edgeSet) : Set (Configuration (finiteLatticeGraph S)) :=
  {A | F ⊆ A.map (frozenEdgeEmbedding S)}

private theorem finiteSubgraphOpenEvent_upper (S : Finset LatticeVertex)
    (F : Finset squareLattice.edgeSet) : IsUpperSet (finiteSubgraphOpenEvent S F) := by
  intro A B hAB hA
  exact hA.trans (Finset.map_subset_map.mpr hAB)

private theorem finiteEvent_indicator_nonneg {V : Type*} {G : SimpleGraph V}
    (A : Set (Configuration G)) :
    ∀ C, 0 ≤ A.indicator (fun _ => (1 : ℝ)) C := by
  intro C
  by_cases h : C ∈ A <;> simp [Set.indicator, h]

private theorem finiteEvent_indicator_monotone {V : Type*} {G : SimpleGraph V}
    (A : Set (Configuration G)) (hA : IsUpperSet A) :
    Monotone (A.indicator (fun _ => (1 : ℝ))) := by
  intro B C hBC
  by_cases hB : B ∈ A
  · have hC := hA hBC hB
    simp [Set.indicator, hB, hC]
  · simp only [Set.indicator_of_notMem hB]
    exact finiteEvent_indicator_nonneg A C

private theorem frozenEdgeEmbedding_compatible {S T : Finset LatticeVertex}
    (hST : S ⊆ T) (hGH : (finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hST) ≤
      finiteLatticeGraph T) (e : (finiteLatticeGraph S).edgeSet) :
    frozenEdgeEmbedding T
        (embeddedEdgeEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T)
          (finiteLatticeVertexEmbedding hST) hGH e) = frozenEdgeEmbedding S e := by
  apply Subtype.ext
  change Sym2.map (fun v : (T : Set LatticeVertex) => v.val)
      (Sym2.map (finiteLatticeVertexEmbedding hST) e.val) =
    Sym2.map (fun v : (S : Set LatticeVertex) => v.val) e.val
  rw [Sym2.map_map]
  congr 1

/-- Every lattice edge already represented in a smaller induced domain remains
represented in each larger induced domain. -/
theorem frozenEdgeEmbedding_range_mono {S T : Finset LatticeVertex}
    (hST : S ⊆ T) {e : squareLattice.edgeSet}
    (he : e ∈ Set.range (frozenEdgeEmbedding S)) :
    e ∈ Set.range (frozenEdgeEmbedding T) := by
  obtain ⟨x, rfl⟩ := Set.mem_range.mp he
  refine Set.mem_range.mpr ⟨embeddedEdgeEmbedding (finiteLatticeGraph S)
    (finiteLatticeGraph T) (finiteLatticeVertexEmbedding hST)
    (finiteLatticeGraph_map_le hST) x, ?_⟩
  exact frozenEdgeEmbedding_compatible hST (finiteLatticeGraph_map_le hST) x

private theorem finiteSubgraphOpenEvent_restrict_iff {S T : Finset LatticeVertex}
    (hST : S ⊆ T) (hGH : (finiteLatticeGraph S).map (finiteLatticeVertexEmbedding hST) ≤
      finiteLatticeGraph T) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding S))
    (A : Configuration (finiteLatticeGraph T)) :
    A ∈ finiteSubgraphOpenEvent T F ↔
      embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
        (finiteLatticeVertexEmbedding hST) hGH A ∈ finiteSubgraphOpenEvent S F := by
  constructor
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    have heOpen : e ∈ A.map (frozenEdgeEmbedding T) := hA he
    obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp heOpen
    have hcompat := frozenEdgeEmbedding_compatible hST hGH x
    have hyx : embeddedEdgeEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T)
        (finiteLatticeVertexEmbedding hST) hGH x = y := by
      apply (frozenEdgeEmbedding T).injective
      calc
        frozenEdgeEmbedding T
            (embeddedEdgeEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T)
              (finiteLatticeVertexEmbedding hST) hGH x) = frozenEdgeEmbedding S x := hcompat
        _ = e := hx
        _ = frozenEdgeEmbedding T y := hye.symm
    apply Finset.mem_map.mpr
    refine ⟨x, ?_, hx⟩
    exact (mem_embeddedConfigurationRestriction _ _ _ _ A x).mpr (hyx ▸ hy)
  · intro hA e he
    obtain ⟨x, hx⟩ := Set.mem_range.mp (hF e he)
    have heOpen := hA he
    obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp heOpen
    have hyx : y = x := (frozenEdgeEmbedding S).injective (hye.trans hx.symm)
    have hrestrict : x ∈ embeddedConfigurationRestriction (finiteLatticeGraph S)
        (finiteLatticeGraph T) (finiteLatticeVertexEmbedding hST) hGH A := by
      rw [← hyx]
      exact hy
    have hlarge := (mem_embeddedConfigurationRestriction _ _ _ _ A x).mp hrestrict
    apply Finset.mem_map.mpr
    exact ⟨embeddedEdgeEmbedding (finiteLatticeGraph S) (finiteLatticeGraph T)
      (finiteLatticeVertexEmbedding hST) hGH x, hlarge,
      (frozenEdgeEmbedding_compatible hST hGH x).trans hx⟩

private theorem finiteSubgraph_interior_closed {S T : Finset LatticeVertex}
    (hST : S ⊆ T) {x : S} (hx : x ∉ frozenVertexBoundary S)
    {y : T} (hxy : (finiteLatticeGraph T).Adj
      (finiteLatticeVertexEmbedding hST x) y) :
    ∃ z : S, finiteLatticeVertexEmbedding hST z = y ∧
      (finiteLatticeGraph S).Adj x z := by
  have hxnot : x.val ∉ vertexBoundary S := by
    simpa [frozenVertexBoundary] using hx
  have hadj : squareLattice.Adj x.val y.val := hxy
  have hyS : y.val ∈ S := by
    by_contra hyS
    exact hxnot ⟨x.property, y.val, hadj, hyS⟩
  refine ⟨⟨y.val, hyS⟩, ?_, hxy⟩
  apply Subtype.ext
  rfl

private theorem finiteSubgraph_interior_avoids_outerBoundary {S T : Finset LatticeVertex}
    (hST : S ⊆ T) {x : S} (hx : x ∉ frozenVertexBoundary S) :
    finiteLatticeVertexEmbedding hST x ∉ frozenVertexBoundary T := by
  have hxnot : x.val ∉ vertexBoundary S := by
    simpa [frozenVertexBoundary] using hx
  intro houter
  have hout : x.val ∈ vertexBoundary T := by
    simpa [finiteLatticeVertexEmbedding, frozenVertexBoundary] using houter
  rcases hout with ⟨_, y, hxy, hyT⟩
  have hyS : y ∈ S := by
    by_contra hyS
    exact hxnot ⟨x.property, y, hxy, hyS⟩
  exact hyT (hST hyS)

/-- Increasing all-open cylinder probabilities are monotone over nested finite
induced free domains, on cylinders supported by the smaller domain. -/
theorem finiteSubgraph_free_open_mono {S T : Finset LatticeVertex}
    (θ : Parameters) (hST : S ⊆ T) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding S)) :
    (measure (finiteLatticeGraph S) θ (BoundaryCondition.free (frozenVertexBoundary S))
      (finiteSubgraphOpenEvent S F)).toReal ≤
    (measure (finiteLatticeGraph T) θ (BoundaryCondition.free (frozenVertexBoundary T))
      (finiteSubgraphOpenEvent T F)).toReal := by
  let f := finiteLatticeVertexEmbedding hST
  let hGH := finiteLatticeGraph_map_le hST
  let A := finiteSubgraphOpenEvent S F
  have hcmp := embedded_free_expectation_le (finiteLatticeGraph S) (finiteLatticeGraph T)
    f hGH θ (frozenVertexBoundary S) (frozenVertexBoundary T)
    (A.indicator (fun _ => (1 : ℝ)))
    (finiteEvent_indicator_nonneg A)
    (finiteEvent_indicator_monotone A (finiteSubgraphOpenEvent_upper S F))
  have hleft : (measure (finiteLatticeGraph S) θ
      (BoundaryCondition.free (frozenVertexBoundary S)) A).toReal =
      expectation (law (finiteLatticeGraph S) θ
        (BoundaryCondition.free (frozenVertexBoundary S)))
        (A.indicator (fun _ => (1 : ℝ))) := by
    rw [measure_toReal_eq_indicator_sum]
    unfold expectation
    apply Finset.sum_congr rfl
    intro C hC
    have hp := configurationProbability_pos (finiteLatticeGraph S) θ
      (BoundaryCondition.free (frozenVertexBoundary S)) C
    simp only [law_apply, ENNReal.toReal_ofReal hp.le]
  have hright : (measure (finiteLatticeGraph T) θ
      (BoundaryCondition.free (frozenVertexBoundary T))
        (finiteSubgraphOpenEvent T F)).toReal =
      expectation (law (finiteLatticeGraph T) θ
        (BoundaryCondition.free (frozenVertexBoundary T)))
        ((finiteSubgraphOpenEvent T F).indicator (fun _ => (1 : ℝ))) := by
    rw [measure_toReal_eq_indicator_sum]
    unfold expectation
    apply Finset.sum_congr rfl
    intro C hC
    have hp := configurationProbability_pos (finiteLatticeGraph T) θ
      (BoundaryCondition.free (frozenVertexBoundary T)) C
    simp only [law_apply, ENNReal.toReal_ofReal hp.le]
  have hlarge : expectation (law (finiteLatticeGraph T) θ
      (BoundaryCondition.free (frozenVertexBoundary T)))
      (fun A => (finiteSubgraphOpenEvent S F).indicator (fun _ => (1 : ℝ))
        (embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
          f hGH A)) =
      expectation (law (finiteLatticeGraph T) θ
        (BoundaryCondition.free (frozenVertexBoundary T)))
        ((finiteSubgraphOpenEvent T F).indicator (fun _ => (1 : ℝ))) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro C hC
    change ((law (finiteLatticeGraph T) θ (BoundaryCondition.free
      (frozenVertexBoundary T))) C).toReal *
        (finiteSubgraphOpenEvent S F).indicator (fun _ => (1 : ℝ))
          (embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
            f hGH C) =
      ((law (finiteLatticeGraph T) θ (BoundaryCondition.free
        (frozenVertexBoundary T))) C).toReal *
          (finiteSubgraphOpenEvent T F).indicator (fun _ => (1 : ℝ)) C
    have heq := finiteSubgraphOpenEvent_restrict_iff hST hGH F hF C
    have hpoint :
        (finiteSubgraphOpenEvent S F).indicator (fun _ => (1 : ℝ))
          (embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
            f hGH C) =
        (finiteSubgraphOpenEvent T F).indicator (fun _ => (1 : ℝ)) C := by
      by_cases h : C ∈ finiteSubgraphOpenEvent T F
      · have hr := heq.mp h
        change (if embeddedConfigurationRestriction (finiteLatticeGraph S)
            (finiteLatticeGraph T) f hGH C ∈ finiteSubgraphOpenEvent S F
          then (1 : ℝ) else 0) = (if C ∈ finiteSubgraphOpenEvent T F then 1 else 0)
        rw [ite_eq_left hr, ite_eq_left h]
      · have hr : embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
            f hGH C ∉ finiteSubgraphOpenEvent S F := by
          intro hr
          exact h (heq.mpr hr)
        change (if embeddedConfigurationRestriction (finiteLatticeGraph S)
            (finiteLatticeGraph T) f hGH C ∈ finiteSubgraphOpenEvent S F
          then (1 : ℝ) else 0) = (if C ∈ finiteSubgraphOpenEvent T F then 1 else 0)
        rw [ite_eq_right hr, ite_eq_right h]
    rw [hpoint]
  have hreal : (measure (finiteLatticeGraph S) θ
      (BoundaryCondition.free (frozenVertexBoundary S)) A).toReal ≤
      (measure (finiteLatticeGraph T) θ (BoundaryCondition.free (frozenVertexBoundary T))
        (finiteSubgraphOpenEvent T F)).toReal := by
    calc
      _ = expectation (law (finiteLatticeGraph S) θ
          (BoundaryCondition.free (frozenVertexBoundary S)))
          (A.indicator (fun _ => (1 : ℝ))) := hleft
      _ ≤ expectation (law (finiteLatticeGraph T) θ
          (BoundaryCondition.free (frozenVertexBoundary T)))
          (fun C => A.indicator (fun _ => (1 : ℝ))
            (embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
              f hGH C)) := hcmp
      _ = expectation (law (finiteLatticeGraph T) θ
          (BoundaryCondition.free (frozenVertexBoundary T)))
          ((finiteSubgraphOpenEvent T F).indicator (fun _ => (1 : ℝ))) := hlarge
      _ = _ := hright.symm
  simpa only [A] using hreal

/-- Increasing all-open cylinder probabilities are decreasing over nested
finite induced wired domains, on cylinders supported by the smaller domain. -/
theorem finiteSubgraph_wired_open_antitone {S T : Finset LatticeVertex}
    (θ : Parameters) (hST : S ⊆ T) (F : Finset squareLattice.edgeSet)
    (hF : ∀ e ∈ F, e ∈ Set.range (frozenEdgeEmbedding S)) :
    (measure (finiteLatticeGraph T) θ (BoundaryCondition.wired (frozenVertexBoundary T))
      (finiteSubgraphOpenEvent T F)).toReal ≤
    (measure (finiteLatticeGraph S) θ (BoundaryCondition.wired (frozenVertexBoundary S))
      (finiteSubgraphOpenEvent S F)).toReal := by
  let f := finiteLatticeVertexEmbedding hST
  let hGH := finiteLatticeGraph_map_le hST
  let A := finiteSubgraphOpenEvent S F
  have hcmp := embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    f hGH θ (BoundaryCondition.wired (frozenVertexBoundary T)) (frozenVertexBoundary S)
    (fun {x} hx {y} hxy => finiteSubgraph_interior_closed hST hx hxy)
    (fun {x} hx => finiteSubgraph_interior_avoids_outerBoundary hST hx)
    A (finiteSubgraphOpenEvent_upper S F)
  have hsub : finiteSubgraphOpenEvent T F ⊆
      {C | embeddedConfigurationRestriction (finiteLatticeGraph S) (finiteLatticeGraph T)
        f hGH C ∈ A} := by
    intro C hC
    exact (finiteSubgraphOpenEvent_restrict_iff hST hGH F hF C).mp hC
  have hreal : (measure (finiteLatticeGraph T) θ
      (BoundaryCondition.wired (frozenVertexBoundary T))
      (finiteSubgraphOpenEvent T F)).toReal ≤
      (measure (finiteLatticeGraph S) θ (BoundaryCondition.wired (frozenVertexBoundary S)) A).toReal := by
    exact (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono hsub)).trans hcmp
  simpa only [A] using hreal

end
end PottsContinuity.PD.RCInfinite
