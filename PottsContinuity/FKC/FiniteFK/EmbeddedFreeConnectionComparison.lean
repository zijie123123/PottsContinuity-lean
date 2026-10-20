-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/EmbeddedFreeConnectionComparison.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SubgraphComparison
public import PottsContinuity.FKC.FiniteFK.IncreasingEvents
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open MeasureTheory
open scoped BigOperators
noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  {G : SimpleGraph V} {H : SimpleGraph W}
  (f : V ↪ W) (hGH : G.map f ≤ H)

local instance embeddedConnectionInnerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance embeddedConnectionOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance embeddedConnectionInnerEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _
local instance embeddedConnectionOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

omit [Finite V] [Finite W] in
private theorem embeddedRestriction_actualConnected_mono
    (A : Configuration H) {x y : V}
    (hconn : ActualConnected G
      (embeddedConfigurationRestriction G H f hGH A) x y) :
    ActualConnected H A (f x) (f y) := by
  let C : Configuration G := embeddedConfigurationRestriction G H f hGH A
  let I : Configuration H := embeddedConfigurationEmbedding G H f hGH C
  have hsub : I ⊆ A := embeddedConfigurationEmbedding_restriction_subset G H f hGH A
  let hhom : openGraph G C →g openGraph H A := {
    toFun := f
    map_rel' := by
      intro a b hab
      rcases (openGraph_adj G C a b).mp hab with ⟨e, he, heval⟩
      have hGadj : G.Adj a b := G.mem_edgeSet.mp (heval ▸ e.property)
      have hmapAdj : (G.map f).Adj (f a) (f b) :=
        (SimpleGraph.map_adj f G (f a) (f b)).mpr ⟨a, b, hGadj, rfl, rfl⟩
      have hHadj : H.Adj (f a) (f b) := hGH hmapAdj
      let eH : H.edgeSet := ⟨s(f a, f b), H.mem_edgeSet.mpr hHadj⟩
      have heI : embeddedEdgeEmbedding G H f hGH e ∈ I := by
        change embeddedEdgeEmbedding G H f hGH e ∈
          embeddedConfigurationEmbedding G H f hGH C
        rw [embeddedConfigurationEmbedding_eq_map]
        exact Finset.mem_map.mpr ⟨e, he, rfl⟩
      have heA : embeddedEdgeEmbedding G H f hGH e ∈ A := hsub heI
      rw [openGraph_adj]
      refine ⟨eH, ?_, ?_⟩
      · have hevalMap : (embeddedEdgeEmbedding G H f hGH e).val = s(f a, f b) := by
          rw [embeddedEdgeEmbedding_coe, heval]
          simp
        have heq : embeddedEdgeEmbedding G H f hGH e = eH := Subtype.ext hevalMap
        simpa [heq] using heA
      · rfl
  }
  change (openGraph G C).Reachable x y at hconn
  change (openGraph H A).Reachable (f x) (f y)
  have hhom_val (z : V) : hhom z = f z := by
    change f z = f z
    rfl
  have hmapped := SimpleGraph.Reachable.map hhom hconn
  rw [hhom_val, hhom_val] at hmapped
  exact hmapped

private theorem fkLaw_measure_toReal_eq_expectation
    {X : Type*} [Finite X] {K : SimpleGraph X}
    (q : ClusterWeight) (ξ : BoundaryCondition X)
    (S : Set (Configuration K)) :
    (measure K q ξ S).toReal =
      FiniteProbability.expectation (law K q ξ)
        (S.indicator (fun _ => (1 : ℝ))) := by
  let : Fintype K.edgeSet := Fintype.ofFinite _
  let : DecidableEq K.edgeSet := Classical.decEq _
  rw [measure_toReal_eq_indicator_sum]
  unfold FiniteProbability.expectation
  apply Finset.sum_congr rfl
  intro A hA
  by_cases h : A ∈ S
  · simp [Set.indicator, h, law_apply,
      ENNReal.toReal_ofReal (configurationProbability_pos K q ξ A).le]
  · simp [Set.indicator, h]

/-- For an actual graph embedding, the finite free FK connection probability
between embedded vertices is monotone under graph inclusion. The proof compares
the full smaller and larger laws and transports the same open path under the
configuration restriction. -/
theorem embedded_free_connection_probability_le
    (hGH : G.map f ≤ H) (q : ClusterWeight) (x y : V) :
    (measure G q (BoundaryCondition.free (∅ : Set V))
      (connectivityEvent G x y)).toReal ≤
    (measure H q (BoundaryCondition.free (∅ : Set W))
      (connectivityEvent H (f x) (f y))).toReal := by
  classical
  let S : Set (Configuration G) := connectivityEvent G x y
  let F : Configuration G → ℝ := S.indicator (fun _ => (1 : ℝ))
  let T : Set (Configuration H) := connectivityEvent H (f x) (f y)
  have hF0 : ∀ A, 0 ≤ F A := by
    intro A
    change 0 ≤ S.indicator (fun _ => (1 : ℝ)) A
    by_cases h : A ∈ S <;> simp [Set.indicator, h]
  have hF : Monotone F := by
    intro A B hAB
    change S.indicator (fun _ => (1 : ℝ)) A ≤
      S.indicator (fun _ => (1 : ℝ)) B
    by_cases hA : A ∈ S
    · have hB : B ∈ S := by
        exact actualConnected_mono hAB hA
      simp [Set.indicator, hA, hB]
    · simp only [Set.indicator_of_notMem hA]
      by_cases hB : B ∈ S <;> simp [Set.indicator, hB]
  have hcmp := embedded_free_expectation_le G H f hGH q
    (∅ : Set V) (∅ : Set W) F hF0 hF
  have hpoint : ∀ A : Configuration H, F
      (embeddedConfigurationRestriction G H f hGH A) ≤
        T.indicator (fun _ => (1 : ℝ)) A := by
    intro A
    change S.indicator (fun _ => (1 : ℝ))
        (embeddedConfigurationRestriction G H f hGH A) ≤
      T.indicator (fun _ => (1 : ℝ)) A
    by_cases h : embeddedConfigurationRestriction G H f hGH A ∈ S
    · have hT : A ∈ T := by
        exact embeddedRestriction_actualConnected_mono f hGH A h
      simp [Set.indicator, h, hT]
    · simp only [Set.indicator_of_notMem h]
      by_cases hT : A ∈ T <;> simp [Set.indicator, hT]
  have hreal :
      FiniteProbability.expectation (law G q (BoundaryCondition.free (∅ : Set V))) F ≤
        FiniteProbability.expectation (law H q (BoundaryCondition.free (∅ : Set W)))
          (T.indicator (fun _ => (1 : ℝ))) :=
    hcmp.trans (FiniteProbability.expectation_mono _ _ _ hpoint)
  have hleft := fkLaw_measure_toReal_eq_expectation (q := q)
    (ξ := BoundaryCondition.free (∅ : Set V)) S
  have hright := fkLaw_measure_toReal_eq_expectation (q := q)
    (ξ := BoundaryCondition.free (∅ : Set W)) T
  calc
    (measure G q (BoundaryCondition.free (∅ : Set V))
        (connectivityEvent G x y)).toReal =
      FiniteProbability.expectation (law G q (BoundaryCondition.free (∅ : Set V))) F := by
        simpa [S, F] using hleft
    _ ≤ FiniteProbability.expectation
        (law H q (BoundaryCondition.free (∅ : Set W)))
        (T.indicator (fun _ => (1 : ℝ))) := hreal
    _ = (measure H q (BoundaryCondition.free (∅ : Set W))
        (connectivityEvent H (f x) (f y))).toReal := by
          simpa [T] using hright.symm

end
end PottsContinuity.FKC.FiniteFK
