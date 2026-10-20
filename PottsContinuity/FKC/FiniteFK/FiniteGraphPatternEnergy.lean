-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/FiniteGraphPatternEnergy.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.FiniteEnergy
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK
noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance finiteGraphPatternEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance finiteGraphPatternEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Finite configurations realizing a prescribed open/closed pattern on a
finite set of edges in an arbitrary finite graph. -/
def finiteConfigurationPatternEvent (F : Finset G.edgeSet)
    (σ : G.edgeSet → Bool) : Set (Configuration G) :=
  {A | ∀ e ∈ F, (e ∈ A ↔ σ e = true)}

omit [Finite V] in
private theorem finiteConfigurationPatternEvent_insert
    (F : Finset G.edgeSet) (e : G.edgeSet) (σ : G.edgeSet → Bool) :
    finiteConfigurationPatternEvent (insert e F) σ =
      {A | (e ∈ A ↔ σ e = true)} ∩ finiteConfigurationPatternEvent F σ := by
  ext A
  simp [finiteConfigurationPatternEvent]

def finitePatternEdgeFirst (e : G.edgeSet) : V := e.1.out.1
def finitePatternEdgeSecond (e : G.edgeSet) : V := e.1.out.2

omit [Finite V] in
private theorem finitePatternEdgeFirst_adj_second (e : G.edgeSet) :
    G.Adj (finitePatternEdgeFirst e) (finitePatternEdgeSecond e) := by
  have heq : s(finitePatternEdgeFirst e, finitePatternEdgeSecond e) = e.1 := Quot.out_eq _
  exact G.mem_edgeSet.mp (heq ▸ e.2)

omit [Finite V] in
private theorem finitePatternCanonicalEdge_eq (e : G.edgeSet) :
    (⟨s(finitePatternEdgeFirst e, finitePatternEdgeSecond e),
      G.mem_edgeSet.mpr (finitePatternEdgeFirst_adj_second e)⟩ : G.edgeSet) = e := by
  apply Subtype.ext
  exact Quot.out_eq e.1

omit [Finite V] in
private theorem finiteConfigurationPatternEvent_stable_erase
    (F : Finset G.edgeSet) (e : G.edgeSet) (he : e ∉ F)
    (σ : G.edgeSet → Bool) :
    ∀ A, A ∈ finiteConfigurationPatternEvent F σ ↔
      A.erase e ∈ finiteConfigurationPatternEvent F σ := by
  intro A
  simp only [finiteConfigurationPatternEvent, Set.mem_ofPred_eq]
  constructor
  · intro h f hf
    have hne : f ≠ e := by
      intro hEq
      subst f
      exact he hf
    have hmem : f ∈ A.erase e ↔ f ∈ A := by simp [hne]
    rw [hmem]
    exact h f hf
  · intro h f hf
    have hne : f ≠ e := by
      intro hEq
      subst f
      exact he hf
    have hmem : f ∈ A.erase e ↔ f ∈ A := by simp [hne]
    rw [← hmem]
    exact h f hf

/-- Exact finite-pattern finite-energy estimate for the genuine FK law on any
finite graph and boundary condition. The base event is invariant under erasing
each queried edge. -/
theorem configurationProbability_finite_pattern_finite_energy
    (q : ClusterWeight) (ξ : BoundaryCondition V) (S : Set (Configuration G))
    (F : Finset G.edgeSet) (σ : G.edgeSet → Bool)
    (hstable : ∀ e ∈ F, ∀ A, A ∈ S ↔ A.erase e ∈ S) :
    (1 / (1 + loopWeight q)) ^ F.card * (measure G q ξ S).toReal ≤
        (measure G q ξ (S ∩ finiteConfigurationPatternEvent F σ)).toReal ∧
      (measure G q ξ (S ∩ finiteConfigurationPatternEvent F σ)).toReal ≤
        edgeParameter q ^ F.card * (measure G q ξ S).toReal := by
  classical
  revert hstable
  induction F using Finset.induction_on with
  | empty =>
      intro hstable
      simp [finiteConfigurationPatternEvent]
  | @insert e F he ih =>
      intro hstable
      have hstable_e : ∀ A, A ∈ S ↔ A.erase e ∈ S :=
        hstable e (Finset.mem_insert_self e F)
      have hstable_F : ∀ f ∈ F, ∀ A, A ∈ S ↔ A.erase f ∈ S := by
        intro f hf
        exact hstable f (Finset.mem_insert_of_mem hf)
      let S' := S ∩ finiteConfigurationPatternEvent F σ
      have hstableS' : ∀ A, A ∈ S' ↔ A.erase e ∈ S' := by
        intro A
        change (A ∈ S ∧ A ∈ finiteConfigurationPatternEvent F σ) ↔
          (A.erase e ∈ S ∧ A.erase e ∈ finiteConfigurationPatternEvent F σ)
        rw [hstable_e A, finiteConfigurationPatternEvent_stable_erase F e he σ A]
      have hOneOpen := configurationProbability_edge_finite_energy q ξ S'
        (finitePatternEdgeFirst_adj_second e) (by
          intro A
          have h := hstableS' A
          simpa [finitePatternCanonicalEdge_eq e] using h)
      have hOneClosed := configurationProbability_edge_finite_energy_closed q ξ S'
        (finitePatternEdgeFirst_adj_second e) (by
          intro A
          have h := hstableS' A
          simpa [finitePatternCanonicalEdge_eq e] using h)
      have hOnePattern :
          (1 / (1 + loopWeight q)) * (measure G q ξ S').toReal ≤
              (measure G q ξ (S' ∩ {A | (e ∈ A ↔ σ e = true)})).toReal ∧
            (measure G q ξ (S' ∩ {A | (e ∈ A ↔ σ e = true)})).toReal ≤
              edgeParameter q * (measure G q ξ S').toReal := by
        cases hσ : σ e with
        | true =>
            simpa [hσ, finitePatternCanonicalEdge_eq] using hOneOpen
        | false =>
            simpa [hσ, finitePatternCanonicalEdge_eq] using hOneClosed
      have hmain := ih (by
        intro f hf A
        exact hstable f (Finset.mem_insert_of_mem hf) A)
      have hpatternEq :
          S' ∩ {A | (e ∈ A ↔ σ e = true)} =
            S ∩ finiteConfigurationPatternEvent (insert e F) σ := by
        dsimp [S']
        rw [finiteConfigurationPatternEvent_insert]
        ext A
        simp [and_left_comm, and_comm]
      rw [← hpatternEq]
      constructor
      · calc
          (1 / (1 + loopWeight q)) ^ (insert e F).card *
              (measure G q ξ S).toReal =
              (1 / (1 + loopWeight q)) *
                ((1 / (1 + loopWeight q)) ^ F.card *
                  (measure G q ξ S).toReal) := by
                    rw [Finset.card_insert_of_notMem he, pow_succ]
                    ring
          _ ≤ (1 / (1 + loopWeight q)) * (measure G q ξ S').toReal :=
            mul_le_mul_of_nonneg_left hmain.1
              ((one_add_loopWeight_pos q).le |> div_nonneg (by norm_num))
          _ ≤ (measure G q ξ (S' ∩ {A | (e ∈ A ↔ σ e = true)})).toReal := hOnePattern.1
      · calc
          (measure G q ξ (S' ∩ {A | (e ∈ A ↔ σ e = true)})).toReal ≤
              edgeParameter q * (measure G q ξ S').toReal := hOnePattern.2
          _ ≤ edgeParameter q *
              (edgeParameter q ^ F.card * (measure G q ξ S).toReal) :=
            mul_le_mul_of_nonneg_left hmain.2 (edgeParameter_pos q).le
          _ = edgeParameter q ^ (insert e F).card * (measure G q ξ S).toReal := by
                rw [Finset.card_insert_of_notMem he, pow_succ]
                ring

end
end PottsContinuity.FKC.FiniteFK
