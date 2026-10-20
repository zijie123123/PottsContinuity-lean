-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredGhostConnection.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.WiredVertexCollapse
public import PottsContinuity.FKC.FiniteFK.WiredVertexQuotient
public import PottsContinuity.FKC.FiniteFK.WiredArcComponent

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Actual connection to the ghost vertex is exactly an open cluster hitting
the collapsed wired set. -/
theorem wiredGhost_actualConnected_iff_exists
    (S : Set V) (hne : S.Nonempty) (G : SimpleGraph V)
    (hno : ∀ ⦃x y⦄, G.Adj x y → ¬ (x ∈ S ∧ y ∈ S))
    (hunique : ∀ ⦃x s t⦄, x ∉ S → s ∈ S → t ∈ S →
      G.Adj s x → G.Adj t x → s = t)
    (A : Configuration G) (u : V) :
    ActualConnected (wiredVertexGraph S hne G hno)
        (A.map (wiredVertexEdgeEquiv S hne G hno hunique).toEmbedding)
        (wiredVertexMap S hne u) none ↔
      ∃ w ∈ S, ActualConnected G A u w := by
  classical
  let s : V := Classical.choose hne
  have hs : s ∈ S := Classical.choose_spec hne
  have hmap : wiredVertexMap S hne s = none := by
    simp [wiredVertexMap, hs]
  have hquot := wiredVertexQuotient_componentSetoid_rel_iff
    (wiredVertexMap S hne) (wiredVertexMap_surjective S hne)
    (wiredVertexEdgeEquiv S hne G hno hunique)
    (wiredVertexEdgeEquiv_val S hne G hno hunique)
    (BoundaryCondition.wired S) (wired_boundary_partition_eq_ker S hne) A u s
  have harc : (componentSetoid G (BoundaryCondition.wired S) A).r u s ↔
      ∃ w ∈ S, ActualConnected G A u w :=
    wired_componentSetoid_rel_iff_exists_actualConnected G A S
      (u := u) (v := s) hs
  calc
    ActualConnected (wiredVertexGraph S hne G hno)
        (A.map (wiredVertexEdgeEquiv S hne G hno hunique).toEmbedding)
        (wiredVertexMap S hne u) none
      ↔ ActualConnected (wiredVertexGraph S hne G hno)
          (A.map (wiredVertexEdgeEquiv S hne G hno hunique).toEmbedding)
          (wiredVertexMap S hne u) (wiredVertexMap S hne s) := by rw [hmap]
    _ ↔ (componentSetoid G (BoundaryCondition.wired S) A).r u s := hquot.symm
    _ ↔ ∃ w ∈ S, ActualConnected G A u w := harc

omit [DecidableEq V] in
/-- The preimage of the ghost-connection event under configuration transport is
exactly the original wired-set-hitting event. -/
theorem wiredGhost_connection_preimage
    (S : Set V) (hne : S.Nonempty) (G : SimpleGraph V)
    (hno : ∀ ⦃x y⦄, G.Adj x y → ¬ (x ∈ S ∧ y ∈ S))
    (hunique : ∀ ⦃x s t⦄, x ∉ S → s ∈ S → t ∈ S →
      G.Adj s x → G.Adj t x → s = t)
    (u : V) :
    (fun A : Configuration G =>
      A.map (wiredVertexEdgeEquiv S hne G hno hunique).toEmbedding) ⁻¹'
        {B | ActualConnected (wiredVertexGraph S hne G hno) B
          (wiredVertexMap S hne u) none} =
      {A | ∃ w ∈ S, ActualConnected G A u w} := by
  ext A
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  exact wiredGhost_actualConnected_iff_exists S hne G hno hunique A u

end
end PottsContinuity.FKC.FiniteFK
