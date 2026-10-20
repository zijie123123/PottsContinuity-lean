module

public import PottsContinuity.Thm3.Push.CommonExplorationEvents
public import PottsContinuity.PD.FK.Isomorphism

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.PD.FK PottsContinuity.Exploration
noncomputable section
variable {V W : Type*} [Finite V] [Finite W]
variable {G : SimpleGraph V} {H : SimpleGraph W}
local instance isoRevealEdgeEq {Z : Type*} (K : SimpleGraph Z) :
    DecidableEq K.edgeSet := Classical.decEq _

omit [Finite V] [Finite W] in
/-- Exact preservation of original recorded edge intersections. -/
theorem configurationIso_inter (e : G ≃g H) (A B : Configuration G) :
    configurationIso e (A ∩ B) = configurationIso e A ∩ configurationIso e B := by
  classical
  exact Finset.map_inter A B

omit [Finite V] [Finite W] in
/-- Pulling back original open records commutes with intersection as well. -/
theorem configurationIso_symm_inter (e : G ≃g H) (A B : Configuration H) :
    (configurationIso e).symm (A ∩ B) =
      (configurationIso e).symm A ∩ (configurationIso e).symm B := by
  apply (configurationIso e).injective
  rw [Equiv.apply_symm_apply,configurationIso_inter,
    Equiv.apply_symm_apply,Equiv.apply_symm_apply]

/-- Relabel a concrete original-bond exploration by an actual graph
isomorphism. The inverse state transport is part of the definition. -/
def isoStoppingReveal (e : G ≃g H) (r : RevealMap (G := G)) : RevealMap (G := H) :=
  fun A => configurationIso e (r ((configurationIso e).symm A))

omit [Finite V] [Finite W] in
/-- Agreement on a transported original record is exactly the corresponding
agreement after pulling back all original sampled edge states. -/
theorem isoStoppingReveal_agreement_pullback (e : G ≃g H) (r : RevealMap (G := G))
    (A B : Configuration H)
    (hstates : B ∩ isoStoppingReveal e r A = A ∩ isoStoppingReveal e r A) :
    (configurationIso e).symm B ∩ r ((configurationIso e).symm A) =
      (configurationIso e).symm A ∩ r ((configurationIso e).symm A) := by
  apply (configurationIso e).injective
  rw [configurationIso_inter,configurationIso_inter,
    Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  exact hstates

omit [Finite V] [Finite W] in
/-- Stopping locality is preserved under actual edge relabeling. -/
theorem isoStoppingReveal_stable (e : G ≃g H) (r : RevealMap (G := G))
    (hr : ∀ A B, B ∩ r A = A ∩ r A → r B = r A)
    (A B : Configuration H)
    (hstates : B ∩ isoStoppingReveal e r A = A ∩ isoStoppingReveal e r A) :
    isoStoppingReveal e r B = isoStoppingReveal e r A :=
  congrArg (configurationIso e)
    (hr _ _ (isoStoppingReveal_agreement_pullback e r A B hstates))

omit [Finite V] [Finite W] in
/-- BOTH success and failure transport through the same actual stopping
record. There is no law or numerical crossing estimate among the premises. -/
theorem readFromReveal_isoStoppingReveal (e : G ≃g H) (r : RevealMap (G := G))
    (hr : ∀ A B, B ∩ r A = A ∩ r A → r B = r A)
    (E : Set (Configuration G)) (hE : ReadFromReveal r E) :
    ReadFromReveal (isoStoppingReveal e r)
      {A | (configurationIso e).symm A ∈ E} := by
  intro A B hB
  have hinner := isoStoppingReveal_agreement_pullback e r A B hB.2
  exact hE _ _ ⟨hr _ _ hinner,hinner⟩

end
end PottsContinuity.Push
