/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverExploration.lean`.
Adaptation: namespace/import relocation, unchanged unique-path statement on the full carrier.
-/
module

public import PottsContinuity.Thm4.FinitePorts
public import PottsContinuity.Thm4.OriginCorner
public import PottsContinuity.Thm4.PairingSingleCut
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.Thm4.Medial
open PottsContinuity.PD.FK
noncomputable section

local instance coverExplorationPortAmbientFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

/-- The actual origin corner port, retained in the finite carrier for positive box radius. -/
def parafermionicCoverFiniteOriginCornerPort (n : ℕ) (hn : 1 ≤ n) :
    ParafermionicCoverFinitePort n := by
  refine ⟨parafermionicCoverOriginCornerPort, ?_⟩
  rw [parafermionicCoverBoxVertices_mem,
    parafermionicCoverOriginCornerPort_primalVertex]
  have hnZ : 1 ≤ (n : ℤ) := by exact_mod_cast hn
  dsimp only
  omega

@[simp] theorem parafermionicCoverFiniteOriginCornerPort_val (n : ℕ)
    (hn : 1 ≤ n) :
    (parafermionicCoverFiniteOriginCornerPort n hn).1 =
      parafermionicCoverOriginCornerPort := rfl

theorem parafermionicCoverFiniteCornerPairPerm_origin (n : ℕ)
    (hn : 1 ≤ n) :
    (parafermionicCoverFiniteCornerPairPerm n
      (parafermionicCoverFiniteOriginCornerPort n hn)).1 =
        parafermionicCoverOriginCornerPortOther := by
  simp [parafermionicCoverFiniteOriginCornerPort,
    parafermionicCoverOriginCornerPortOther]

theorem parafermionicCoverFiniteCornerPairPerm_origin_ne (n : ℕ)
    (hn : 1 ≤ n) :
    parafermionicCoverFiniteOriginCornerPort n hn ≠
      parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn) := by
  intro h
  have hv := congrArg Subtype.val h
  rw [parafermionicCoverFiniteOriginCornerPort_val,
    parafermionicCoverFiniteCornerPairPerm_origin] at hv
  exact parafermionicCoverOriginCornerPorts_ne hv.symm

theorem parafermionicCoverFiniteLocalPairPerm_involutive (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    Function.Involutive (parafermionicCoverFiniteLocalPairPerm n A) := by
  intro c
  apply Subtype.ext
  exact parafermionicCoverLocalPair_involutive _ c.1

theorem parafermionicCoverFiniteCornerPairPerm_involutive (n : ℕ) :
    Function.Involutive (parafermionicCoverFiniteCornerPairPerm n) := by
  intro c
  apply Subtype.ext
  exact parafermionicCoverCornerPair_involutive c.1

/-- The finite layered pairing graph after cutting the actual corner-pair edge
incident to the retained origin port. -/
def parafermionicCoverFiniteCornerCutPairingGraph (n : ℕ) (hn : 1 ≤ n)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    SimpleGraph (ParafermionicCoverFinitePort n × Bool) :=
  pairingGraph (parafermionicCoverFiniteLocalPairPerm n A)
    (pairingSingleCutPerm (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteOriginCornerPort n hn)
      (parafermionicCoverFiniteCornerPairPerm_involutive n))
    (parafermionicCoverFiniteLocalPairPerm_involutive n A)
    (pairingSingleCut_involutive (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteOriginCornerPort n hn)
      (parafermionicCoverFiniteCornerPairPerm_involutive n))

theorem parafermionicCoverFiniteCornerCut_existsUnique_isPath (n : ℕ)
    (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n)) :
    ∃! p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
      ((parafermionicCoverFiniteOriginCornerPort n hn), true)
      ((parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn)), true),
      p.IsPath := by
  classical
  simpa [parafermionicCoverFiniteCornerCutPairingGraph] using
    (pairingGraph_singleCut_existsUnique_isPath
      (parafermionicCoverFiniteLocalPairPerm n A)
      (parafermionicCoverFiniteCornerPairPerm n)
      (parafermionicCoverFiniteLocalPairPerm_involutive n A)
      (parafermionicCoverFiniteCornerPairPerm_involutive n)
      (parafermionicCoverFiniteLocalPairPerm_no_fixed_points n A)
      (parafermionicCoverFiniteCornerPairPerm_no_fixed_points n)
      (parafermionicCoverFiniteOriginCornerPort n hn))

end
end PottsContinuity.Thm4
