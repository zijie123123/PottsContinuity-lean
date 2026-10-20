/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/ParafermionicCoverFinitePorts.lean`.
Adaptation: namespace/import relocation, exact cover graph and PD configurations.
-/
module

public import PottsContinuity.Thm4.CoverPorts
public import PottsContinuity.Thm4.PortCoordinates
public import PottsContinuity.Thm4.CoverConfiguration
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.Thm4

open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section

local instance coverFinitePortAmbientFintype (n : ℕ) :
    Fintype (ParafermionicAmbientVertex n) := Fintype.ofFinite _

/-- All actual lifted medial ports whose primal endpoint is a vertex of the
finite cover box. Boundary half-ports are retained. -/
abbrev ParafermionicCoverFinitePort (n : ℕ) :=
  {c : ParafermionicCoverPort //
    parafermionicCoverPortVertex c ∈ parafermionicCoverBoxVertices n}

def parafermionicCoverFinitePortCoordinatesEmbedding (n : ℕ) :
    ParafermionicCoverFinitePort n ↪
      ParafermionicAmbientVertex n × (LatticeAxis × (Bool × Bool)) where
  toFun c :=
    (⟨parafermionicCoverPortVertex c.1, c.2⟩,
      (c.1.1.bond.axis, (c.1.1.tip, c.1.1.side)))
  inj' := by
    intro c d h
    apply Subtype.ext
    have hvert := congrArg Prod.fst h
    have hflags := congrArg Prod.snd h
    have hbase : c.1.1.primalVertex = d.1.1.primalVertex :=
      congrArg (fun z : ParafermionicAmbientVertex n => z.1.1) hvert
    have hsheet : c.1.2 = d.1.2 :=
      congrArg (fun z : ParafermionicAmbientVertex n => z.1.2) hvert
    have hport : c.1.1 = d.1.1 := by
      apply latticePortPrimalVertexCoordinatesEquiv.injective
      exact Prod.ext hbase hflags
    exact Prod.ext hport hsheet

noncomputable instance parafermionicCoverFinitePortFintype (n : ℕ) :
    Fintype (ParafermionicCoverFinitePort n) :=
  Fintype.ofInjective (parafermionicCoverFinitePortCoordinatesEmbedding n)
    (parafermionicCoverFinitePortCoordinatesEmbedding n).injective

theorem parafermionicCoverLocalPair_preservesFinitePort
    (n : ℕ) (A : Configuration (ParafermionicAmbientGraph n))
    (c : ParafermionicCoverFinitePort n) :
    parafermionicCoverPortVertex
      (parafermionicCoverLocalPair
        (parafermionicCoverConfigurationExtensionState n A) c.1) ∈
      parafermionicCoverBoxVertices n := by
  let ω : ParafermionicCoverConfiguration :=
    parafermionicCoverConfigurationExtensionState n A
  by_cases hopen : parafermionicCoverPortBondState ω c.1
  · rw [parafermionicCoverLocalPair, ite_eq_left hopen]
    have he := parafermionicCoverConfigurationExtensionState_true_endpoints_in_box
      n A (parafermionicCoverPortEdge c.1) hopen
    rw [parafermionicCoverPortEdge_eq_incident_pair] at he
    rw [parafermionicCoverOpenPair_vertex]
    exact he _ (Sym2.mem_mk_right _ _)
  · rw [parafermionicCoverLocalPair, ite_eq_right hopen]
    rw [parafermionicCoverClosedPair_vertex]
    exact c.2

theorem parafermionicCoverCornerPair_preservesFinitePort
    (n : ℕ) (c : ParafermionicCoverFinitePort n) :
    parafermionicCoverPortVertex (parafermionicCoverCornerPair c.1) ∈
      parafermionicCoverBoxVertices n := by
  rw [parafermionicCoverCornerPair_vertex]
  exact c.2

def parafermionicCoverFiniteLocalPairPerm (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    Equiv.Perm (ParafermionicCoverFinitePort n) where
  toFun c := ⟨parafermionicCoverLocalPair
      (parafermionicCoverConfigurationExtensionState n A) c.1,
    parafermionicCoverLocalPair_preservesFinitePort n A c⟩
  invFun c := ⟨parafermionicCoverLocalPair
      (parafermionicCoverConfigurationExtensionState n A) c.1,
    parafermionicCoverLocalPair_preservesFinitePort n A c⟩
  left_inv := by
    intro c
    apply Subtype.ext
    exact parafermionicCoverLocalPair_involutive _ c.1
  right_inv := by
    intro c
    apply Subtype.ext
    exact parafermionicCoverLocalPair_involutive _ c.1

def parafermionicCoverFiniteCornerPairPerm (n : ℕ) :
    Equiv.Perm (ParafermionicCoverFinitePort n) where
  toFun c := ⟨parafermionicCoverCornerPair c.1,
    parafermionicCoverCornerPair_preservesFinitePort n c⟩
  invFun c := ⟨parafermionicCoverCornerPair c.1,
    parafermionicCoverCornerPair_preservesFinitePort n c⟩
  left_inv := by
    intro c
    apply Subtype.ext
    exact parafermionicCoverCornerPair_involutive c.1
  right_inv := by
    intro c
    apply Subtype.ext
    exact parafermionicCoverCornerPair_involutive c.1

@[simp] theorem parafermionicCoverFiniteLocalPairPerm_val (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) (c : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteLocalPairPerm n A c).1 =
      parafermionicCoverLocalPair (parafermionicCoverConfigurationExtensionState n A) c.1 := rfl

@[simp] theorem parafermionicCoverFiniteCornerPairPerm_val (n : ℕ)
    (c : ParafermionicCoverFinitePort n) :
    (parafermionicCoverFiniteCornerPairPerm n c).1 =
      parafermionicCoverCornerPair c.1 := rfl

theorem parafermionicCoverFiniteLocalPairPerm_no_fixed_points (n : ℕ)
    (A : Configuration (ParafermionicAmbientGraph n)) :
    ∀ c, parafermionicCoverFiniteLocalPairPerm n A c ≠ c := by
  intro c h
  exact parafermionicCoverLocalPair_ne _ c.1 (congrArg Subtype.val h)

theorem parafermionicCoverFiniteCornerPairPerm_no_fixed_points (n : ℕ) :
    ∀ c, parafermionicCoverFiniteCornerPairPerm n c ≠ c := by
  intro c h
  exact parafermionicCoverCornerPair_ne c.1 (congrArg Subtype.val h)

end
end PottsContinuity.Thm4
