module

public import PottsContinuity.DualityExt.PositiveIsolatedBoundaryLaw
public import PottsContinuity.DualityExt.PositiveDomainMarkov
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Relabeling finite positive-`q` FK laws

Transporting a finite graph by a vertex equivalence transports its boundary
partition and its configuration law exactly. This provides the algebraic
carrier bridge used when a concrete dual graph is represented on a shifted
integer lattice.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.Duality

noncomputable section

variable {V W : Type*}

/-- Applying the FK dual edge parameter twice returns the original interior
edge probability. -/
theorem dualParameter_involutive {q p : ℝ}
    (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1) :
    dualParameter q (dualParameter q p) = p := by
  have hD : p + q * (1 - p) ≠ 0 :=
    (dualParameter_den_pos hq hp hp1).ne'
  have hpStar := dualParameter_pos hq hp hp1
  have hpStar1 := dualParameter_lt_one hq hp hp1
  have hDStar : dualParameter q p + q * (1 - dualParameter q p) ≠ 0 :=
    (dualParameter_den_pos hq hpStar hpStar1).ne'
  rw [dualParameter, one_sub_dualParameter hq hp hp1, dualParameter]
  field_simp [hD, hDStar]
  ring

/-- Transport a boundary partition and its supported boundary set through a
vertex equivalence. -/
def positiveBoundaryTransport (e : V ≃ W) (ξ : BoundaryCondition V) :
    BoundaryCondition W where
  boundary := e '' ξ.boundary
  partition := Setoid.comap e.symm ξ.partition
  supported := by
    intro u v huv
    have h := (Setoid.comap_rel e.symm ξ.partition u v).mp huv
    rcases ξ.supported h with heq | ⟨hu, hv⟩
    · exact Or.inl (by simpa using congrArg e heq)
    · exact Or.inr
        ⟨⟨e.symm u, hu, Equiv.apply_symm_apply e u⟩,
          ⟨e.symm v, hv, Equiv.apply_symm_apply e v⟩⟩

/-- Pulling a transported partition back along the same equivalence recovers
the original partition exactly. -/
theorem positiveBoundaryTransport_pullback_partition
    (e : V ≃ W) (ξ : BoundaryCondition V) :
    (isolatedExtensionPullbackBoundary e.toEmbedding
      (positiveBoundaryTransport e ξ)).partition = ξ.partition := by
  ext u v
  change ξ.partition.r (e.symm (e u)) (e.symm (e v)) ↔ ξ.partition.r u v
  simp

/-- The positive FK law is invariant under relabeling its vertex carrier by an
equivalence, with the boundary partition transported along that equivalence. -/
theorem positiveFKLaw_relabel_map {G : SimpleGraph V}
    [Finite V] [Finite W]
    {q p : ℝ} (hq : 0 < q) (hp : 0 < p) (hp1 : p < 1)
    (ξ : BoundaryCondition V) (e : V ≃ W) :
    (positiveFKLaw G q p hq hp hp1 ξ).map
        (isolatedExtensionConfigurationEquiv G e.toEmbedding) =
      positiveFKLaw (G.map e.toEmbedding) q p hq hp hp1
        (positiveBoundaryTransport e ξ) := by
  have hpart := positiveBoundaryTransport_pullback_partition e ξ
  have hrename := positiveFKLaw_eq_of_partition_eq
    (G := G) hq hp hp1
    (isolatedExtensionPullbackBoundary e.toEmbedding
      (positiveBoundaryTransport e ξ)) ξ hpart
  rw [← hrename]
  exact positiveFKLaw_isolatedExtension_map_boundary_pullback
    G e.toEmbedding hq hp hp1 (positiveBoundaryTransport e ξ)

end
end PottsContinuity.DualityExt
