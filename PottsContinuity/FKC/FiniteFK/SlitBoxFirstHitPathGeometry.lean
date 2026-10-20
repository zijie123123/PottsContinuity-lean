-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxFirstHitPathGeometry.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.ActualConnectionFirstHitPath
public import PottsContinuity.FKC.FiniteFK.SlitBoxDomain
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC

/-- The literal vertex projection maps the open slit graph into the square
lattice, since slit edges are retained square-lattice edges. -/
def slitBoxOpenGraphToSquareLatticeHom (n : ℕ)
    (A : Configuration (slitBoxGraph n)) :
    openGraph (slitBoxGraph n) A →g squareLattice where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    exact ((slitBoxGraph_adj_iff n u v).mp
      (openGraph_le (slitBoxGraph n) A huv)).1

@[simp] theorem slitBoxOpenGraphToSquareLatticeHom_apply (n : ℕ)
    (A : Configuration (slitBoxGraph n)) (u : SlitBoxVertex n) :
    slitBoxOpenGraphToSquareLatticeHom n A u = u.val := rfl

theorem slitBoxOpenGraphToSquareLatticeHom_injective (n : ℕ)
    (A : Configuration (slitBoxGraph n)) :
    Function.Injective (slitBoxOpenGraphToSquareLatticeHom n A) :=
  Subtype.val_injective

/-- Every actual wired-arc connection has a simple actual open path whose
square-lattice image stays in the box and first meets the lattice wired arc at
its terminal vertex. The retained open walk and its image are both returned. -/
theorem slitBoxWiredArcConnectionEvent_firstHit_path_geometry
    (n : ℕ) (A : Configuration (slitBoxGraph n)) (u : SlitBoxVertex n)
    (hA : A ∈ slitBoxWiredArcConnectionEvent n u) :
    ∃ t ∈ slitBoxWiredArc n,
      ∃ p : (openGraph (slitBoxGraph n) A).Walk u t,
        p.IsPath ∧
        (p.map (slitBoxOpenGraphToSquareLatticeHom n A)).IsPath ∧
        (∀ x ∈ p.support, x ∈ slitBoxWiredArc n → x = t) ∧
        ∀ y ∈ (p.map (slitBoxOpenGraphToSquareLatticeHom n A)).support,
          y ∈ latticeRectangle (-(n : ℤ), -(n : ℤ)) (2 * n) (2 * n) ∧
          (y.1 = 0 ∧ 0 ≤ y.2 ∧ y.2 ≤ n → y = t.val) := by
  classical
  obtain ⟨t, ht, p, hp, hfirst⟩ :=
    actualConnected_exists_first_hit_path A hA
  have hmappedPath :
      (p.map (slitBoxOpenGraphToSquareLatticeHom n A)).IsPath :=
    hp.map (slitBoxOpenGraphToSquareLatticeHom_injective n A)
  refine ⟨t, ht, p, hp, hmappedPath, hfirst, ?_⟩
  intro y hy
  rw [SimpleGraph.Walk.support_map] at hy
  rcases List.mem_map.mp hy with ⟨x, hx, hxy⟩
  subst y
  constructor
  · exact x.property
  · intro hyArc
    have hxArc : x ∈ slitBoxWiredArc n := by
      rw [mem_slitBoxWiredArc_iff]
      exact hyArc
    have hxt : x = t := hfirst x hx hxArc
    exact congrArg Subtype.val hxt

end PottsContinuity.FKC.FiniteFK
