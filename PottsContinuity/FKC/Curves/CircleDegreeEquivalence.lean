-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/CircleDegreeEquivalence.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.CircleMapDegree
public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Algebra.Group.Int.Units

/-!
# A circle homotopy equivalence has degree plus or minus one

Degree is invariant under actual free homotopies of circle maps and is
multiplicative under composition. A supplied homotopy equivalence has genuine
homotopy-inverse proofs, so the two integer degrees multiply to one.
-/

@[expose] public section

namespace PottsContinuity.FKC

open scoped unitInterval

theorem circleMapDegree_id : circleMapDegree (ContinuousMap.id Circle) = 1 := by
  have h : standardCirclePath.map (ContinuousMap.id Circle).continuous = standardCirclePath := by
    ext t
    rfl
  unfold circleMapDegree
  rw [h]
  exact degree_standardCirclePath

theorem circleMapDegree_comp (f g : C(Circle, Circle)) :
    circleMapDegree (f.comp g) = circleMapDegree f * circleMapDegree g := by
  simpa only [circleMapDegree, Path.map_map] using
    degree_map_circle f (standardCirclePath.map g.continuous)

/-- Free homotopies of actual circle maps preserve their degree. -/
theorem circleMapDegree_eq_of_homotopic {f g : C(Circle, Circle)} (h : f.Homotopic g) :
    circleMapDegree f = circleMapDegree g := by
  obtain ⟨F⟩ := h
  apply Circle.degree_eq_of_homotopy (standardCirclePath.map f.continuous)
    (standardCirclePath.map g.continuous)
    (⟨fun u : I × I => F (u.1, standardCirclePath u.2), by fun_prop⟩ : C(I × I, Circle))
  · intro t
    exact F.map_zero_left _
  · intro t
    exact F.map_one_left _
  · intro s
    change F (s, standardCirclePath 0) = F (s, standardCirclePath 1)
    rw [standardCirclePath.source, standardCirclePath.target]

/-- A genuine circle homotopy equivalence has degree either one or negative one. -/
theorem circleMapDegree_homotopyEquiv (e : ContinuousMap.HomotopyEquiv Circle Circle) :
    circleMapDegree e.toFun = 1 ∨ circleMapDegree e.toFun = -1 := by
  apply Int.eq_one_or_neg_one_of_mul_eq_one (v := circleMapDegree e.invFun)
  rw [← circleMapDegree_comp,
    circleMapDegree_eq_of_homotopic e.right_inv, circleMapDegree_id]

/-- Equality at every parameter implies equality of loop degrees even if their
basepoints were packaged differently. -/
theorem circleDegree_eq_of_pointwise_eq {x y : Circle} (γ : Path x x) (η : Path y y)
    (h : ∀ t, γ t = η t) : Circle.degree γ = Circle.degree η := by
  apply Circle.degree_eq_of_homotopy γ η
    (⟨fun u : I × I => γ u.2, γ.continuous.comp continuous_snd⟩ : C(I × I, Circle))
  · intro t
    rfl
  · intro t
    exact h t
  · intro s
    change γ 0 = γ 1
    rw [γ.source, γ.target]

end PottsContinuity.FKC
