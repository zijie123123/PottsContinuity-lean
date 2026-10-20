-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/CircleMapDegree.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.WindingCircle
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Degree of a continuous circle map acting on loops

The standard circle loop is parametrized by its actual angle `2 * pi * t`.
Every continuous circle self-map has a continuous lift after composition with
the real exponential covering map. Its increment under a full turn determines
the degree, and the same increment formula computes its action on every loop.
No smoothness or injectivity assumption is imposed on the circle map.
-/

@[expose] public section

namespace PottsContinuity.FKC

open scoped unitInterval

noncomputable section

/-- The unit circle traversed once in the positive direction, with circle-valued carrier. -/
def standardCirclePath : Path (1 : Circle) 1 where
  toFun t := Circle.exp (2 * Real.pi * t)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp] theorem standardCirclePath_apply (t : I) :
    standardCirclePath t = Circle.exp (2 * Real.pi * t) := rfl

/-- The positive standard loop has degree one, calculated from its angle lift. -/
theorem degree_standardCirclePath : Circle.degree standardCirclePath = 1 := by
  apply Circle.degree_eq_of_sub_eq (θ := fun t => 2 * Real.pi * t)
  · fun_prop
  · intro t
    rfl
  · simp

/-- The degree of a continuous circle self-map, evaluated on the positive standard loop. -/
def circleMapDegree (f : C(Circle, Circle)) : ℤ :=
  Circle.degree (standardCirclePath.map f.continuous)

private theorem exists_circleMapLift (f : C(Circle, Circle)) :
    ∃ L : C(ℝ, ℝ), ∀ t, Circle.exp (L t) = f (Circle.exp t) := by
  obtain ⟨L, hL, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (f.comp Circle.exp) 0 (Complex.arg (f 1)) (by simp)
  exact ⟨L, fun t => congr_fun hL.2 t⟩

private theorem circleMapLift_fullTurn (f : C(Circle, Circle)) (L : C(ℝ, ℝ))
    (hL : ∀ t, Circle.exp (L t) = f (Circle.exp t)) (t : ℝ) :
    L (t + 2 * Real.pi) - L t = (circleMapDegree f : ℝ) * (2 * Real.pi) := by
  have hconst : L (t + 2 * Real.pi) - L t = L (2 * Real.pi) - L 0 := by
    have h := Circle.isCoveringMap_exp.const_of_comp
      (g := fun s : ℝ => L (s + 2 * Real.pi) - L s) (by fun_prop)
      (fun s r => by
        simp only [Circle.exp_sub, hL]
        rw [Circle.periodic_exp s, Circle.periodic_exp r, div_self', div_self']) t 0
    simpa only [zero_add] using h
  have hdegree := Circle.sub_eq_degree_mul (standardCirclePath.map f.continuous)
    (θ := fun s : I => L (2 * Real.pi * s)) (by fun_prop)
    (fun s => hL (2 * Real.pi * s))
  have hdegree' : L (2 * Real.pi) - L 0 =
      (circleMapDegree f : ℝ) * (2 * Real.pi) := by
    simpa only [Set.Icc.coe_one, Set.Icc.coe_zero, mul_one, mul_zero, circleMapDegree] using hdegree
  exact hconst.trans hdegree'

private theorem circleMapLift_intTurn (f : C(Circle, Circle)) (L : C(ℝ, ℝ))
    (hL : ∀ t, Circle.exp (L t) = f (Circle.exp t)) (t : ℝ) (n : ℤ) :
    L (t + n * (2 * Real.pi)) - L t =
      (circleMapDegree f : ℝ) * n * (2 * Real.pi) := by
  have hperiod : Function.Periodic
      (fun s : ℝ => L s - (circleMapDegree f : ℝ) * s) (2 * Real.pi) := by
    intro s
    have h := circleMapLift_fullTurn f L hL s
    dsimp only
    nlinarith only [h]
  have h := hperiod.int_mul n t
  nlinarith only [h]

/-- A continuous circle self-map multiplies the degree of every closed circle path
by its own degree, measured on the standard positive circle. -/
theorem degree_map_circle (f : C(Circle, Circle)) {x : Circle} (γ : Path x x) :
    Circle.degree (γ.map f.continuous) = circleMapDegree f * Circle.degree γ := by
  obtain ⟨L, hL⟩ := exists_circleMapLift f
  obtain ⟨θ, hθlift, -⟩ := Circle.isCoveringMap_exp.exists_path_lifts γ.toContinuousMap
    (Complex.arg x) (by simp)
  have hθ (t : I) : Circle.exp (θ t) = γ t := congr_fun hθlift t
  apply Circle.degree_eq_of_sub_eq (γ.map f.continuous) (θ := fun t => L (θ t)) (by fun_prop)
  · intro t
    change Circle.exp (L (θ t)) = f (γ t)
    rw [hL, hθ]
  · have hθdegree := Circle.sub_eq_degree_mul γ θ.continuous hθ
    have hend : θ 1 = θ 0 + (Circle.degree γ : ℝ) * (2 * Real.pi) := by
      linarith only [hθdegree]
    rw [hend]
    simpa only [Int.cast_mul] using circleMapLift_intTurn f L hL (θ 0) (Circle.degree γ)

end

end PottsContinuity.FKC
