-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripReflectedHeightDualAlternative.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.HorizontalStripFiniteHeightDualAlternative
public import PottsContinuity.FKC.FiniteFK.RectangleDualVerticalReflection
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

private theorem rectangleDualVerticalReflection_symm_apply
    (N n : ℕ) (z : RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n)) :
    (rectangleDualGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)).symm z =
      rectangleDualGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n) z := by
  let e := rectangleDualGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)
  have hleft : e (e.symm z) = z := e.apply_symm_apply z
  have hright : e (e z) = z := by
    change rectangleDualVerticalReflectionVertexEquiv (-(N : ℤ), 0) (2*N) (2*n)
      (rectangleDualVerticalReflectionVertexEquiv (-(N : ℤ), 0) (2*N) (2*n) z) = z
    exact (rectangleDualVerticalReflectionVertexEquiv
      (-(N : ℤ), 0) (2*N) (2*n)).left_inv z
  exact e.injective (hleft.trans hright.symm)

private theorem rectangleDualVerticalReflection_symm_val
    (N n : ℕ) (z : RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n)) :
    ((rectangleDualGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)).symm z).val =
      (z.val.1, (2*n : ℤ) - 1 - z.val.2) := by
  rw [rectangleDualVerticalReflection_symm_apply]
  change (rectangleDualVerticalReflectionVertexEquiv (-(N : ℤ), 0) (2*N) (2*n) z).val = _
  rw [rectangleDualVerticalReflectionVertexEquiv_val]
  norm_num

private theorem rectangleDualConfiguration_reflection_symm
    (N n : ℕ) (B : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n))) :
    (configurationIso (rectangleDualGraphVerticalReflectionIso
      (-(N : ℤ), 0) (2*N) (2*n))).symm
      (rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n)
        (configurationIso (rectangleGraphVerticalReflectionIso
          (-(N : ℤ), 0) (2*N) (2*n)) B)) =
      rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n) B := by
  have hc := rectanglePrimalDualConfiguration_reflection_commute
    (-(N : ℤ), 0) (2*N) (2*n) B
  rw [← hc]
  exact (configurationIso (rectangleDualGraphVerticalReflectionIso
    (-(N : ℤ), 0) (2*N) (2*n))).symm_apply_apply _

private theorem rectangleDual_reflected_reachable
    (N n : ℕ) (B : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)))
    {u v : RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n)}
    (h : (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
      (rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n)
        (configurationIso (rectangleGraphVerticalReflectionIso
          (-(N : ℤ), 0) (2*N) (2*n)) B))).Reachable u v) :
    (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
      (rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n) B)).Reachable
      ((rectangleDualGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)).symm u)
      ((rectangleDualGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)).symm v) := by
  let eD := rectangleDualGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)
  let D' := rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n)
    (configurationIso (rectangleGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)) B)
  let D := rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n) B
  have hc : (configurationIso eD).symm D' = D :=
    rectangleDualConfiguration_reflection_symm N n B
  have h' : (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n)) D').Reachable u v := by
    change (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
      (rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n)
        (configurationIso (rectangleGraphVerticalReflectionIso
          (-(N : ℤ), 0) (2*N) (2*n)) B))).Reachable u v
    exact h
  have hm := SimpleGraph.Reachable.map
    ((openGraphIso eD.symm D').toRelEmbedding.toRelHom) h'
  change (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n)) D).Reachable
    (eD.symm u) (eD.symm v)
  rw [← hc]
  exact hm

private theorem rectangleDual_reflected_left_or_bottom_to_left_or_top
    (N n : ℕ) (t : RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n))
    (ht : t.1.1 = -(N : ℤ)-1 ∨ t.1.2 = -1) :
    let t' := (rectangleDualGraphVerticalReflectionIso
      (-(N : ℤ), 0) (2*N) (2*n)).symm t
    t'.1.1 = -(N : ℤ)-1 ∨ t'.1.2 = (2*n : ℤ) := by
  dsimp
  rw [rectangleDualVerticalReflection_symm_val]
  rcases ht with hx | hy
  · exact Or.inl hx
  · right
    rw [hy]
    norm_num

private theorem rectangle_reflected_failure_has_dual_left_bottom
    (N n : ℕ) (B : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)))
    (hfail : configurationIso
      (rectangleGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)) B ∉
        rectangleCenterTopConnectionEvent N n) :
    ∃ J : ℕ, n ≤ J ∧ J < 2*n ∧
      ∃ t : RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n),
        (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
          (rectanglePrimalDualConfigurationEquiv (-(N : ℤ), 0) (2*N) (2*n)
            (configurationIso (rectangleGraphVerticalReflectionIso
              (-(N : ℤ), 0) (2*N) (2*n)) B))).Reachable
          (rectangleLeftHalfDualVertexEmbedding N n
            (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) J)) t ∧
        (rectangleLeftHalfDualVertexEmbedding N n
          (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) J)).1 =
            (0, (J : ℤ)) ∧
        (t.1.1 = -(N : ℤ)-1 ∨ t.1.2 = -1) := by
  exact rectangle_no_center_top_connection_dual_left_or_bottom_path N n
    (configurationIso (rectangleGraphVerticalReflectionIso
      (-(N : ℤ), 0) (2*N) (2*n)) B) hfail

/-- Reflecting the primal configuration turns the finite-height alternative
into a path from a retained lower center face to the left or top side. The
face-base reflection has the required `-1` shift. -/
theorem rectangle_reflected_no_center_top_connection_dual_left_or_top_path
    (N n : ℕ) (B : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)))
    (hfail : configurationIso
      (rectangleGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)) B ∉
        rectangleCenterTopConnectionEvent N n) :
    ∃ s t : RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n),
      s.1.1 = 0 ∧ 0 ≤ s.1.2 ∧ s.1.2 < (n : ℤ) ∧
      (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
        (rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) B)).Reachable s t ∧
      (t.1.1 = -(N : ℤ) - 1 ∨ t.1.2 = (2*n : ℤ)) := by
  let eP := rectangleGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)
  let eD := rectangleDualGraphVerticalReflectionIso (-(N : ℤ), 0) (2*N) (2*n)
  obtain ⟨J, hJlo, hJhi, t', hpath', hstart', hend'⟩ :=
    rectangle_reflected_failure_has_dual_left_bottom N n B hfail
  let b' := rectangleLeftHalfDualVertexEmbedding N n
    (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) J)
  let s := eD.symm b'
  let t := eD.symm t'
  have hpath := rectangleDual_reflected_reachable N n B hpath'
  have hcast : ((2*n - 1 - J : ℕ) : ℤ) = (2*n : ℤ) - 1 - J := by
    rw [Nat.cast_sub (show J ≤ 2*n - 1 by omega),
      Nat.cast_sub (show 1 ≤ 2*n by omega)]
    norm_num
  have hsval : s.1 = (0, ((2*n - 1 - J : ℕ) : ℤ)) := by
    rw [show s = eD.symm b' from rfl,
      rectangleDualVerticalReflection_symm_val N n b']
    rw [hstart']
    simp only [Prod.mk.injEq]
    rw [hcast]
    trivial
  have hnpos : 0 < n := by omega
  have hjlo : 0 ≤ (2*n - 1 - J : ℕ) := by omega
  have hjhi : (2*n - 1 - J : ℕ) < n := by omega
  refine ⟨s, t, ?_, ?_, ?_, hpath, ?_⟩
  · exact congrArg Prod.fst hsval
  · have hs2 := congrArg Prod.snd hsval
    rw [hs2]
    change 0 ≤ ((2*n - 1 - J : ℕ) : ℤ)
    exact_mod_cast hjlo
  · have hs2 := congrArg Prod.snd hsval
    rw [hs2]
    change ((2*n - 1 - J : ℕ) : ℤ) < (n : ℤ)
    exact_mod_cast hjhi
  · exact rectangleDual_reflected_left_or_bottom_to_left_or_top N n t' hend'

end
end PottsContinuity.FKC.FiniteFK
