-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/HorizontalStripFiniteHeightDualAlternative.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.RectangleDualLeftHalfEmbedding
public import PottsContinuity.FKC.FiniteFK.RectangleDualRightBoundaryPath
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC PottsContinuity.FKC.Medial

noncomputable section

/-- The true finite vertical-crossing event: a center-column vertex at height at
most `n` is connected in the original rectangle to its top row. -/
def rectangleCenterTopConnectionEvent (N n : ℕ) :
    Set (Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n))) :=
  {A | ∃ u v : RectangleVertex (-(N : ℤ), 0) (2*N) (2*n),
    u.1.1 = 0 ∧ u.1.2 ≤ (n : ℤ) ∧ v.1.2 = (2*n : ℤ) ∧
      ActualConnected (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A u v}

/-- If there is no actual center-to-top connection from height at most `n`,
the complementary dual has a path from a face above the center at height in
`[n,2n)` to the left or bottom side of the full expanded dual rectangle. -/
theorem rectangle_no_center_top_connection_dual_left_or_bottom_path
    (N n : ℕ) (A : Configuration (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)))
    (hfail : A ∉ rectangleCenterTopConnectionEvent N n) :
    ∃ j : ℕ, n ≤ j ∧ j < 2*n ∧
      ∃ t : RectangleDualVertex (-(N : ℤ), 0) (2*N) (2*n),
        (openGraph (rectangleDualGraph (-(N : ℤ), 0) (2*N) (2*n))
          (rectangleDualConfiguration (-(N : ℤ), 0) (2*N) (2*n) A)).Reachable
          (rectangleLeftHalfDualVertexEmbedding N n
            (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) j)) t ∧
        (rectangleLeftHalfDualVertexEmbedding N n
          (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) j)).1 =
            (0, (j : ℤ)) ∧
        (t.1.1 = -(N : ℤ) - 1 ∨ t.1.2 = -1) := by
  classical
  by_cases hn : n = 0
  · subst n
    exfalso
    apply hfail
    let u : RectangleVertex (-(N : ℤ), 0) (2*N) 0 := ⟨(0,0), by
      rw [mem_latticeRectangle]
      constructor <;> constructor <;> omega⟩
    exact ⟨u, u, rfl, by norm_num, rfl, SimpleGraph.Reachable.refl u⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let L : Finset (RectangleVertex (-(N : ℤ), 0) (2*N) (2*n)) :=
    Finset.univ.filter fun v => v.1.2 = (2*n : ℤ)
  let σ : RectangleVertex (-(N : ℤ), 0) N (2*n) → Bool :=
    rectangleLeftHalfReachabilityLabel N n A L
  have htop : ∀ v : RectangleVertex (-(N : ℤ), 0) N (2*n),
      v.1.2 = (0 : ℤ) + (2*n : ℤ) → σ v = true := by
    intro v hv
    apply actualReachabilityLabel_eq_true_of_mem
    simp [L, rectangleLeftHalfVertexEmbedding_val,
      hv]
  have hfalse : ∀ j ≤ n, rectangleClampedRightLabel (-(N : ℤ), 0) N (2*n) σ j = false := by
    intro j hj
    have hjmin : Nat.min j (2*n) = j := Nat.min_eq_left (by omega)
    let vh : RectangleVertex (-(N : ℤ), 0) N (2*n) :=
      ⟨(0, (j : ℤ)), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
    let vf : RectangleVertex (-(N : ℤ), 0) (2*N) (2*n) :=
      ⟨(0, (j : ℤ)), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩
    have hmap : rectangleLeftHalfVertexEmbedding N n vh = vf := by
      apply Subtype.ext
      rfl
    have hclamp0 :
        (⟨((-(N : ℤ) + (N : ℤ)),
            (0 : ℤ) + ((Nat.min j (2*n) : ℕ) : ℤ)), by
          rw [mem_latticeRectangle]
          constructor <;> constructor <;> omega⟩ :
          RectangleVertex (-(N : ℤ), 0) N (2*n)) = vh := by
      apply Subtype.ext
      simp [vh, hjmin]
    have hvertex : rectangleClampedRightLabel (-(N : ℤ), 0) N (2*n) σ j =
        actualReachabilityLabel (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L vf := by
      have hσ : σ (⟨((-(N : ℤ) + (N : ℤ)),
          (0 : ℤ) + ((Nat.min j (2*n) : ℕ) : ℤ)), by
            rw [mem_latticeRectangle]
            constructor <;> constructor <;> omega⟩ :
          RectangleVertex (-(N : ℤ), 0) N (2*n)) = σ vh :=
        congrArg σ hclamp0
      have hσfull : σ vh =
          actualReachabilityLabel (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L vf := by
        dsimp only [σ, rectangleLeftHalfReachabilityLabel]
        exact congrArg (actualReachabilityLabel
          (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L) hmap
      calc
        _ = σ (⟨((-(N : ℤ) + (N : ℤ)),
            (0 : ℤ) + ((Nat.min j (2*n) : ℕ) : ℤ)), by
              rw [mem_latticeRectangle]
              constructor <;> constructor <;> omega⟩ :
            RectangleVertex (-(N : ℤ), 0) N (2*n)) := by
              simp only [rectangleClampedRightLabel]
        _ = σ vh := hσ
        _ = actualReachabilityLabel (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A L vf := hσfull
    rw [hvertex]
    have hNo : ¬ ∃ s, s ∈ L ∧ ActualConnected
        (rectangleGraph (-(N : ℤ), 0) (2*N) (2*n)) A s vf := by
      rintro ⟨s, hs, hconn⟩
      apply hfail
      refine ⟨vf, s, ?_, ?_, (Finset.mem_filter.mp hs).2, hconn.symm⟩
      · simp [vf]
      · change (j : ℤ) ≤ (n : ℤ)
        exact_mod_cast hj
    simp [actualReachabilityLabel, hNo]
  have htopRight : rectangleClampedRightLabel (-(N : ℤ), 0) N (2*n) σ (2*n) = true := by
    have htop' := htop
      (⟨(0, (2*n : ℤ)), by rw [mem_latticeRectangle]; constructor <;> constructor <;> omega⟩)
      (by change (2*n : ℤ) = 0 + (2*n : ℤ); omega)
    simpa [rectangleClampedRightLabel, Nat.min_self] using htop'
  obtain ⟨b, hb, t, ht, hreach⟩ := rectangleDual_right_boundary_reachable
    (-(N : ℤ), 0) N (2*n) σ htop (hfalse 0 (by omega)) htopRight
  obtain ⟨j, hjlt, hbj, hjn⟩ := rectangleDual_right_boundary_reachable_port_index_ge
    (-(N : ℤ), 0) N (2*n) σ n hfalse b hb t ht hreach
  have hcoord : b.1 = (0, (j : ℤ)) := by
    calc
      b.1 = (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) j).1 :=
        congrArg (fun z : RectangleDualVertex (-(N : ℤ), 0) N (2*n) => z.1) hbj.symm
      _ = (0, (j : ℤ)) := by
        rw [rectangleDualRightPort_val_of_lt (-(N : ℤ), 0) N (2*n) j hjlt]
        apply Prod.ext <;> simp
  have htarget : t.1.1 = -(N : ℤ)-1 ∨ t.1.2 = -1 := by
    rcases Finset.mem_union.mp ht with hleft | hbottom
    · rcases Finset.mem_image.mp hleft with ⟨i, hi, heq⟩
      have hval := congrArg (fun z : RectangleDualVertex (-(N : ℤ), 0) N (2*n) => z.1) heq
      simp [rectangleDualLeftPortVertex] at hval
      exact Or.inl (by simpa using (congrArg Prod.fst hval).symm)
    · rcases Finset.mem_image.mp hbottom with ⟨i, hi, heq⟩
      have hval := congrArg (fun z : RectangleDualVertex (-(N : ℤ), 0) N (2*n) => z.1) heq
      simp [rectangleDualBottomPortVertex] at hval
      exact Or.inr (by simpa using (congrArg Prod.snd hval).symm)
  refine ⟨j, hjn, hjlt, rectangleLeftHalfDualVertexEmbedding N n t,
    ?_, ?_, htarget⟩
  · have hfull := rectangleLeftHalf_labelCut_reachable_is_fullDual_open N n A L b t hreach
    have hbeq : rectangleLeftHalfDualVertexEmbedding N n b =
        rectangleLeftHalfDualVertexEmbedding N n
          (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) j) :=
      congrArg (rectangleLeftHalfDualVertexEmbedding N n) hbj.symm
    rw [hbeq] at hfull
    exact hfull
  · calc
      (rectangleLeftHalfDualVertexEmbedding N n
        (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) j)).1 =
          (rectangleDualRightPortVertex (-(N : ℤ), 0) N (2*n) j).1 := rfl
      _ = (0, (j : ℤ)) := by
        rw [rectangleDualRightPort_val_of_lt (-(N : ℤ), 0) N (2*n) j hjlt]
        apply Prod.ext <;> simp

end
end PottsContinuity.FKC.FiniteFK
