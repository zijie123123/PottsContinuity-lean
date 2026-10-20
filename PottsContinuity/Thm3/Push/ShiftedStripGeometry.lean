module

public import PottsContinuity.Thm3.Push.ThirdRounding
public import PottsContinuity.Thm3.RSW.StripWindow

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
noncomputable section

/-- At scale 3*s, translate the exact base rectangle down by s into the
Lemma-2 strip. Both its bottom and its wired top align exactly. -/
def baseStripWindowEmbedding (k : ℝ) (s M : ℕ)
    (hM : ⌊k * (3*s : ℕ)⌋ ≤ (M : ℤ)) :
    (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ)) ↪
      (stripWindow s M : Set (ℤ × ℤ)) where
  toFun v := ⟨(v.val.1, v.val.2 - s), by
    change (v.val.1, v.val.2 - s) ∈ stripWindow s M
    have hv := (mem_topWiredRectangle_iff k (4/3) (3*s) v.val).mp v.property
    rw [floor_four_thirds_mul_three] at hv
    simp only [stripWindow, PottsContinuity.latticeRectangle,
      Finset.mem_product, Finset.mem_Icc]
    push_cast at hM hv ⊢
    omega⟩
  inj' := by
    intro x y h
    have hc := congrArg
      (fun z : (stripWindow s M : Set (ℤ × ℤ)) => z.val) h
    apply Subtype.ext
    simp only [Prod.mk.injEq] at hc
    exact Prod.ext hc.1 (by omega)

theorem baseStripWindowEmbedding_map_le (k : ℝ) (s M : ℕ)
    (hM : ⌊k * (3*s : ℕ)⌋ ≤ (M : ℤ)) :
    (PottsContinuity.squareLattice.induce
      (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ))).map
        (baseStripWindowEmbedding k s M hM) ≤
      PottsContinuity.squareLattice.induce (stripWindow s M : Set (ℤ × ℤ)) := by
  intro x y hxy
  obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  change |u.val.1 - v.val.1| + |(u.val.2 - s) - (v.val.2 - s)| = 1
  have heq : (u.val.2 - (s : ℤ)) - (v.val.2 - s) = u.val.2 - v.val.2 := by ring
  rw [heq]
  exact huv

theorem baseStripWindowEmbedding_neighbor_closed (k : ℝ) (s M : ℕ)
    (hM : ⌊k * (3*s : ℕ)⌋ ≤ (M : ℤ))
    {x : (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ))}
    (hx : x ∉ (topWiredRectangleBoundary k (4/3) (3*s)).boundary)
    {y : (stripWindow s M : Set (ℤ × ℤ))}
    (hxy : (PottsContinuity.squareLattice.induce
      (stripWindow s M : Set (ℤ × ℤ))).Adj (baseStripWindowEmbedding k s M hM x) y) :
    ∃ z : (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ)),
      baseStripWindowEmbedding k s M hM z = y ∧
      (PottsContinuity.squareLattice.induce
        (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ))).Adj x z := by
  have hm := (mem_topWiredRectangle_iff k (4/3) (3*s) x.val).mp x.property
  rw [floor_four_thirds_mul_three] at hm
  have hy : y.val ∈ stripWindow s M := y.property
  simp only [stripWindow, PottsContinuity.latticeRectangle,
    Finset.mem_product, Finset.mem_Icc] at hy
  change ¬ (x.val.1 = -⌊k*(3*s : ℕ)⌋ ∨ x.val.1 = ⌊k*(3*s : ℕ)⌋ ∨
    x.val.2 = ⌊(4/3 : ℝ)*(3*s : ℕ)⌋) at hx
  rw [floor_four_thirds_mul_three] at hx
  have hd : |x.val.1 - y.val.1| + |(x.val.2 - s) - y.val.2| = 1 := hxy
  have hz : (y.val.1, y.val.2 + s) ∈ topWiredRectangle k (4/3) (3*s) := by
    rw [mem_topWiredRectangle_iff, floor_four_thirds_mul_three]
    simp only [abs_eq_max_neg] at *
    push_cast at hM hm hx hy ⊢
    omega
  refine ⟨⟨(y.val.1, y.val.2+s), hz⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp only [baseStripWindowEmbedding, Function.Embedding.coeFn_mk]
    simp
  · change |x.val.1 - y.val.1| + |x.val.2 - (y.val.2 + s)| = 1
    have heq : x.val.2 - (y.val.2 + (s : ℤ)) = (x.val.2 - s) - y.val.2 := by ring
    rw [heq]
    exact hd

theorem baseStripWindowEmbedding_boundary_avoid (k : ℝ) (s M : ℕ)
    (hM : ⌊k * (3*s : ℕ)⌋ ≤ (M : ℤ))
    {x : (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ))}
    (hx : x ∉ (topWiredRectangleBoundary k (4/3) (3*s)).boundary) :
    baseStripWindowEmbedding k s M hM x ∉ (stripWindowBoundary s M 0).boundary := by
  change ¬ ((x.val.2 - s) = 3*(s : ℤ) ∨
    (0 : Fin 2) = 1 ∧ (_ ∨ _))
  simp only [Fin.zero_eq_one_iff]
  change ¬ (x.val.1 = -⌊k*(3*s : ℕ)⌋ ∨ x.val.1 = ⌊k*(3*s : ℕ)⌋ ∨
    x.val.2 = ⌊(4/3 : ℝ)*(3*s : ℕ)⌋) at hx
  rw [floor_four_thirds_mul_three] at hx
  push_cast at hx
  omega

/-- Genuine finite-window law domination for the translated base rectangle.
All one-sided closure and boundary hypotheses have been discharged above. -/
theorem baseStripWindow_restriction_probability_le (θ : Parameters) (k : ℝ) (s M : ℕ)
    (hM : ⌊k * (3*s : ℕ)⌋ ≤ (M : ℤ))
    (S : Set (Configuration (PottsContinuity.squareLattice.induce
      (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ)))))
    (hS : IsUpperSet S) :
    (measure (PottsContinuity.squareLattice.induce (stripWindow s M : Set (ℤ × ℤ)))
      θ (stripWindowBoundary s M 0)
      {A | embeddedConfigurationRestriction _ _ (baseStripWindowEmbedding k s M hM)
        (baseStripWindowEmbedding_map_le k s M hM) A ∈ S}).toReal ≤
    (measure (PottsContinuity.squareLattice.induce
      (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ))) θ
      (topWiredRectangleBoundary k (4/3) (3*s)) S).toReal :=
  embeddedConfigurationRestriction_preimage_measure_le_wired_of_closedInterior
    (baseStripWindowEmbedding k s M hM) (baseStripWindowEmbedding_map_le k s M hM)
    θ (stripWindowBoundary s M 0) (topWiredRectangleBoundary k (4/3) (3*s)).boundary
    (fun _ hx _ hxy => baseStripWindowEmbedding_neighbor_closed k s M hM hx hxy)
    (fun _ hx => baseStripWindowEmbedding_boundary_avoid k s M hM hx) S hS

end
end PottsContinuity.Push
