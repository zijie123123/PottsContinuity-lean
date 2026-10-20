module

public import PottsContinuity.Thm3.Push.ThirdRounding
public import PottsContinuity.Thm3.RSW.EmbeddedComparison

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
noncomputable section

/-- At n=3*s, shift the induction rectangle up by s into the next-height
rectangle. Both tops and both wired sides align exactly, including all floors. -/
def pushShiftEmbedding (k ℓ : ℝ) (s : ℕ) :
    (squareLattice.induce (topWiredRectangle k ℓ (3*s) : Set (ℤ × ℤ))) ↪g
      squareLattice.induce (topWiredRectangle k (ℓ+1/3) (3*s) : Set (ℤ × ℤ)) where
  toFun v := ⟨(v.val.1, v.val.2+s), by
    change (v.val.1,v.val.2+(s : ℤ)) ∈ topWiredRectangle k (ℓ+1/3) (3*s)
    rw [mem_topWiredRectangle_iff, floor_height_add_third_mul_three]
    have hv := (mem_topWiredRectangle_iff k ℓ (3*s) v.val).mp v.property
    exact ⟨hv.1,hv.2.1,by omega,by omega⟩⟩
  inj' := by
    intro u v h
    have hc := congrArg (fun z : (topWiredRectangle k (ℓ+1/3) (3*s) : Set (ℤ × ℤ)) => z.val) h
    apply Subtype.ext
    simp only [Prod.mk.injEq] at hc
    exact Prod.ext hc.1 (by omega)
  map_rel_iff' := by
    intro u v
    change (|u.val.1-v.val.1|+|(u.val.2+s)-(v.val.2+s)|=1) ↔
      (|u.val.1-v.val.1|+|u.val.2-v.val.2|=1)
    have heq : (u.val.2+(s : ℤ))-(v.val.2+s)=u.val.2-v.val.2 := by ring
    rw [heq]

theorem pushShiftEmbedding_map_le (k ℓ : ℝ) (s : ℕ) :
    (squareLattice.induce (topWiredRectangle k ℓ (3*s) : Set (ℤ × ℤ))).map
      (pushShiftEmbedding k ℓ s).toEmbedding ≤
    squareLattice.induce (topWiredRectangle k (ℓ+1/3) (3*s) : Set (ℤ × ℤ)) := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ _ _).mp hxy
  exact (pushShiftEmbedding k ℓ s).map_rel_iff'.mpr huv

/-- The pulled-back ORIGINAL boundary partition is exactly top-and-sides
wiring on the shifted induction rectangle. External bonds below its free
bottom are handled by the lower embedded-law comparison, not discarded. -/
theorem pushShiftEmbedding_pullback_partition (k ℓ : ℝ) (s : ℕ) :
    (isolatedExtensionPullbackBoundary (pushShiftEmbedding k ℓ s).toEmbedding
      (topWiredRectangleBoundary k (ℓ+1/3) (3*s))).partition =
    (topWiredRectangleBoundary k ℓ (3*s)).partition := by
  apply Setoid.ext
  intro u v
  change ((pushShiftEmbedding k ℓ s u = pushShiftEmbedding k ℓ s v) ∨
      ((u.val.1 = -⌊k*(3*s : ℕ)⌋ ∨ u.val.1 = ⌊k*(3*s : ℕ)⌋ ∨
        u.val.2+s=⌊(ℓ+1/3)*(3*s : ℕ)⌋) ∧
       (v.val.1 = -⌊k*(3*s : ℕ)⌋ ∨ v.val.1 = ⌊k*(3*s : ℕ)⌋ ∨
        v.val.2+s=⌊(ℓ+1/3)*(3*s : ℕ)⌋))) ↔
    u=v ∨ ((u.val.1 = -⌊k*(3*s : ℕ)⌋ ∨ u.val.1 = ⌊k*(3*s : ℕ)⌋ ∨
      u.val.2=⌊ℓ*(3*s : ℕ)⌋) ∧
      (v.val.1 = -⌊k*(3*s : ℕ)⌋ ∨ v.val.1 = ⌊k*(3*s : ℕ)⌋ ∨
      v.val.2=⌊ℓ*(3*s : ℕ)⌋))
  rw [floor_height_add_third_mul_three]
  simp only [(pushShiftEmbedding k ℓ s).injective.eq_iff, add_left_inj]

/-- The shifted restricted-configuration law dominates the unchanged source
law for EVERY increasing event, at arbitrary interior FK parameters. -/
theorem pushShift_restriction_probability_ge (θ : Parameters) (k ℓ : ℝ) (s : ℕ)
    (E : Set (Configuration (squareLattice.induce
      (topWiredRectangle k ℓ (3*s) : Set (ℤ × ℤ))))) (hE : IsUpperSet E) :
    (measure _ θ (topWiredRectangleBoundary k ℓ (3*s)) E).toReal ≤
    (measure _ θ (topWiredRectangleBoundary k (ℓ+1/3) (3*s))
      {A | embeddedConfigurationRestriction _ _ (pushShiftEmbedding k ℓ s).toEmbedding
        (pushShiftEmbedding_map_le k ℓ s) A ∈ E}).toReal := by
  have h := embedded_boundary_probability_le _ _ (pushShiftEmbedding k ℓ s).toEmbedding
    (pushShiftEmbedding_map_le k ℓ s) θ (topWiredRectangleBoundary k (ℓ+1/3) (3*s)) E hE
  have heq := law_eq_of_boundary_partition_eq (G := squareLattice.induce
    (topWiredRectangle k ℓ (3*s) : Set (ℤ × ℤ))) θ _ _
    (pushShiftEmbedding_pullback_partition k ℓ s)
  unfold PD.FK.measure at h ⊢
  rw [heq] at h
  exact h

end
end PottsContinuity.Push
