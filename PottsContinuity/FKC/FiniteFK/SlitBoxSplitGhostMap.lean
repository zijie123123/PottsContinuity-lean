-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/SlitBoxSplitGhostMap.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.SlitBoxSplitCoverDomain
public import PottsContinuity.FKC.FiniteFK.SlitBoxQuotientLaw

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

/-- Collapse the two cut sides to the existing slit-box ghost and retain every
split interior vertex as its corresponding outside slit-box vertex. -/
def slitBoxSplitGhostMap (n : ℕ) :
    SlitBoxSplitCoverVertex n → slitBoxGhostCarrier n
  | .inl v => some v
  | .inr _ => none

@[simp] theorem slitBoxSplitGhostMap_inl (n : ℕ)
    (v : SlitBoxSplitInterior n) :
    slitBoxSplitGhostMap n (.inl v) = some v := rfl

@[simp] theorem slitBoxSplitGhostMap_inr (n : ℕ)
    (v : SlitBoxArcSideVertex n) :
    slitBoxSplitGhostMap n (.inr v) = none := rfl

theorem slitBoxSplitGhostMap_surjective (n : ℕ) :
    Function.Surjective (slitBoxSplitGhostMap n) := by
  intro x
  cases x with
  | none =>
      obtain ⟨v, hv⟩ := slitBoxWiredArc_nonempty n
      exact ⟨Sum.inr (⟨v, hv⟩, false), rfl⟩
  | some v => exact ⟨Sum.inl v, rfl⟩

theorem slitBoxSplitGhostMap_eq_none_iff_boundary (n : ℕ)
    (v : SlitBoxSplitCoverVertex n) :
    slitBoxSplitGhostMap n v = none ↔ v ∈ slitBoxSplitCoverBoundary n := by
  cases v with
  | inl u => simp [slitBoxSplitGhostMap, slitBoxSplitCoverBoundary]
  | inr a => exact ⟨fun _ => ⟨a, rfl⟩, fun _ => rfl⟩

/-- The split cover's existing wired boundary is exactly the kernel of the
common map into the slit box's existing ghost carrier. -/
theorem slitBoxSplitBoundary_partition_eq_ker_commonGhostMap (n : ℕ) :
    (BoundaryCondition.wired (slitBoxSplitCoverBoundary n)).partition =
      Setoid.ker (slitBoxSplitGhostMap n) := by
  classical
  apply Setoid.ext
  intro x y
  rw [BoundaryCondition.wired_rel]
  change (x = y ∨ x ∈ slitBoxSplitCoverBoundary n ∧
      y ∈ slitBoxSplitCoverBoundary n) ↔
    slitBoxSplitGhostMap n x = slitBoxSplitGhostMap n y
  constructor
  · rintro (rfl | ⟨hx, hy⟩)
    · rfl
    · cases x with
      | inl u => exact (slitBoxSplitCoverMap_inl_not_boundary n u hx).elim
      | inr a =>
        cases y with
        | inl v => exact (slitBoxSplitCoverMap_inl_not_boundary n v hy).elim
        | inr b => rfl
  · intro h
    cases x with
    | inl u =>
      cases y with
      | inl v =>
        simp only [slitBoxSplitGhostMap] at h
        have huv : u = v := Option.some.inj h
        subst v
        exact Or.inl rfl
      | inr b => cases h
    | inr a =>
      cases y with
      | inl v => cases h
      | inr b =>
        exact Or.inr ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩

end
end PottsContinuity.FKC.FiniteFK
