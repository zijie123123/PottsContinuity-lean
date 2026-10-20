module

public import PottsContinuity.Thm3.Prop4.TiltedCutSeparation
public import PottsContinuity.Thm3.Prop4.ExteriorPartition
public import PottsContinuity.PD.FK.ConditionalEmbeddedLaw

/-! # The actual induced interval between two tilted closed cuts -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4

noncomputable section

/-- Retain exactly the vertices between the two specified integer columns. -/
def tiltedInterval (n M : ℕ) (t : ℝ) (lo hi : ℤ) : Finset (ℤ × ℤ) := by
  classical
  exact (tiltedWindow n M t).filter (fun z => lo ≤ z.1 ∧ z.1 ≤ hi)

@[simp] theorem mem_tiltedInterval (n M : ℕ) (t : ℝ) (lo hi : ℤ) (z : ℤ × ℤ) :
    z ∈ tiltedInterval n M t lo hi ↔ z ∈ tiltedWindow n M t ∧ lo ≤ z.1 ∧ z.1 ≤ hi := by
  classical
  simp only [tiltedInterval,Finset.mem_filter]

/-- Literal original-vertex inclusion into the outer tilted window. -/
def tiltedIntervalEmbedding (n M : ℕ) (t : ℝ) (lo hi : ℤ) :
    (tiltedInterval n M t lo hi : Set (ℤ × ℤ)) ↪ (tiltedWindow n M t : Set (ℤ × ℤ)) where
  toFun z := ⟨z.val,((mem_tiltedInterval n M t lo hi z.val).mp z.property).1⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun z : (tiltedWindow n M t : Set (ℤ × ℤ)) => z.val) h)

/-- Every original induced edge is retained by the interval inclusion. -/
theorem tiltedInterval_map_le (n M : ℕ) (t : ℝ) (lo hi : ℤ) :
    (squareLattice.induce (tiltedInterval n M t lo hi : Set (ℤ × ℤ))).map
      (tiltedIntervalEmbedding n M t lo hi) ≤
        squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ)) := by
  rw [SimpleGraph.map_le_iff_le_comap]
  intro u v huv
  exact huv

/-- The image consists exactly of the retained column interval. -/
theorem mem_tiltedIntervalEmbedding_range (n M : ℕ) (t : ℝ) (lo hi : ℤ)
    (z : (tiltedWindow n M t : Set (ℤ × ℤ))) :
    z ∈ Set.range (tiltedIntervalEmbedding n M t lo hi) ↔ lo ≤ z.val.1 ∧ z.val.1 ≤ hi := by
  constructor
  · rintro ⟨u,rfl⟩
    exact ((mem_tiltedInterval n M t lo hi u.val).mp u.property).2
  · intro h
    exact ⟨⟨z.val,(mem_tiltedInterval n M t lo hi z.val).mpr ⟨z.property,h⟩⟩,rfl⟩

/-- Intrinsic digital top wiring on the actual induced interval. -/
def tiltedIntervalTopBoundary (n M : ℕ) (t : ℝ) (lo hi : ℤ) :
    PD.FK.BoundaryCondition (tiltedInterval n M t lo hi : Set (ℤ × ℤ)) :=
  PD.FK.BoundaryCondition.wired {z | tiltedTop n t z.val}

/-- Exact partition after a frozen exterior with no open edge incident to
any retained interval vertex. The no-box-boundary premise is geometric. -/
theorem tiltedInterval_frozen_partition_eq_top (n M : ℕ) (t : ℝ) (lo hi : ℤ) (i : Fin 2)
    (A : PD.FK.Configuration (squareLattice.induce (tiltedWindow n M t : Set (ℤ × ℤ))))
    (hinside : ∀ z ∈ tiltedInterval n M t lo hi, z ∉ vertexBoundary (box M))
    (hA : ∀ ⦃e⦄, e ∈ A → ∀ ⦃z : (tiltedWindow n M t : Set (ℤ × ℤ))⦄,
      z ∈ e.val → z ∉ Set.range (tiltedIntervalEmbedding n M t lo hi)) :
    (PD.FK.isolatedExtensionPullbackBoundary (tiltedIntervalEmbedding n M t lo hi)
      (PD.FK.frozenBoundary (tiltedWindowBoundary n M t i) A)).partition =
        (tiltedIntervalTopBoundary n M t lo hi).partition := by
  let f := tiltedIntervalEmbedding n M t lo hi
  let D : Set (tiltedWindow n M t : Set (ℤ × ℤ)) := (Set.range f)ᶜ
  let W : Set (tiltedWindow n M t : Set (ℤ × ℤ)) := {z | tiltedTop n t z.val}
  have hξ : (tiltedWindowBoundary n M t i).boundary ⊆ D ∪ W := by
    intro z hz
    change tiltedTop n t z.val ∨ i = 1 ∧ z.val ∈ vertexBoundary (box M) at hz
    rcases hz with hz | ⟨_,hz⟩
    · exact Or.inr hz
    · left
      rintro ⟨u,hu⟩
      have hmem := u.property
      have heq : u.val = z.val := congrArg Subtype.val hu
      exact hinside z.val (heq ▸ hmem) hz
  have hW : (PD.FK.BoundaryCondition.wired W).partition ≤ (tiltedWindowBoundary n M t i).partition := by
    intro u v huv
    change (u = v ∨ u ∈ W ∧ v ∈ W) at huv
    change u = v ∨ (tiltedTop n t u.val ∨ _) ∧ (tiltedTop n t v.val ∨ _)
    rcases huv with rfl | ⟨hu,hv⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨Or.inl hu,Or.inl hv⟩
  exact pullback_frozen_partition_eq_wired_away f D W (tiltedWindowBoundary n M t i) A hξ hW hA
    (fun u hu => hu ⟨u,rfl⟩)

end

end PottsContinuity.Thm3.Prop4
