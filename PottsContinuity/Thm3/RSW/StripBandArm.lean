module

public import PottsContinuity.Thm3.RSW.ThreeSideWalkExit

@[expose] public section

namespace PottsContinuity.RSW

/-- A bottom interval reaches the top height by an actual sampled walk whose
entire trace stays in the stated closed height band. -/
def stripBandArm (n : ℕ) (H a b : ℤ) : Set (StripConfiguration n) :=
  {ω | ∃ u v : stripVertices n, ∃ p : (stripOpenGraph n ω).Walk u v,
    a ≤ u.val.1 ∧ u.val.1 ≤ b ∧ u.val.2 = 0 ∧ v.val.2 = H ∧
      ∀ z ∈ p.support, 0 ≤ z.val.2 ∧ z.val.2 ≤ H}

/-- The literal arm from a bottom interval to B inside a finite rectangle. -/
def stripRectangleArm (n : ℕ) (l r H a b : ℤ) (B : Set (stripVertices n)) :
    Set (StripConfiguration n) :=
  stripConfinedConnection n (stripRectangleVertices n l r 0 H)
    {u | a ≤ u.val.1 ∧ u.val.1 ≤ b ∧ u.val.2 = 0} B

/-- The band-confined arm is exactly an increasing union of finite-window
confined arm events, with every original sampled bond retained. -/
theorem stripBandArm_eq_iUnion_rectangleArm (n : ℕ) (H a b : ℤ) :
    stripBandArm n H a b = ⋃ m : ℕ,
      stripRectangleArm n (-(m:ℤ)) m H a b {v | v.val.2 = H} := by
  classical
  ext ω
  constructor
  · rintro ⟨u,v,p,ha,hb,hu,hv,hp⟩
    let m := p.support.toFinset.sup (fun z => z.val.1.natAbs)
    apply Set.mem_iUnion.mpr
    refine ⟨m,u,v,p,⟨ha,hb,hu⟩,hv,?_⟩
    intro z hz
    have hzm : z.val.1.natAbs ≤ m := Finset.le_sup (f := fun z => z.val.1.natAbs)
      (List.mem_toFinset.mpr hz)
    have habs : |z.val.1| ≤ (m:ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hzm
    have hpz := hp z hz
    simp only [stripRectangleVertices, Finset.mem_preimage,
      latticeRectangle, Finset.mem_product, Finset.mem_Icc]
    exact ⟨abs_le.mp habs,hpz⟩
  · intro h
    obtain ⟨m,u,v,p,hu,hv,hp⟩ := Set.mem_iUnion.mp h
    refine ⟨u,v,p,hu.1,hu.2.1,hu.2.2,hv,?_⟩
    intro z hz
    have h := hp z hz
    simp only [stripRectangleVertices, Finset.mem_preimage,
      latticeRectangle, Finset.mem_product, Finset.mem_Icc] at h
    exact h.2

/-- The corrected height-confined source arm is measurable. -/
theorem stripBandArm_measurableSet (n : ℕ) (H a b : ℤ) :
    MeasurableSet (stripBandArm n H a b) := by
  rw [stripBandArm_eq_iUnion_rectangleArm]
  apply MeasurableSet.iUnion
  intro m
  exact (stripConfinedConnection_isClopen n _ _ _).isOpen.measurableSet

end PottsContinuity.RSW
