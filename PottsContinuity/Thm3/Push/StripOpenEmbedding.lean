module

public import PottsContinuity.Thm3.Push.ShiftedStripGeometry
public import PottsContinuity.Thm3.Push.OpenStateEmbedding

@[expose] public section

namespace PottsContinuity.Push
open PottsContinuity.RSW PottsContinuity.PD.FK
noncomputable section

/-- Original strip bonds in a finite window retain their sampled states.
Adapted from the private lemma stripWindowPlaneConfiguration_at in
Thm3/RSW/StripLimit.lean, with no mathematical change. -/
theorem stripWindowPlaneConfiguration_on_edge (s M : ℕ)
    (C : Configuration (PottsContinuity.squareLattice.induce
      (stripWindow s M : Set (ℤ × ℤ))))
    (e : (PottsContinuity.squareLattice.induce
      (stripWindow s M : Set (ℤ × ℤ))).edgeSet) :
    stripWindowPlaneConfiguration s M C ((stripWindowPlaneEmbedding s M).mapEdgeSet e) =
      (boolConfigurationEquiv _).symm C e := by
  classical
  simp only [stripWindowPlaneConfiguration, boolConfigurationEquiv,
    Equiv.coe_fn_symm_mk, decide_eq_decide]
  exact Finset.mem_map' (stripWindowPlaneEmbedding s M).mapEdgeSet

/-- The exact translated base rectangle is an induced subgraph of the strip. -/
def baseStripEmbedding (k : ℝ) (s : ℕ) :
    (PottsContinuity.squareLattice.induce
      (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ))) ↪g stripGraph s where
  toFun v := ⟨(v.val.1, v.val.2-s), by
    have hv := (mem_topWiredRectangle_iff k (4/3) (3*s) v.val).mp v.property
    rw [floor_four_thirds_mul_three] at hv
    change -(s : ℤ) ≤ v.val.2 - s ∧ v.val.2 - s ≤ 3*s
    push_cast at hv
    omega⟩
  inj' := by
    intro u v h
    have hc := congrArg (fun z : stripVertices s => z.val) h
    apply Subtype.ext
    simp only [Prod.mk.injEq] at hc
    exact Prod.ext hc.1 (by omega)
  map_rel_iff' := by
    intro u v
    change (|u.val.1-v.val.1| + |(u.val.2-s)-(v.val.2-s)| = 1) ↔
      (|u.val.1-v.val.1| + |u.val.2-v.val.2| = 1)
    have heq : (u.val.2-(s : ℤ))-(v.val.2-s) = u.val.2-v.val.2 := by ring
    rw [heq]

theorem baseStripEmbedding_edge_state (k : ℝ) (s M : ℕ)
    (hM : ⌊k*(3*s : ℕ)⌋ ≤ (M : ℤ))
    (C : Configuration (PottsContinuity.squareLattice.induce
      (stripWindow s M : Set (ℤ × ℤ))))
    (e : (PottsContinuity.squareLattice.induce
      (topWiredRectangle k (4/3) (3*s) : Set (ℤ × ℤ))).edgeSet) :
    (boolConfigurationEquiv _).symm
      (embeddedConfigurationRestriction _ _ (baseStripWindowEmbedding k s M hM)
        (baseStripWindowEmbedding_map_le k s M hM) C) e =
    stripPlaneRestriction s (stripWindowPlaneConfiguration s M C)
      ((baseStripEmbedding k s).mapEdgeSet e) := by
  rw [bool_embeddedRestriction_state]
  have heq : (stripPlaneEmbedding s).mapEdgeSet ((baseStripEmbedding k s).mapEdgeSet e) =
      (stripWindowPlaneEmbedding s M).mapEdgeSet
        (embeddedEdgeEmbedding _ _ (baseStripWindowEmbedding k s M hM)
          (baseStripWindowEmbedding_map_le k s M hM) e) := by
    apply Subtype.ext
    change Sym2.map _ (Sym2.map _ e.val) = Sym2.map _ (Sym2.map _ e.val)
    rw [Sym2.map_map, Sym2.map_map]
    rfl
  change _ = stripWindowPlaneConfiguration s M C _
  rw [heq, stripWindowPlaneConfiguration_on_edge]

end
end PottsContinuity.Push
