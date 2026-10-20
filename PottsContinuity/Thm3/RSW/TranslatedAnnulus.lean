module

public import PottsContinuity.Thm3.RSW.FiniteRestriction
public import PottsContinuity.Thm3.RSW.AnnulusCircuit

/-!
# Sampled annulus events in translated local windows

A local event reads literal ambient edge states on a translated copy of box(8m).
The enclosing circuit is the genuine source polygon event under that relabeling.
The explicit containment premise constructs an actual embedding; no outside
window state or exceptional case is supplied by a default value.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- Translate every local vertex into the ambient finite sampled domain. -/
def translatedWindowVertexEmbedding (U V : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hwindow : ∀ z ∈ U, (z.1+c.1,z.2+c.2) ∈ V) :
    (U:Set (ℤ × ℤ)) ↪ (V:Set (ℤ × ℤ)) where
  toFun := fun v => ⟨(v.val.1+c.1,v.val.2+c.2),hwindow v.val v.property⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    have hv := congrArg (fun z : (V:Set (ℤ × ℤ)) => z.val) h
    change (u.val.1+c.1,u.val.2+c.2) = (v.val.1+c.1,v.val.2+c.2) at hv
    exact Prod.ext (add_right_cancel (congrArg Prod.fst hv))
      (add_right_cancel (congrArg Prod.snd hv))

/-- Every translated original edge is an actual ambient lattice edge. -/
theorem translatedWindow_graph_le (U V : Finset (ℤ × ℤ)) (c : ℤ × ℤ)
    (hwindow : ∀ z ∈ U, (z.1+c.1,z.2+c.2) ∈ V) :
    (squareLattice.induce (U:Set (ℤ × ℤ))).map
      (translatedWindowVertexEmbedding U V c hwindow) ≤
        squareLattice.induce (V:Set (ℤ × ℤ)) := by
  intro x y hxy
  obtain ⟨u,v,huv,rfl,rfl⟩ := (SimpleGraph.map_adj _ _ x y).mp hxy
  change |(u.val.1+c.1)-(v.val.1+c.1)|+|(u.val.2+c.2)-(v.val.2+c.2)|=1
  have hx : (u.val.1+c.1)-(v.val.1+c.1) = u.val.1-v.val.1 := by ring
  have hy : (u.val.2+c.2)-(v.val.2+c.2) = u.val.2-v.val.2 := by ring
  rw [hx,hy]
  exact huv

/-- The genuine local annulus circuit, sampled by original-edge restriction
from its translated finite window in V. -/
def translatedAnnulusEvent (V : Finset (ℤ × ℤ)) (m : ℕ) (c : ℤ × ℤ)
    (hwindow : ∀ z ∈ box (8*m), (z.1+c.1,z.2+c.2) ∈ V) :
    Set ((squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) :=
  {ω | finiteBoolRestriction (box (8*m)) V
      (translatedWindowVertexEmbedding (box (8*m)) V c hwindow)
      (translatedWindow_graph_le (box (8*m)) V c hwindow) ω ∈
        annulusCircuitEvent (box (8*m)) (0,0) m}

/-- The sampled local annulus event is increasing in all ambient edge states. -/
theorem translatedAnnulusEvent_isUpperSet (V : Finset (ℤ × ℤ)) (m : ℕ) (c : ℤ × ℤ)
    (hwindow : ∀ z ∈ box (8*m), (z.1+c.1,z.2+c.2) ∈ V) :
    IsUpperSet (translatedAnnulusEvent V m c hwindow) := by
  let R := finiteBoolRestriction (box (8*m)) V
    (translatedWindowVertexEmbedding (box (8*m)) V c hwindow)
    (translatedWindow_graph_le (box (8*m)) V c hwindow)
  let E : Set ((squareLattice.induce (box (8*m):Set (ℤ × ℤ))).edgeSet → Bool) :=
    annulusCircuitEvent (box (8*m)) (0,0) m
  have hR : Monotone R := finiteBoolRestriction_monotone _ _ _ _
  have hE : IsUpperSet E := annulusCircuitEvent_isUpperSet _ _ _
  change IsUpperSet (R ⁻¹' E)
  exact hE.preimage hR

/-- The actual small free annulus probability is a lower bound in the common
ambient free law. The only premise is deterministic window containment. -/
theorem annulusProbability_le_translatedAnnulusProbability
    (θ : Parameters) (V : Finset (ℤ × ℤ)) (m : ℕ) (c : ℤ × ℤ)
    (hwindow : ∀ z ∈ box (8*m), (z.1+c.1,z.2+c.2) ∈ V) :
    annulusProbability θ 8 m ≤
      finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
        (fun ω => ω ∈ translatedAnnulusEvent V m c hwindow) :=
  finite_free_restriction_probability_le (box (8*m)) V
    (translatedWindowVertexEmbedding (box (8*m)) V c hwindow)
    (translatedWindow_graph_le (box (8*m)) V c hwindow) θ
    (fun ω => ω ∈ annulusCircuitEvent (box (8*m)) (0,0) m)
    (annulusCircuitEvent_isUpperSet (box (8*m)) (0,0) m)

end
end PottsContinuity.RSW
