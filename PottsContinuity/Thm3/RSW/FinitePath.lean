module

public import PottsContinuity.Thm3.RSW.EmbeddedPath
public import PottsContinuity.Thm3.RSW.PairReflection

/-! Actual paths confined to a prescribed finite region, without confining
an entire cluster. These are the local events for reflected corridor chains. -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK
noncomputable section

/-- An actual open path between the endpoints whose every vertex lies in S.
The ambient sampled graph is induced by V; S may be any finite lattice set. -/
def finitePathEvent (V S : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    Set ((squareLattice.induce (V:Set (ℤ × ℤ))).edgeSet → Bool) :=
  {ω | ∃ hx : x ∈ V, ∃ hy : y ∈ V,
    ∃ w : (rcOpenGraph V ω).Walk ⟨x,hx⟩ ⟨y,hy⟩,
      ∀ v ∈ w.support, v.val ∈ S}

/-- Adding sampled open edges preserves the same confined path. -/
theorem finitePathEvent_isUpperSet (V S : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    IsUpperSet (finitePathEvent V S x y) := by
  rintro ω η h ⟨hx,hy,w,hw⟩
  refine ⟨hx,hy,w.mapLe (rcOpenGraph_mono V h), ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
  exact hw v hv

/-- Forgetting confinement gives the original actual connection event. -/
theorem finitePathEvent_subset_connection (V S : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    finitePathEvent V S x y ⊆ finiteConnectionEvent V x y := by
  rintro ω ⟨hx,hy,w,_⟩
  exact ⟨hx,hy,⟨w⟩⟩

/-- The Boolean open graph is exactly the finite-edge open graph after
transport back from the finite-set configuration carrier. -/
theorem rcOpenGraph_boolConfigurationEquiv_symm (V : Finset (ℤ × ℤ))
    (A : Configuration (squareLattice.induce (V:Set (ℤ × ℤ)))) :
    rcOpenGraph V ((boolConfigurationEquiv _).symm A) =
      openGraph (squareLattice.induce (V:Set (ℤ × ℤ))) A := by
  have h := rcOpenGraph_eq V ((boolConfigurationEquiv _).symm A)
  change openGraph _ ((boolConfigurationEquiv _) ((boolConfigurationEquiv _).symm A)) =
    rcOpenGraph V ((boolConfigurationEquiv _).symm A) at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- An embedded small free connection gives an ambient path confined to the
image of its vertices. All exterior states are allowed; there is no cluster
confinement or boundary-separation premise. -/
theorem embedded_free_connection_le_finitePathProbability
    {X : Type*} [Finite X] (G : SimpleGraph X)
    (V S : Finset (ℤ × ℤ)) (θ : Parameters)
    (f : X ↪ (V:Set (ℤ × ℤ)))
    (hGV : G.map f ≤ squareLattice.induce (V:Set (ℤ × ℤ)))
    (himage : ∀ v : X, (f v).val ∈ S) (x y : X) :
    (measure G θ (BoundaryCondition.free ∅) {A | ActualConnected G A x y}).toReal ≤
      finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
        (fun ω => ω ∈ finitePathEvent V S (f x).val (f y).val) := by
  let H := squareLattice.induce (V:Set (ℤ × ℤ))
  let E : Set (Configuration G) := {A | ActualConnected G A x y}
  let T := finiteBoolEvent V (fun ω => ω ∈ finitePathEvent V S (f x).val (f y).val)
  have hcomp := embedded_free_probability_le G H f hGV θ E
    (fun _ _ h hA => actualConnected_mono h hA)
  have hsub : {A | embeddedConfigurationRestriction G H f hGV A ∈ E} ⊆ T := by
    intro A hA
    obtain ⟨w,hw⟩ := embedded_restriction_confined_path G H f hGV A x y hA
    change (boolConfigurationEquiv _).symm A ∈ finitePathEvent V S (f x).val (f y).val
    change ∃ hx : (f x).val ∈ V, ∃ hy : (f y).val ∈ V,
      ∃ p : (rcOpenGraph V ((boolConfigurationEquiv _).symm A)).Walk
        ⟨(f x).val,hx⟩ ⟨(f y).val,hy⟩, ∀ v ∈ p.support, v.val ∈ S
    rw [rcOpenGraph_boolConfigurationEquiv_symm]
    refine ⟨(f x).property,(f y).property,w,?_⟩
    intro v hv
    obtain ⟨z,hz⟩ := hw v hv
    rw [← hz]
    exact himage z
  have hprob := hcomp.trans (measureReal_mono (μ := measure H θ (BoundaryCondition.free ∅)) hsub)
  have hlaw := law_eq_of_boundary_partition_eq (G := H) θ (BoundaryCondition.free (∅ : Set (V:Set (ℤ × ℤ))))
    (frozenBoundaryCondition V 0) (by simp [frozenBoundaryCondition,BoundaryCondition.free])
  change (measure G θ (BoundaryCondition.free ∅) E).toReal ≤ (measure H θ _ T).toReal
  unfold PD.FK.measure at hprob ⊢
  rw [hlaw] at hprob
  exact hprob

end
end PottsContinuity.RSW
