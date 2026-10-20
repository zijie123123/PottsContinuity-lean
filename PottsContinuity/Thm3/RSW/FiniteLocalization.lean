module

public import PottsContinuity.Thm3.RSW.ClusterLocalization
public import PottsContinuity.Thm3.RSW.FiniteClusterCover

/-!
# Localization on the frozen Boolean carrier

The bounding square may extend beyond the ambient finite domain. We first
localize to its intersection with that domain, then compare the free induced
law to the law on the full square. All connections below are actual paths.
-/

@[expose] public section

namespace PottsContinuity.RSW
open PD.FK
noncomputable section

/-- Actual connection on the Boolean carrier agrees with actual connection on
its finite open-edge carrier, with the prescribed endpoint memberships. -/
theorem finiteConnectionEvent_bool_iff (V : Finset (ℤ × ℤ)) (x y : ℤ × ℤ)
    (hx : x ∈ V) (hy : y ∈ V)
    (A : Configuration (squareLattice.induce (V : Set (ℤ × ℤ)))) :
    (boolConfigurationEquiv _).symm A ∈ finiteConnectionEvent V x y ↔
      ActualConnected (squareLattice.induce (V : Set (ℤ × ℤ))) A ⟨x, hx⟩ ⟨y, hy⟩ := by
  have hg : rcOpenGraph V ((boolConfigurationEquiv _).symm A) =
      openGraph (squareLattice.induce (V : Set (ℤ × ℤ))) A := by
    have h := rcOpenGraph_eq V ((boolConfigurationEquiv _).symm A)
    change openGraph (squareLattice.induce (V : Set (ℤ × ℤ)))
      ((boolConfigurationEquiv _) ((boolConfigurationEquiv _).symm A)) =
      rcOpenGraph V ((boolConfigurationEquiv _).symm A) at h
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  change (∃ hx' : x ∈ V, ∃ hy' : y ∈ V,
    (rcOpenGraph V _).Reachable ⟨x, hx'⟩ ⟨y, hy'⟩) ↔ _
  rw [hg]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hx, hy, h⟩⟩

/-- Connection together with confinement of the whole actual cluster in S. -/
def finiteConfinedConnectionEvent (V S : Finset (ℤ × ℤ)) (x y : ℤ × ℤ) :
    Set ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :=
  {ω | ω ∈ finiteConnectionEvent V x y ∧
    ∀ z, ω ∈ finiteConnectionEvent V x z → z ∈ S}

/-- Exact conversion of cluster confinement to the finite open-edge carrier. -/
theorem finiteBoolEvent_confinedConnection (V S : Finset (ℤ × ℤ)) (x y : ℤ × ℤ)
    (hx : x ∈ V) (hy : y ∈ V) :
    finiteBoolEvent V (fun ω => ω ∈ finiteConfinedConnectionEvent V S x y) =
      confinedConnectionEvent (squareLattice.induce (V : Set (ℤ × ℤ)))
        {v | v.val ∈ S} ⟨x, hx⟩ ⟨y, hy⟩ := by
  ext A
  change ((_ ∈ finiteConnectionEvent V x y) ∧ _) ↔ _
  rw [finiteConnectionEvent_bool_iff V x y hx hy A]
  constructor
  · rintro ⟨hconn, hconf⟩
    refine ⟨hconn, fun z hz => ?_⟩
    exact hconf z.val ((finiteConnectionEvent_bool_iff V x z.val hx z.property A).mpr hz)
  · rintro ⟨hconn, hconf⟩
    refine ⟨hconn, fun z hz => ?_⟩
    obtain ⟨_, hzV, hzconn⟩ := hz
    exact hconf ⟨z, hzV⟩ ((finiteConnectionEvent_bool_iff V x z hx hzV A).mp
      ⟨hx, hzV, hzconn⟩)

/-- The free localization inequality for arbitrary finite lattice regions,
including squares touching or extending beyond the ambient boundary. -/
theorem finite_free_confinedConnection_probability_le (θ : Parameters)
    (V S : Finset (ℤ × ℤ)) (x y : ℤ × ℤ)
    (hxV : x ∈ V) (hyV : y ∈ V) (hxS : x ∈ S) (hyS : y ∈ S) :
    finiteBoundaryEventProbability V θ (frozenBoundaryCondition V 0)
      (fun ω => ω ∈ finiteConfinedConnectionEvent V S x y) ≤
    finiteBoundaryEventProbability S θ (frozenBoundaryCondition S 0)
      (fun ω => ω ∈ finiteConnectionEvent S x y) := by
  classical
  let G := squareLattice.induce (V : Set (ℤ × ℤ))
  let H := squareLattice.induce (S : Set (ℤ × ℤ))
  let W : Set (V : Set (ℤ × ℤ)) := {v | v.val ∈ S}
  let xW : W := ⟨⟨x, hxV⟩, hxS⟩
  let yW : W := ⟨⟨y, hyV⟩, hyS⟩
  let f : W ↪ (S : Set (ℤ × ℤ)) :=
    ⟨fun v => ⟨v.val.val, v.property⟩,
      fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z => z.val) h))⟩
  have hmap : (G.induce W).map f ≤ H := by
    intro a b hab
    obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj f _ a b).mp hab
    exact huv
  have hlocal := free_confinedConnection_probability_le (G := G) θ W xW yW
  have hcomp := embedded_free_connection_probability_le_allq f hmap θ xW yW
  have hV : law G θ (frozenBoundaryCondition V 0) = law G θ (BoundaryCondition.free ∅) :=
    law_eq_of_boundary_partition_eq θ _ _ (by simp [frozenBoundaryCondition, BoundaryCondition.free])
  have hS : law H θ (frozenBoundaryCondition S 0) = law H θ (BoundaryCondition.free ∅) :=
    law_eq_of_boundary_partition_eq θ _ _ (by simp [frozenBoundaryCondition, BoundaryCondition.free])
  have hpair : finiteBoolEvent S (fun ω => ω ∈ finiteConnectionEvent S x y) =
      {A | ActualConnected H A ⟨x, hxS⟩ ⟨y, hyS⟩} := by
    ext A
    exact finiteConnectionEvent_bool_iff S x y hxS hyS A
  unfold finiteBoundaryEventProbability
  rw [finiteBoolEvent_confinedConnection V S x y hxV hyV, hpair]
  unfold PD.FK.measure
  rw [hV, hS]
  exact hlocal.trans hcomp

end
end PottsContinuity.RSW
