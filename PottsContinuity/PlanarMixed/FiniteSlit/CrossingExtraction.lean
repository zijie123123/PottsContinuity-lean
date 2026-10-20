module

public import PottsContinuity.PlanarMixed.FiniteSlit.ClampedDualSample

/-! Finite crossing extraction by removing only fixed slit-internal bonds.
A rectangle dual crossing gives an actual B'-K' path in the sampled reflected
graph. No infinite path, escape statement, or boundary-path premise occurs. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial PD.Duality BD12 DualityExt
noncomputable section
local instance finiteSlitCrossingExtractionEdgeDecidableEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

private theorem embedded_endpoint_in_range
    {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)
    (C : Configuration G) (e : H.edgeSet)
    (he : e ∈ embeddedConfigurationEmbedding G H f hGH C) (z : W) (hz : z ∈ e.val) :
    z ∈ Set.range f := by
  rw [embeddedConfigurationEmbedding_eq_map] at he
  obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp he
  change z ∈ Sym2.map f a.val at hz
  obtain ⟨u,_,hu⟩ := Sym2.mem_map.mp hz
  exact ⟨u,hu⟩

/-- A dual rectangle crossing in a sample plus its fixed slit state contains
an actual marked B'-K' connection in that same sampled reflected configuration. -/
theorem crossing_extract_from_static_slit (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (C : Configuration (dualGraph M x y))
    (hcross : embeddedConfigurationEmbedding (dualGraph M x y)
        (rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M) (cellEmbedding M x hM)
        (dualGraph_map_le_rectangleDual M x y hM) C ∪ (dualExteriorState M x y).val ∈
      rectangleDualBottomTopCrossingEvent (x-(M : ℤ),0) (2*M-1) M) :
    C ∈ arcsConnectionEvent (dualGraph M x y) (dualBottom M x) (dualRay M x y) := by
  let H := rectangleDualGraph (x-(M : ℤ),0) (2*M-1) M
  let D := dualGraph M x y
  let f := cellEmbedding M x hM
  let F := embeddedConfigurationEmbedding D H f (dualGraph_map_le_rectangleDual M x y hM) C
  let K := (dualExteriorState M x y).val
  let A : Set (RectangleDualVertex (x-(M : ℤ),0) (2*M-1) M) := {z | z.val.2 = -1}
  let S : Set (RectangleDualVertex (x-(M : ℤ),0) (2*M-1) M) :=
    {z | z.val.1 = x-1 ∧ y ≤ z.val.2}
  obtain ⟨b,hb,t,ht,hconn⟩ := hcross
  have hbrow : b.val.2 = -1 := by obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb; rfl
  have htrow : t.val.2 = (M : ℤ) := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    simp [rectangleDualTopPortVertex]
  have hbt : b ≠ t := by
    intro h
    have := congrArg (fun z => z.val.2) h
    omega
  have htout : t ∉ Set.range f := by
    rintro ⟨u,rfl⟩
    have hu := (mem_rectangle_iff M x (by omega) u.val).mp u.property
    change u.val.2-1 = (M : ℤ) at htrow
    omega
  have htS : t ∈ S := by
    obtain ⟨z,htz⟩ := hconn.nonempty_neighborSet_right hbt
    obtain ⟨e,he,heq⟩ := (openGraph_adj _ _ _ _).mp htz
    have hte : t ∈ e.val := by rw [heq]; exact (Sym2.mem_iff').mpr (Or.inl rfl)
    rcases Finset.mem_union.mp he with he | he
    · exact (htout (embedded_endpoint_in_range D H f _ C e he t hte)).elim
    · exact dualExteriorState_endpoint_on_slit M x y hM hy hyM e he t hte
  have hAS : Disjoint A S := by
    apply Set.disjoint_left.mpr
    intro z hzA hzS
    change z.val.2 = -1 at hzA
    change z.val.1 = x-1 ∧ y ≤ z.val.2 at hzS
    omega
  have hK : ∀ u v (huv : H.Adj u v), (⟨s(u,v),H.mem_edgeSet.mpr huv⟩ : H.edgeSet) ∈ K →
      (twoBlockBoundary A S hAS).partition.r u v := by
    intro u v huv he
    apply (twoBlockBoundary_partition_rel A S hAS u v).mpr
    apply Or.inr ∘ Or.inr
    constructor
    · exact dualExteriorState_endpoint_on_slit M x y hM hy hyM _ he u
        ((Sym2.mem_iff').mpr (Or.inl rfl))
    · exact dualExteriorState_endpoint_on_slit M x y hM hy hyM _ he v
        ((Sym2.mem_iff').mpr (Or.inr rfl))
  have hclean : F ∈ arcsConnectionEvent H A S :=
    (arcsConnectionEvent_union_removed A S hAS ⟨b,hbrow⟩ ⟨t,htS⟩ K hK F ⟨K,le_rfl⟩).mp
      ⟨b,hbrow,t,htS,hconn⟩
  obtain ⟨u,hu,v,hv,huv⟩ := hclean
  change (openGraph H (subgraphConfigurationEmbedding _
    (isolatedExtensionConfigurationEquiv D f C))).Reachable u v at huv
  rw [openGraph_subgraphConfigurationEmbedding,openGraph_isolatedExtension] at huv
  rcases (reachable_isolatedExtension (openGraph D C) f u v).mp huv with heq | ⟨p,q,hpq,hp,hq⟩
  · change u.val.2 = -1 at hu
    change v.val.1 = x-1 ∧ y ≤ v.val.2 at hv
    have := congrArg (fun z => z.val.2) heq
    omega
  · have hp0 : p.val.2 = 0 := by
      have h := congrArg (fun z => z.val.2) hp
      change p.val.2-1 = u.val.2 at h
      change u.val.2 = -1 at hu
      omega
    have hqK : q ∈ dualRay M x y := by
      change q.val.1 = x ∧ y+1 ≤ q.val.2
      have hx := congrArg (fun z => z.val.1) hq
      have hk := congrArg (fun z => z.val.2) hq
      change 2*x-1-q.val.1 = v.val.1 at hx
      change q.val.2-1 = v.val.2 at hk
      change v.val.1 = x-1 ∧ y ≤ v.val.2 at hv
      constructor <;> omega
    have hpqne : p ≠ q := by
      intro h
      have he := congrArg (fun z => z.val.2) h
      change q.val.1 = x ∧ y+1 ≤ q.val.2 at hqK
      omega
    obtain ⟨w,hpw⟩ := hpq.nonempty_neighborSet_left hpqne
    have hbound := (dualGraph_adj_boundary_bounds M x y hM p w (openGraph_le D C hpw)).1
    have hpB : p ∈ dualBottom M x := by
      change p.val.2 = 0 ∧ x-(M : ℤ)+1 ≤ p.val.1 ∧ p.val.1 ≤ x-1
      exact ⟨hp0,by omega,hbound.2 hp0⟩
    exact ⟨p,hpB,q,hqK,hpq⟩

/-- One-way finite four-arc existence, on the canonical sample and exact
finite reflected carrier. This is the geometric input to the uniform bound. -/
theorem dual_crossing_exists_of_nonconnection (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (hy : 0 < y) (hyM : y < (M : ℤ))
    (C : Configuration (graph M x y)) (hC : C ∉ connectionEvent M x y) :
    dualConfiguration M x y C ∈
      arcsConnectionEvent (dualGraph M x y) (dualBottom M x) (dualRay M x y) := by
  apply crossing_extract_from_static_slit M x y hM hy hyM
  have h := hostAugmentation_dual_crossing_of_nonconnection M x y hM hy hyM C hC
  rw [augmented_dual_decomposition M x y hM hy hyM C] at h
  exact h

end
end PottsContinuity.PlanarMixed.FiniteSlit
