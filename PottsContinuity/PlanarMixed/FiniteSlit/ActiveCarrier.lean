module

public import PottsContinuity.PlanarMixed.FiniteSlit.Corners

/-! The finite active carrier after alpha/beta prewiring. Its corrected
reflected crossing bonds stay in the same balanced box and slit graph. -/

@[expose] public section

namespace PottsContinuity.PlanarMixed.FiniteSlit
open PD.FK PD.FK.Medial BD12
noncomputable section

/-- An actual source bond internal to one of the two separate wired arcs. -/
def boundaryInternal (M : ℕ) (x y : ℤ) (b : LatticeBond) : Prop :=
  ∃ hs : b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M,
    ∃ ht : b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M,
      ((⟨b.source,hs⟩ ∈ alpha M x ∧ ⟨b.target,ht⟩ ∈ alpha M x) ∨
       (⟨b.source,hs⟩ ∈ beta M x y ∧ ⟨b.target,ht⟩ ∈ beta M x y))

/-- Every sampled finite slit bond except boundary-internal alpha/beta bonds. -/
def ActiveBond (M : ℕ) (x y : ℤ) (b : LatticeBond) : Prop :=
  b.source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M ∧
  b.target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M ∧
  SlitRetainedBond x y b ∧ ¬ boundaryInternal M x y b

/-- Finite outer prewiring includes all boundary-internal bonds of the
original two marked arcs. Thus the earlier global active-carrier inclusion applies. -/
theorem activeBond_global_active (M : ℕ) (x y : ℤ) (b : LatticeBond)
    (hb : ActiveBond M x y b) : SlitActiveBond x y b := by
  obtain ⟨hs,ht,hret,hnot⟩ := hb
  refine ⟨hret,?_⟩
  intro hp
  apply hnot
  refine ⟨hs,ht,?_⟩
  rcases b with ⟨⟨a,k⟩,ax⟩
  cases ax <;>
    simp [SlitPrewiredBond,alpha,beta,LatticeBond.source,LatticeBond.target] at hp ⊢ <;> omega

/-- Corrected reflection retains every active finite source bond in D. -/
theorem activeBond_reflection_retained (M : ℕ) (x y : ℤ) (b : LatticeBond)
    (hb : ActiveBond M x y b) : SlitRetainedBond x y (slitReflectedBond x b) := by
  apply slitReflectedActiveBond_subset_retained x y
  change SlitActiveBond x y (slitReflectedBondInv x (slitReflectedBond x b))
  rw [slitReflectedBondInv_apply]
  exact activeBond_global_active M x y b hb

/-- The top and outer-side prewiring removes exactly the potential escaping
reflected endpoints. Every active image lies in the SAME balanced finite box. -/
theorem activeBond_reflected_endpoints_mem (M : ℕ) (x y : ℤ)
    (hM : 2 ≤ M) (_hy : 0 < y) (hyM : y < (M : ℤ))
    (b : LatticeBond) (hb : ActiveBond M x y b) :
    (slitReflectedBond x b).source ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M ∧
    (slitReflectedBond x b).target ∈ PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M := by
  obtain ⟨hs,ht,hret,hnot⟩ := hb
  have hsb := (mem_rectangle_iff M x (by omega) b.source).mp hs
  have htb := (mem_rectangle_iff M x (by omega) b.target).mp ht
  rcases b with ⟨⟨a,k⟩,ax⟩
  cases ax
  · simp only [LatticeBond.source,LatticeBond.target] at hsb htb
    have htop : k ≠ (M : ℤ) := by
      intro hk
      apply hnot
      refine ⟨hs,ht,?_⟩
      have havoid : a ≠ x-1 := by
        have hr := hret.2
        simp only at hr
        simp only [SlitRetainedBond] at hret
        simp_all
      simp only [alpha,beta,Set.mem_ofPred_eq,LatticeBond.source,LatticeBond.target,
        ]
      omega
    constructor
    all_goals
      apply (mem_rectangle_iff M x (by omega) _).mpr
      simp only [slitReflectedBond,LatticeBond.source,LatticeBond.target]
      omega
  · simp only [LatticeBond.source,LatticeBond.target] at hsb htb
    have hleft : a ≠ x-(M : ℤ) := by
      intro ha
      apply hnot
      refine ⟨hs,ht,Or.inl ⟨?_,?_⟩⟩
      all_goals simp [alpha,LatticeBond.source,LatticeBond.target,ha]
    constructor
    all_goals
      apply (mem_rectangle_iff M x (by omega) _).mpr
      simp only [slitReflectedBond,LatticeBond.source,LatticeBond.target]
      omega

/-- Literal reflected active bonds, restricted to the original finite vertex
carrier. Under the finite regime every active image is included by the preceding lemma. -/
def dualGraph (M : ℕ) (x y : ℤ) : SimpleGraph (Vertex M x) :=
  (SimpleGraph.fromEdgeSet {s | ∃ b : LatticeBond,
    ActiveBond M x y b ∧ (slitReflectedBond x b).toSym2 = s}).induce
      (PD.FK.latticeRectangle (x-(M : ℤ),0) (2*M-1) M : Set LatticeVertex)

/-- The actual finite retained graph is the induced global retained graph. -/
theorem graph_adj_iff_retained (M : ℕ) (x y : ℤ) (u v : Vertex M x) :
    (graph M x y).Adj u v ↔ (slitRetainedBondGraph x y).Adj u.val v.val := by
  rw [slitRetainedBondGraph_adj_iff]
  have hu := ((PD.FK.mem_latticeRectangle _ u.val _ _).mp u.property).2.1
  have hv := ((PD.FK.mem_latticeRectangle _ v.val _ _).mp v.property).2.1
  change (_ ∧ _) ↔ (_ ∧ _ ∧ _ ∧ _)
  tauto

/-- The corrected reflected active graph is a genuine subgraph of D_M,
with its entire original vertex carrier retained. -/
theorem dualGraph_le_graph (M : ℕ) (x y : ℤ) : dualGraph M x y ≤ graph M x y := by
  intro u v h
  obtain ⟨⟨b,hb,hpair⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
  apply (graph_adj_iff_retained M x y u v).mpr
  apply (SimpleGraph.fromEdgeSet_adj _).mpr
  exact ⟨⟨slitReflectedBond x b,activeBond_reflection_retained M x y b hb,hpair⟩,hne⟩

end
end PottsContinuity.PlanarMixed.FiniteSlit
