module

public import PottsContinuity.DualityExt.PositiveDomainMarkov
public import PottsContinuity.PD.FK.ComponentMerge
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.CompletePartialOrder

/-!
# Exact positive-`q` reweighting when two wired boundary classes are merged

The annular transfer compares separately wired inner and outer classes with
the boundary condition that wires their union. The latter law has weight
`q⁻¹` on configurations whose open clusters do not already join the classes.
-/

@[expose] public section

namespace PottsContinuity.DualityExt

open PottsContinuity.PD.FK
open PottsContinuity.PD.FK.FiniteProbability

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance positiveMergeEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance positiveMergeEdgeDecidableEq : DecidableEq G.edgeSet :=
  positiveDMPEdgeDecidableEq
local instance positiveMergeConfigFintype : Fintype (Configuration G) := Fintype.ofFinite _

/-- Add the identification of two chosen vertices to a boundary condition. -/
def positiveBoundaryMerge (ξ : BoundaryCondition V) (u v : V) :
    BoundaryCondition V where
  boundary := ξ.boundary ∪ {u, v}
  partition := ξ.partition ⊔ (BoundaryCondition.wired ({u, v} : Set V)).partition
  supported := by
    intro x y h
    let S : Setoid V := {
      r := fun x y => x = y ∨
        x ∈ ξ.boundary ∪ {u, v} ∧ y ∈ ξ.boundary ∪ {u, v}
      iseqv := by
        refine ⟨?_, ?_, ?_⟩
        · intro x
          exact Or.inl rfl
        · intro x y h
          rcases h with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨h.2, h.1⟩
        · intro x y z hxy hyz
          rcases hxy with hxy | hxy
          · subst y
            exact hyz
          · rcases hyz with hyz | hyz
            · subst z
              exact Or.inr hxy
            · exact Or.inr ⟨hxy.1, hyz.2⟩ }
    have hle : ξ.partition ⊔
        (BoundaryCondition.wired ({u, v} : Set V)).partition ≤ S := by
      apply sup_le
      · intro x y hxy
        rcases ξ.supported hxy with heq | hbd
        · exact Or.inl heq
        · exact Or.inr ⟨Or.inl hbd.1, Or.inl hbd.2⟩
      · intro x y hxy
        rcases (BoundaryCondition.wired_rel ({u, v} : Set V) x y).mp hxy with heq | hpair
        · exact Or.inl heq
        · exact Or.inr ⟨Or.inr hpair.1, Or.inr hpair.2⟩
    exact hle h

omit [Finite V] in
@[simp] theorem componentSetoid_positiveBoundaryMerge (ξ : BoundaryCondition V)
    (A : Configuration G) (u v : V) :
    componentSetoid G (positiveBoundaryMerge ξ u v) A =
      componentSetoid G ξ A ⊔ (BoundaryCondition.wired ({u, v} : Set V)).partition := by
  simp [componentSetoid, positiveBoundaryMerge, sup_assoc]

noncomputable def positiveBoundaryConditionOfSetoid (s : Setoid V) :
    BoundaryCondition V where
  boundary := Set.univ
  partition := s
  supported := by
    intro x y h
    exact Or.inr ⟨Set.mem_univ _, Set.mem_univ _⟩

omit [Finite V] in
private theorem positive_openGraph_singleEdge_reachableSetoid_eq_wired
    {u v : V} (hne : u ≠ v) :
    (openGraph (⊤ : SimpleGraph V)
      ({⟨s(u,v), by simp [hne]⟩} : Configuration (⊤ : SimpleGraph V))).reachableSetoid =
      (BoundaryCondition.wired ({u,v} : Set V)).partition := by
  classical
  let H : SimpleGraph V := ⊤
  let e : H.edgeSet := ⟨s(u,v), by simp [H, hne]⟩
  have huv : (openGraph H {e}).Reachable u v := by
    apply actualConnected_of_adj
    rw [openGraph_adj]
    exact ⟨e, by simp, rfl⟩
  have hvu : (openGraph H {e}).Reachable v u := huv.symm
  change (openGraph H ({e} : Configuration H)).reachableSetoid = _
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    apply reachableSetoid_le_of_adj (openGraph H {e})
      (BoundaryCondition.wired ({u,v} : Set V)).partition
    · intro a b hab
      rw [openGraph_adj] at hab
      rcases hab with ⟨f, hf, hab⟩
      have hfe : f = e := by simpa using hf
      subst f
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (BoundaryCondition.wired_rel ({u,v} : Set V) u v).2
          (Or.inr ⟨by simp, by simp⟩)
      · exact (BoundaryCondition.wired_rel ({u,v} : Set V) v u).2
          (Or.inr ⟨by simp, by simp⟩)
    · exact h
  · intro h
    rcases (BoundaryCondition.wired_rel ({u,v} : Set V) x y).mp h with hxy | hxy
    · subst y
      exact SimpleGraph.Reachable.refl _
    · have hx : x = u ∨ x = v := by simpa using hxy.1
      have hy : y = u ∨ y = v := by simpa using hxy.2
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact SimpleGraph.Reachable.refl _
      · exact huv
      · exact hvu
      · exact SimpleGraph.Reachable.refl _

private theorem positive_componentCount_join_wiredPair_eq_of_related
    (s : Setoid V) {u v : V} (hne : u ≠ v) (hrel : s.r u v) :
    Nat.card (Quotient (s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition)) =
      Nat.card (Quotient s) := by
  classical
  let H : SimpleGraph V := ⊤
  have huv : H.Adj u v := by simp [H, hne]
  let ξ := positiveBoundaryConditionOfSetoid s
  let e : H.edgeSet := ⟨s(u,v), H.mem_edgeSet.mpr huv⟩
  have hzero : componentSetoid H ξ (∅ : Configuration H) = s := by
    simp [componentSetoid_empty, ξ, positiveBoundaryConditionOfSetoid]
  have hone : componentSetoid H ξ ({e} : Configuration H) =
      s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition := by
    rw [componentSetoid, positive_openGraph_singleEdge_reachableSetoid_eq_wired hne]
    simp [ξ, positiveBoundaryConditionOfSetoid, sup_comm]
  have hrel' : (componentSetoid H ξ (∅ : Configuration H)).r u v := by
    rw [hzero]
    exact hrel
  have hins := componentSetoid_insert_eq_of_related ξ (∅ : Configuration H) huv hrel'
  have hwire : (BoundaryCondition.wired ({u,v} : Set V)).partition ≤ s := by
    intro x y hxy
    rcases (BoundaryCondition.wired_rel ({u,v} : Set V) x y).mp hxy with hxy | hxy
    · subst y
      exact s.refl _
    · have hx : x = u ∨ x = v := by simpa using hxy.1
      have hy : y = u ∨ y = v := by simpa using hxy.2
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact s.refl _
      · exact hrel
      · exact s.symm hrel
      · exact s.refl _
  have hset : s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition = s :=
    le_antisymm (sup_le le_rfl hwire) le_sup_left
  have hins' : componentSetoid H ξ ({e} : Configuration H) =
      componentSetoid H ξ (∅ : Configuration H) := by
    simpa [e] using hins
  have hcnt : componentCount H ξ ({e} : Configuration H) =
      componentCount H ξ (∅ : Configuration H) := by
    rw [componentCount, componentCount, hins']
  simp [hset]

private theorem positive_componentCount_join_wiredPair_succ_of_not_related
    (s : Setoid V) {u v : V} (hne : u ≠ v) (hrel : ¬ s.r u v) :
    Nat.card (Quotient (s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition)) + 1 =
      Nat.card (Quotient s) := by
  classical
  let H : SimpleGraph V := ⊤
  have huv : H.Adj u v := by simp [H, hne]
  let ξ := positiveBoundaryConditionOfSetoid s
  let e : H.edgeSet := ⟨s(u,v), H.mem_edgeSet.mpr huv⟩
  have hzero : componentSetoid H ξ (∅ : Configuration H) = s := by
    simp [componentSetoid_empty, ξ, positiveBoundaryConditionOfSetoid]
  have hone : componentSetoid H ξ ({e} : Configuration H) =
      s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition := by
    rw [componentSetoid, positive_openGraph_singleEdge_reachableSetoid_eq_wired hne]
    simp [ξ, positiveBoundaryConditionOfSetoid, sup_comm]
  have hrel' : ¬ (componentSetoid H ξ (∅ : Configuration H)).r u v := by
    rw [hzero]
    exact hrel
  have hcnt := componentCount_insert_of_not_related ξ (∅ : Configuration H) huv hrel'
  simpa [componentCount, e, hzero, hone] using hcnt

private theorem positive_componentCount_join_wiredPair_eq_or_succ
    (s : Setoid V) (u v : V) :
    Nat.card (Quotient (s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition)) =
        Nat.card (Quotient s) ∨
      Nat.card (Quotient (s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition)) + 1 =
        Nat.card (Quotient s) := by
  classical
  by_cases hne : u = v
  · subst v
    left
    have hw : (BoundaryCondition.wired ({u,u} : Set V)).partition = (⊥ : Setoid V) := by
      apply Setoid.ext
      intro x y
      constructor
      · intro h
        rcases (BoundaryCondition.wired_rel ({u,u} : Set V) x y).mp h with h | h
        · exact h
        · have hx : x = u := by simpa using h.1
          have hy : y = u := by simpa using h.2
          exact hx.trans hy.symm
      · intro h
        subst y
        exact (BoundaryCondition.wired_rel ({u,u} : Set V) x x).2 (Or.inl rfl)
    rw [hw]
    simp
  · by_cases hrel : s.r u v
    · left
      exact positive_componentCount_join_wiredPair_eq_of_related s hne hrel
    · right
      exact positive_componentCount_join_wiredPair_succ_of_not_related s hne hrel

/-- Merging a pair of boundary vertices either leaves the component count
unchanged, when already connected under the old boundary condition, or merges
exactly one component. -/
theorem positive_componentCount_boundaryMerge_eq_or_succ
    (ξ : BoundaryCondition V) (A : Configuration G) (u v : V) :
    componentCount G (positiveBoundaryMerge ξ u v) A = componentCount G ξ A ∨
      componentCount G (positiveBoundaryMerge ξ u v) A + 1 = componentCount G ξ A := by
  rw [componentCount, componentCount,
    componentSetoid_positiveBoundaryMerge ξ A u v]
  exact positive_componentCount_join_wiredPair_eq_or_succ
    (componentSetoid G ξ A) u v

private theorem positive_componentCount_join_wiredPair_eq_iff_related
    (s : Setoid V) (u v : V) :
    Nat.card (Quotient (s ⊔ (BoundaryCondition.wired ({u,v} : Set V)).partition)) =
      Nat.card (Quotient s) ↔ s.r u v := by
  classical
  by_cases hne : u = v
  · subst v
    have hw : (BoundaryCondition.wired ({u,u} : Set V)).partition = (⊥ : Setoid V) := by
      apply Setoid.ext
      intro x y
      constructor
      · intro h
        rcases (BoundaryCondition.wired_rel ({u,u} : Set V) x y).mp h with h | h
        · exact h
        · have hx : x = u := by simpa using h.1
          have hy : y = u := by simpa using h.2
          exact hx.trans hy.symm
      · intro h
        subst y
        exact (BoundaryCondition.wired_rel ({u,u} : Set V) x x).2 (Or.inl rfl)
    rw [hw]
    constructor
    · intro _
      exact s.refl u
    · intro _
      simp
  · constructor
    · intro hcount
      by_contra hrel
      have hsucc := positive_componentCount_join_wiredPair_succ_of_not_related s hne hrel
      omega
    · exact positive_componentCount_join_wiredPair_eq_of_related s hne

/-- The merged component count is unchanged exactly when the old boundary
partition and open edges already join the chosen vertices. -/
theorem positive_componentCount_boundaryMerge_eq_iff_connected
    (ξ : BoundaryCondition V) (A : Configuration G) (u v : V) :
    componentCount G (positiveBoundaryMerge ξ u v) A = componentCount G ξ A ↔
      (componentSetoid G ξ A).r u v := by
  rw [componentCount, componentCount,
    componentSetoid_positiveBoundaryMerge ξ A u v]
  exact positive_componentCount_join_wiredPair_eq_iff_related
    (componentSetoid G ξ A) u v

/-- Pointwise, merging two boundary classes reweights exactly configurations
whose old open components do not already join them by a factor `q⁻¹`. -/
theorem positiveFKWeight_boundaryMerge {q p : ℝ} (hq : 0 < q)
    (ξ : BoundaryCondition V) (A : Configuration G) (u v : V) :
    ((componentSetoid G ξ A).r u v →
      positiveFKWeight G q p (positiveBoundaryMerge ξ u v) A =
        positiveFKWeight G q p ξ A) ∧
    (¬ (componentSetoid G ξ A).r u v →
      positiveFKWeight G q p (positiveBoundaryMerge ξ u v) A =
        positiveFKWeight G q p ξ A / q) := by
  classical
  constructor
  · intro hrel
    have hcount := (positive_componentCount_boundaryMerge_eq_iff_connected
      ξ A u v).2 hrel
    have hcount' : Nat.card (Quotient (componentSetoid G ξ A ⊔
        (BoundaryCondition.wired ({u,v} : Set V)).partition)) =
        Nat.card (Quotient (componentSetoid G ξ A)) := by
      simpa only [componentCount, componentSetoid_positiveBoundaryMerge] using hcount
    simp only [positiveFKWeight, componentCount,
      componentSetoid_positiveBoundaryMerge, hcount']
  · intro hrel
    have hnot : componentCount G (positiveBoundaryMerge ξ u v) A ≠
        componentCount G ξ A := by
      intro heq
      exact hrel ((positive_componentCount_boundaryMerge_eq_iff_connected
        ξ A u v).1 heq)
    have hcounts := positive_componentCount_boundaryMerge_eq_or_succ ξ A u v
    rcases hcounts with heq | hsucc
    · exact (hnot heq).elim
    · have hsucc' : Nat.card (Quotient (componentSetoid G ξ A ⊔
          (BoundaryCondition.wired ({u,v} : Set V)).partition)) + 1 =
          Nat.card (Quotient (componentSetoid G ξ A)) := by
        simpa only [componentCount, componentSetoid_positiveBoundaryMerge] using hsucc
      have hpow : q ^ Nat.card
          (Quotient (componentSetoid G ξ A ⊔
            (BoundaryCondition.wired ({u,v} : Set V)).partition)) =
          q ^ Nat.card (Quotient (componentSetoid G ξ A)) / q := by
        rw [← hsucc', pow_succ]
        field_simp [hq.ne']
      simp only [positiveFKWeight, componentCount,
        componentSetoid_positiveBoundaryMerge]
      rw [hpow]
      ring

/-- A separately wired two-block boundary. -/
def positiveTwoBlockBoundary (I O : Set V) (_hIO : Disjoint I O) :
    BoundaryCondition V where
  boundary := I ∪ O
  partition := (BoundaryCondition.wired I).partition ⊔
    (BoundaryCondition.wired O).partition
  supported := by
    intro x y h
    let S : Setoid V := {
      r := fun x y => x = y ∨ (x ∈ I ∧ y ∈ I) ∨ (x ∈ O ∧ y ∈ O)
      iseqv := by
        refine ⟨?_, ?_, ?_⟩
        · intro x
          exact Or.inl rfl
        · intro x y h
          rcases h with h | h | h
          · exact Or.inl h.symm
          · exact Or.inr (Or.inl ⟨h.2,h.1⟩)
          · exact Or.inr (Or.inr ⟨h.2,h.1⟩)
        · intro x y z hxy hyz
          rcases hxy with hxy | hxy | hxy
          · subst y
            exact hyz
          · rcases hyz with hyz | hyz | hyz
            · subst z
              exact Or.inr (Or.inl hxy)
            · exact Or.inr (Or.inl ⟨hxy.1,hyz.2⟩)
            · exact False.elim ((Set.disjoint_left.mp _hIO) hxy.2 hyz.1)
          · rcases hyz with hyz | hyz | hyz
            · subst z
              exact Or.inr (Or.inr hxy)
            · exact False.elim ((Set.disjoint_left.mp _hIO) hyz.1 hxy.2)
            · exact Or.inr (Or.inr ⟨hxy.1,hyz.2⟩) }
    have hle : (BoundaryCondition.wired I).partition ⊔
        (BoundaryCondition.wired O).partition ≤ S := by
      apply sup_le
      · intro x y hxy
        rcases (BoundaryCondition.wired_rel I x y).mp hxy with heq | hI
        · exact Or.inl heq
        · exact Or.inr (Or.inl hI)
      · intro x y hxy
        rcases (BoundaryCondition.wired_rel O x y).mp hxy with heq | hO
        · exact Or.inl heq
        · exact Or.inr (Or.inr hO)
    rcases hle h with heq | hI | hO
    · exact Or.inl heq
    · exact Or.inr ⟨Or.inl hI.1, Or.inl hI.2⟩
    · exact Or.inr ⟨Or.inr hO.1, Or.inr hO.2⟩

omit [Finite V] in
/-- Joining one vertex from each separated boundary class produces the wired
union partition. -/
theorem positiveTwoBlockBoundary_merge_partition (I O : Set V) (hIO : Disjoint I O)
    {u v : V} (hu : u ∈ I) (hv : v ∈ O) :
    (positiveBoundaryMerge (positiveTwoBlockBoundary I O hIO) u v).partition =
      (BoundaryCondition.wired (I ∪ O)).partition := by
  classical
  apply Setoid.ext
  intro x y
  constructor
  · intro h
    change (((BoundaryCondition.wired I).partition ⊔
      (BoundaryCondition.wired O).partition) ⊔
      (BoundaryCondition.wired ({u,v} : Set V)).partition).r x y at h
    have hI : (BoundaryCondition.wired I).partition ≤
        (BoundaryCondition.wired (I ∪ O)).partition := by
      intro a b hab
      rw [BoundaryCondition.wired_rel] at hab ⊢
      rcases hab with hab | hab
      · exact Or.inl hab
      · exact Or.inr ⟨Or.inl hab.1, Or.inl hab.2⟩
    have hO : (BoundaryCondition.wired O).partition ≤
        (BoundaryCondition.wired (I ∪ O)).partition := by
      intro a b hab
      rw [BoundaryCondition.wired_rel] at hab ⊢
      rcases hab with hab | hab
      · exact Or.inl hab
      · exact Or.inr ⟨Or.inr hab.1, Or.inr hab.2⟩
    have hUV : (BoundaryCondition.wired ({u,v} : Set V)).partition ≤
        (BoundaryCondition.wired (I ∪ O)).partition := by
      intro a b hab
      rw [BoundaryCondition.wired_rel] at hab ⊢
      rcases hab with hab | hab
      · exact Or.inl hab
      · rcases hab.1 with rfl | rfl <;> rcases hab.2 with rfl | rfl <;>
          simp [hu, hv]
    exact (sup_le (sup_le hI hO) hUV) h
  · intro h
    rw [BoundaryCondition.wired_rel] at h
    change (((BoundaryCondition.wired I).partition ⊔
      (BoundaryCondition.wired O).partition) ⊔
      (BoundaryCondition.wired ({u,v} : Set V)).partition).r x y
    have hI : (BoundaryCondition.wired I).partition ≤
        (BoundaryCondition.wired I).partition ⊔
          (BoundaryCondition.wired O).partition ⊔
            (BoundaryCondition.wired ({u,v} : Set V)).partition :=
      le_trans le_sup_left le_sup_left
    have hO : (BoundaryCondition.wired O).partition ≤
        (BoundaryCondition.wired I).partition ⊔
          (BoundaryCondition.wired O).partition ⊔
            (BoundaryCondition.wired ({u,v} : Set V)).partition :=
      le_trans le_sup_right le_sup_left
    have hUV : (BoundaryCondition.wired ({u,v} : Set V)).partition ≤
        (BoundaryCondition.wired I).partition ⊔
          (BoundaryCondition.wired O).partition ⊔
            (BoundaryCondition.wired ({u,v} : Set V)).partition := le_sup_right
    rcases h with h | h
    · subst y
      exact ((BoundaryCondition.wired I).partition ⊔
        (BoundaryCondition.wired O).partition ⊔
        (BoundaryCondition.wired ({u,v} : Set V)).partition).refl x
    · rcases h.1 with hxI | hxO <;> rcases h.2 with hyI | hyO
      · exact hI ((BoundaryCondition.wired_rel I x y).mpr (Or.inr ⟨hxI,hyI⟩))
      · exact Setoid.trans' ((BoundaryCondition.wired I).partition ⊔
            (BoundaryCondition.wired O).partition ⊔
            (BoundaryCondition.wired ({u,v} : Set V)).partition)
          (hI ((BoundaryCondition.wired_rel I x u).mpr (Or.inr ⟨hxI,hu⟩)))
          (Setoid.trans' ((BoundaryCondition.wired I).partition ⊔
              (BoundaryCondition.wired O).partition ⊔
              (BoundaryCondition.wired ({u,v} : Set V)).partition)
            (hUV ((BoundaryCondition.wired_rel ({u,v} : Set V) u v).mpr
              (Or.inr ⟨by simp,by simp⟩)))
            (hO ((BoundaryCondition.wired_rel O v y).mpr (Or.inr ⟨hv,hyO⟩))))
      · exact Setoid.trans' ((BoundaryCondition.wired I).partition ⊔
            (BoundaryCondition.wired O).partition ⊔
            (BoundaryCondition.wired ({u,v} : Set V)).partition)
          (hO ((BoundaryCondition.wired_rel O x v).mpr (Or.inr ⟨hxO,hv⟩)))
          (Setoid.trans' ((BoundaryCondition.wired I).partition ⊔
              (BoundaryCondition.wired O).partition ⊔
              (BoundaryCondition.wired ({u,v} : Set V)).partition)
            (hUV ((BoundaryCondition.wired_rel ({u,v} : Set V) v u).mpr
              (Or.inr ⟨by simp,by simp⟩)))
            (hI ((BoundaryCondition.wired_rel I u y).mpr (Or.inr ⟨hu,hyI⟩))))
      · exact hO ((BoundaryCondition.wired_rel O x y).mpr (Or.inr ⟨hxO,hyO⟩))

end
end PottsContinuity.DualityExt
