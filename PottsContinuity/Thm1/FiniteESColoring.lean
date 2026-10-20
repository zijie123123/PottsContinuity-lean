module

public import PottsContinuity.Thm1.ClusterColoring
public import PottsContinuity.Thm1.FiniteES
public import PottsContinuity.PD.FK.Graph
public import PottsContinuity.PD.FK.Wiring

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

attribute [local instance] configurationMeasurableSpace

noncomputable section

local instance pottsESVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESConfigurationDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

 theorem pottsESSupport_interior (V : Finset (ℤ × ℤ))
    {x : ℤ × ℤ} (hx : x ∈ V) : x ∈ pottsESSupport V := by
  exact Finset.mem_union.mpr (Or.inl hx)

/-- The origin vertex in the finite Edwards--Sokal graph, when the origin is
inside the Potts volume. -/
def pottsESOriginVertex (V : Finset (ℤ × ℤ))
    (h0 : (0, 0) ∈ V) : PottsESVertex V :=
  some ⟨(0, 0), pottsESSupport_interior V h0⟩

@[simp] theorem pottsESSpin_originVertex (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (σ : V → Fin q) (h0 : (0, 0) ∈ V) :
    pottsESSpin V i σ (pottsESOriginVertex V h0) = σ ⟨(0, 0), h0⟩ := by
  simp [pottsESOriginVertex, pottsESSpin, pottsExtend, h0]

/-- Constancy of the extended spin field on each wired open component is
equivalent to the edge compatibility condition. -/
theorem pottsESCompatible_iff_componentConst (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (A : Configuration (pottsESGraph V))
    (σ : V → Fin q) :
    pottsESCompatible V i A σ ↔
      componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A ≤
        Setoid.ker (pottsESSpin V i σ) := by
  constructor
  · intro h
    apply componentSetoid_le
    · apply reachableSetoid_le_of_adj
      intro x y hxy
      rw [openGraph_adj] at hxy
      rcases hxy with ⟨e, he, hexy⟩
      have heq : e.val = Sym2.mk x y := hexy
      change pottsESSpin V i σ x = pottsESSpin V i σ y
      exact h e he x (by rw [heq]; exact Sym2.mem_mk_left x y)
        y (by rw [heq]; exact Sym2.mem_mk_right x y)
    · intro x y hxy
      rcases (BoundaryCondition.wired_rel (pottsESBoundary V) x y).mp hxy with
        heq | ⟨hx, hy⟩
      · exact congrArg (pottsESSpin V i σ) heq
      · have hx' := pottsESSpin_eq_boundary_colour V i σ hx
        have hy' := pottsESSpin_eq_boundary_colour V i σ hy
        exact hx'.trans hy'.symm
  · intro h e he x hx y hy
    by_cases hxy : x = y
    · exact congrArg (pottsESSpin V i σ) hxy
    · have hxy' : s(x, y) ∈ openEdges (pottsESGraph V) A := by
        refine ⟨e, he, ?_⟩
        exact (Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩
      have hadj : (openGraph (pottsESGraph V) A).Adj x y :=
        (openGraph_adj (pottsESGraph V) A x y).mpr hxy'
      exact h (actualConnected_component (pottsESGraph V)
        (pottsESBoundaryCondition V) A hadj.reachable)

/-- Compatible Potts assignments are precisely the colorings of the open
components with the ghost component pinned to the exterior color. -/
def pottsESCompatibleColoringEquiv (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (A : Configuration (pottsESGraph V)) :
    {σ : V → Fin q // pottsESCompatible V i A σ} ≃
      PinnedPottsClusterColoring
        (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
        none i where
  toFun σ :=
    ⟨⟨pottsESSpin V i σ.1,
      (pottsESCompatible_iff_componentConst V i A σ.1).mp σ.2⟩, rfl⟩
  invFun τ := by
    refine ⟨fun x => τ.1.1 (some ⟨x, pottsESSupport_interior V x.2⟩), ?_⟩
    apply (pottsESCompatible_iff_componentConst V i A _).mpr
    have hext : pottsESSpin V i
        (fun x => τ.1.1 (some ⟨x, pottsESSupport_interior V x.2⟩)) = τ.1.1 := by
      funext x
      cases x with
      | none => exact τ.2.symm
      | some y =>
        by_cases hy : y.1 ∈ V
        · simp [pottsESSpin, pottsExtend, hy]
        · have hboundary : some y ∈ pottsESBoundary V := by
            simp only [pottsESBoundary, Set.mem_ofPred_eq]
            exact Or.inr ⟨y, rfl, hy⟩
          have hrel : (componentSetoid (pottsESGraph V)
              (pottsESBoundaryCondition V) A).r (some y) none := by
            apply boundary_component
            rw [pottsESBoundaryCondition, BoundaryCondition.wired_rel]
            exact Or.inr ⟨hboundary, by simp [pottsESBoundary]⟩
          have hcolor := τ.1.2 hrel
          simpa [pottsESSpin, pottsExtend, hy] using τ.2.symm.trans hcolor.symm
    rw [hext]
    exact τ.1.2
  left_inv σ := by
    apply Subtype.ext
    funext x
    simp [pottsESSpin, pottsExtend, x.2]
  right_inv τ := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    cases x with
    | none => exact τ.2.symm
    | some y =>
      by_cases hy : y.1 ∈ V
      · simp [pottsESSpin, pottsExtend, hy]
      · have hboundary : some y ∈ pottsESBoundary V := by
          simp only [pottsESBoundary, Set.mem_ofPred_eq]
          exact Or.inr ⟨y, rfl, hy⟩
        have hrel : (componentSetoid (pottsESGraph V)
            (pottsESBoundaryCondition V) A).r (some y) none := by
          apply boundary_component
          rw [pottsESBoundaryCondition, BoundaryCondition.wired_rel]
          exact Or.inr ⟨hboundary, by simp [pottsESBoundary]⟩
        have hcolor := τ.1.2 hrel
        simpa [pottsESSpin, pottsExtend, hy] using τ.2.symm.trans hcolor.symm

/-- The number of compatible finite-volume spin assignments is `q` to the
number of wired open components other than the pinned ghost component. -/
theorem card_pottsESCompatibleColorings (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (A : Configuration (pottsESGraph V)) :
    Nat.card {σ : V → Fin q // pottsESCompatible V i A σ} =
      q ^ (componentCount (pottsESGraph V) (pottsESBoundaryCondition V) A - 1) := by
  rw [Nat.card_congr (pottsESCompatibleColoringEquiv V i A),
    card_pinnedPottsClusterColoring]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, componentCount]

end

end PottsContinuity.Thm1
