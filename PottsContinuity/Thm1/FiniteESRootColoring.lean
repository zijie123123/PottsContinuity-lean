module

public import PottsContinuity.Thm1.FiniteESMeasure

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESRootVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

/-- Compatible Boolean-bond colorings with the origin pinned are equivalent
to quotient colorings with both the ghost and origin classes pinned. -/
def pottsESRootCompatibleColoringEquiv (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (ω : (pottsESGraph V).edgeSet → Bool)
    (h0 : (0, 0) ∈ V) :
    {σ : V → Fin q //
      (∀ e, ω e = true → pottsESEdgeAgreement V i σ e) ∧
        σ ⟨(0, 0), h0⟩ = i} ≃
    {τ : PottsClusterColoring
        (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V)
          (boolConfigurationEquiv (pottsESGraph V) ω)) (Fin q) //
      τ.val none = i ∧
        τ.val (pottsESOriginVertex V h0) = i} := by
  classical
  let A := boolConfigurationEquiv (pottsESGraph V) ω
  let eBool := pottsESBoolCompatibleColoringEquiv V i ω
  let eEdgeSplit := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun σ : V → Fin q =>
      ∀ e, ω e = true → pottsESEdgeAgreement V i σ e)
    (fun σ => σ ⟨(0, 0), h0⟩ = i)
  let eBoolRoot :
      {σ : {σ : V → Fin q //
          ∀ e, ω e = true → pottsESEdgeAgreement V i σ e} //
        σ.val ⟨(0, 0), h0⟩ = i} ≃
      {σ : {σ : V → Fin q // pottsESCompatible V i A σ} //
        σ.val ⟨(0, 0), h0⟩ = i} :=
    eBool.subtypeEquiv
      (p := fun σ => σ.val ⟨(0, 0), h0⟩ = i)
      (q := fun σ => σ.val ⟨(0, 0), h0⟩ = i)
      (fun _ => Iff.rfl)
  let eCompat := pottsESCompatibleColoringEquiv V i A
  let eCompatRoot :
      {σ : {σ : V → Fin q // pottsESCompatible V i A σ} //
        σ.val ⟨(0, 0), h0⟩ = i} ≃
      {τ : PinnedPottsClusterColoring
          (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
          none i // τ.val.val (pottsESOriginVertex V h0) = i} :=
    eCompat.subtypeEquiv
      (p := fun σ => σ.val ⟨(0, 0), h0⟩ = i)
      (q := fun τ => τ.val.val (pottsESOriginVertex V h0) = i)
      (fun σ => by
    simp [eCompat, pottsESCompatibleColoringEquiv,
      pottsESSpin_originVertex])
  let R := componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A
  let ePin := pinnedPottsClusterColoringEquiv
    R none i
  let ePinRoot :
      {τ : PinnedPottsClusterColoring R none i //
        τ.val.val (pottsESOriginVertex V h0) = i} ≃
      {f : {f : Quotient R → Fin q // f (Quotient.mk R none) = i} //
        f.val (Quotient.mk R (pottsESOriginVertex V h0)) = i} :=
    ePin.subtypeEquiv
      (p := fun τ => τ.val.val (pottsESOriginVertex V h0) = i)
      (q := fun f => f.val (Quotient.mk R (pottsESOriginVertex V h0)) = i)
      (fun τ => by
        change τ.val.val (pottsESOriginVertex V h0) = i ↔
          Quotient.lift τ.val.val τ.val.property
            (Quotient.mk R (pottsESOriginVertex V h0)) = i
        rw [Quotient.lift_mk])
  let ePinSplit := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun f : Quotient R → Fin q => f (Quotient.mk R none) = i)
    (fun f => f (Quotient.mk R (pottsESOriginVertex V h0)) = i)
  let eDouble := twoPinnedPottsClusterColoringEquiv
    R none (pottsESOriginVertex V h0) i i
  exact eEdgeSplit.symm.trans (eBoolRoot.trans
    (eCompatRoot.trans (ePinRoot.trans (ePinSplit.trans eDouble.symm))))

/-- For a fixed bond state, pinning the origin and exterior classes leaves
one free color for each other open component. -/
theorem pottsESRootCompatibleColorings_count_of_not_connected
    (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (ω : (pottsESGraph V).edgeSet → Bool) (h0 : (0, 0) ∈ V)
    (hconn : ¬ (componentSetoid (pottsESGraph V)
      (pottsESBoundaryCondition V) (boolConfigurationEquiv (pottsESGraph V) ω)).r
        (pottsESOriginVertex V h0) none) :
    Nat.card {σ : V → Fin q //
      (∀ e, ω e = true → pottsESEdgeAgreement V i σ e) ∧
        σ ⟨(0, 0), h0⟩ = i} =
      q ^ (componentCount (pottsESGraph V) (pottsESBoundaryCondition V)
        (boolConfigurationEquiv (pottsESGraph V) ω) - 2) := by
  classical
  rw [Nat.card_congr (pottsESRootCompatibleColoringEquiv V i ω h0)]
  have hnot : ¬ (componentSetoid (pottsESGraph V)
      (pottsESBoundaryCondition V) (boolConfigurationEquiv (pottsESGraph V) ω)).r
        none (pottsESOriginVertex V h0) := by
    intro h
    exact hconn ((componentSetoid (pottsESGraph V)
      (pottsESBoundaryCondition V) (boolConfigurationEquiv (pottsESGraph V) ω)).symm h)
  simpa [componentCount] using
    card_two_pinnedPottsClusterColoring
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V)
        (boolConfigurationEquiv (pottsESGraph V) ω))
      none (pottsESOriginVertex V h0) hnot i i

/-- If the origin is connected to the wired exterior, its pinning is already
implied by compatibility with the fixed ghost color. -/
theorem pottsESRootCompatibleColorings_count_of_connected
    (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (ω : (pottsESGraph V).edgeSet → Bool) (h0 : (0, 0) ∈ V)
    (hconn : (componentSetoid (pottsESGraph V)
      (pottsESBoundaryCondition V) (boolConfigurationEquiv (pottsESGraph V) ω)).r
        (pottsESOriginVertex V h0) none) :
    Nat.card {σ : V → Fin q //
      (∀ e, ω e = true → pottsESEdgeAgreement V i σ e) ∧
        σ ⟨(0, 0), h0⟩ = i} =
      q ^ (componentCount (pottsESGraph V) (pottsESBoundaryCondition V)
        (boolConfigurationEquiv (pottsESGraph V) ω) - 1) := by
  classical
  let A := boolConfigurationEquiv (pottsESGraph V) ω
  have hroot (σ : V → Fin q)
      (hσ : ∀ e, ω e = true → pottsESEdgeAgreement V i σ e) :
      σ ⟨(0, 0), h0⟩ = i := by
    have hconst :=
      (pottsESCompatible_iff_componentConst V i A σ).mp
        ((pottsESCompatible_bool_iff V i σ ω).2 hσ)
    rw [← pottsESSpin_originVertex V i σ h0]
    exact (hconst hconn).trans rfl
  have e :
      {σ : V → Fin q //
        (∀ e, ω e = true → pottsESEdgeAgreement V i σ e) ∧
          σ ⟨(0, 0), h0⟩ = i} ≃
      {σ : V → Fin q //
        ∀ e, ω e = true → pottsESEdgeAgreement V i σ e} :=
    { toFun := fun σ =>
        (⟨σ.1, σ.2.1⟩ : {f : V → Fin q //
          ∀ e, ω e = true → pottsESEdgeAgreement V i f e})
      invFun := fun (σ : {f : V → Fin q //
          ∀ e, ω e = true → pottsESEdgeAgreement V i f e}) =>
        (⟨σ.1, And.intro σ.2 (hroot σ.1 σ.2)⟩ : {f : V → Fin q //
          (∀ e, ω e = true → pottsESEdgeAgreement V i f e) ∧
            f ⟨(0, 0), h0⟩ = i})
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    Nat.card {σ : V → Fin q //
        (∀ e, ω e = true → pottsESEdgeAgreement V i σ e) ∧
          σ ⟨(0, 0), h0⟩ = i} =
        Nat.card {σ : V → Fin q //
          ∀ e, ω e = true → pottsESEdgeAgreement V i σ e} :=
      Nat.card_congr e
    _ = q ^ (componentCount (pottsESGraph V) (pottsESBoundaryCondition V) A - 1) :=
      pottsESBoolCompatibleColorings_count V i ω

end

end PottsContinuity.Thm1
