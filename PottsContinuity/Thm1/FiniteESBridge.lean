module

public import PottsContinuity.Thm1.FiniteES
public import PottsContinuity.PD.FK.ConfigurationBridge
public import PottsContinuity.Frozen.Defs

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESBridgeEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

/-- The color field on the auxiliary option carrier. -/
def pottsESOptionSpin (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (σ : V → Fin q) : Option (ℤ × ℤ) → Fin q
  | none => i
  | some x => pottsExtend V i σ x

private theorem forall₂_mem_sym2_map {α β : Type*} (f : α → β) (e : Sym2 α)
    (R : β → β → Prop) :
    (∀ x ∈ e.map f, ∀ y ∈ e.map f, R x y) ↔
      ∀ x ∈ e, ∀ y ∈ e, R (f x) (f y) := by
  constructor
  · intro h x hx y hy
    exact h (f x) (Sym2.mem_map.mpr ⟨x, hx, rfl⟩)
      (f y) (Sym2.mem_map.mpr ⟨y, hy, rfl⟩)
  · intro h x hx y hy
    obtain ⟨x', hx', rfl⟩ := Sym2.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Sym2.mem_map.mp hy
    exact h x' hx' y' hy'

private theorem pottsESSpin_eq_optionSpin_forget (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (σ : V → Fin q) (x : PottsESVertex V) :
    pottsESSpin V i σ x = pottsESOptionSpin V i σ (Option.map Subtype.val x) := by
  cases x <;> rfl

/-- Agreement on a lifted lattice edge is exactly agreement on its original
two lattice endpoints. -/
theorem pottsESEdgeEquiv_agreement_iff (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (σ : V → Fin q) (e : pottsEdges V) :
    (∀ x ∈ (pottsESEdgeEquiv V e).1, ∀ y ∈ (pottsESEdgeEquiv V e).1,
      pottsESSpin V i σ x = pottsESSpin V i σ y) ↔
    ∀ x ∈ e.1, ∀ y ∈ e.1,
      pottsExtend V i σ x = pottsExtend V i σ y := by
  have hmap : Sym2.map (fun x : PottsESVertex V => Option.map Subtype.val x)
      (pottsESEdgeEquiv V e).1 = Sym2.map some e.1 := by
    exact pottsESEdgeEquiv_map_forget V e
  calc
    _ ↔ ∀ x ∈ (pottsESEdgeEquiv V e).1.map
          (fun x : PottsESVertex V => Option.map Subtype.val x),
          ∀ y ∈ (pottsESEdgeEquiv V e).1.map
            (fun x : PottsESVertex V => Option.map Subtype.val x),
            pottsESOptionSpin V i σ x = pottsESOptionSpin V i σ y := by
      simp only [pottsESSpin_eq_optionSpin_forget]
      exact (forall₂_mem_sym2_map
        (fun x : PottsESVertex V => Option.map Subtype.val x)
        (pottsESEdgeEquiv V e).1
        (fun x y => pottsESOptionSpin V i σ x = pottsESOptionSpin V i σ y)).symm
    _ ↔ ∀ x ∈ (Sym2.map some e.1), ∀ y ∈ (Sym2.map some e.1),
          pottsESOptionSpin V i σ x = pottsESOptionSpin V i σ y := by
      rw [hmap]
    _ ↔ ∀ x ∈ e.1, ∀ y ∈ e.1,
          pottsExtend V i σ x = pottsExtend V i σ y := by
      rw [forall₂_mem_sym2_map some e.1
        (fun x y => pottsESOptionSpin V i σ x = pottsESOptionSpin V i σ y)]
      simp only [pottsESOptionSpin]

/-- Agreement of the extended spin field on one graph edge. -/
def pottsESEdgeAgreement (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (σ : V → Fin q) (e : (pottsESGraph V).edgeSet) : Prop :=
  ∀ x ∈ e.1, ∀ y ∈ e.1, pottsESSpin V i σ x = pottsESSpin V i σ y

/-- The finite graph's agreement count, written as a sum of indicators. -/
def pottsESGraphAgreeSum (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (σ : V → Fin q) : ℝ :=
  ∑ e : (pottsESGraph V).edgeSet,
    if pottsESEdgeAgreement V i σ e then (1 : ℝ) else 0

/-- The lifted edge bijection preserves the number of agreements in the frozen
finite-volume energy. -/
theorem pottsESGraphAgreeSum_eq (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (σ : V → Fin q) :
    pottsESGraphAgreeSum V i σ =
      (pottsAgreeCount V (pottsExtend V i σ) : ℝ) := by
  classical
  unfold pottsESGraphAgreeSum
  rw [← Equiv.sum_comp (pottsESEdgeEquiv V)
    (fun e : (pottsESGraph V).edgeSet =>
      if pottsESEdgeAgreement V i σ e then (1 : ℝ) else 0)]
  simp_rw [pottsESEdgeAgreement, pottsESEdgeEquiv_agreement_iff]
  rw [← Finset.sum_subtype (pottsEdges V) (fun _ => Iff.rfl)
    (fun e : Sym2 (ℤ × ℤ) =>
      if (∀ x ∈ e, ∀ y ∈ e, pottsExtend V i σ x = pottsExtend V i σ y)
      then (1 : ℝ) else 0)]
  rw [pottsAgreeCount]
  rw [Finset.sum_boole]

/-- The graph energy weight is exactly the frozen Potts weight. -/
theorem pottsESGraphGibbsWeight_eq (V : Finset (ℤ × ℤ)) {q : ℕ}
    (β : ℝ) (i : Fin q) (σ : V → Fin q) :
    Real.exp (β * pottsESGraphAgreeSum V i σ) = pottsWeight V β i σ := by
  rw [pottsESGraphAgreeSum_eq]
  rfl

end

end PottsContinuity.Thm1
