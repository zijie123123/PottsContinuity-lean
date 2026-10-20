module

public import PottsContinuity.Thm1.FiniteESPatternQuotient
public import PottsContinuity.Thm1.FiniteESColoring
public import PottsContinuity.Thm1.FiniteESCylinder

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESPatternCountVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESPatternCountEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESPatternCountConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

/-- Spin assignments satisfying edge compatibility and a finite set of graph-vertex colors. -/
def pottsESGraphPatternColorings (V : Finset (ℤ × ℤ)) {q : ℕ}
    (i : Fin q) (A : Configuration (pottsESGraph V))
    (S : Finset (PottsESVertex V)) (c : PottsESVertex V → Fin q) :=
  {σ : V → Fin q // pottsESCompatible V i A σ ∧
    ∀ x ∈ S, pottsESSpin V i σ x = c x}


/-- A class-consistent graph-vertex pattern fixes exactly its marked components. -/
theorem pottsESGraphPatternColorings_card (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (A : Configuration (pottsESGraph V))
    (S : Finset (PottsESVertex V)) (c : PottsESVertex V → Fin q)
    (hstable : ∀ x ∈ S, ∀ y ∈ S,
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x y →
        c x = c y)
    (hghost : ∀ x ∈ S,
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x none →
        c x = i) :
    Nat.card (pottsESGraphPatternColorings V i A S c) =
      q ^ (Nat.card (Quotient (componentSetoid (pottsESGraph V)
        (pottsESBoundaryCondition V) A)) -
        (insert (Quotient.mk _ none)
          (pottsESObservedComponentClasses
            (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A) S)).card) := by
  classical
  let R := componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A
  let eSource : pottsESGraphPatternColorings V i A S c ≃
      {σ : {σ : V → Fin q // pottsESCompatible V i A σ} //
        ∀ x ∈ S, pottsESSpin V i σ.val x = c x} :=
    { toFun := fun σ => ⟨⟨σ.1, σ.2.1⟩, σ.2.2⟩
      invFun := fun σ => ⟨σ.1.1, σ.1.2, σ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eCompat := pottsESCompatibleColoringEquiv V i A
  let eCompatPattern := eCompat.subtypeEquiv
    (p := fun σ => ∀ x ∈ S, pottsESSpin V i σ.1 x = c x)
    (q := fun τ => ∀ x ∈ S, τ.1.1 x = c x)
    (fun _ => Iff.rfl)
  let ePin := pinnedPottsClusterColoringEquiv R none i
  let ePinPattern := ePin.subtypeEquiv
    (p := fun τ => ∀ x ∈ S, τ.1.1 x = c x)
    (q := fun f => ∀ x ∈ S, f.1 (Quotient.mk R x) = c x)
    (fun τ => by
      change (∀ x ∈ S, τ.1.1 x = c x) ↔
        ∀ x ∈ S,
          Quotient.lift τ.1.1 τ.1.2 (Quotient.mk R x) = c x
      simp [Quotient.lift_mk])
  let ePinFlatten := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun f : Quotient R → Fin q => f (Quotient.mk R none) = i)
    (fun f => ∀ x ∈ S, f (Quotient.mk R x) = c x)
  let e := eSource.trans (eCompatPattern.trans (ePinPattern.trans ePinFlatten))
  let hcount := card_pottsESQuotientPatternColorings R none i S c hstable hghost
  calc
    Nat.card (pottsESGraphPatternColorings V i A S c) =
        Nat.card (pottsESQuotientPatternColorings R none i S c) := Nat.card_congr e
    _ = q ^ (Nat.card (Quotient R) -
        (insert (Quotient.mk R none) (pottsESObservedComponentClasses R S)).card) := by
      simpa using hcount



/-- The graph vertex representing an interior lattice site. -/
noncomputable def pottsESInteriorVertex (V : Finset (ℤ × ℤ))
    (x : ℤ × ℤ) (hx : x ∈ V) : PottsESVertex V :=
  some ⟨x, Finset.mem_union.mpr (Or.inl hx)⟩

/-- Graph vertices corresponding to observed sites inside the Potts volume. -/
noncomputable def pottsESObservedInteriorVertices (V : Finset (ℤ × ℤ))
    (observed : Finset (ℤ × ℤ)) : Finset (PottsESVertex V) := by
  classical
  let S := observed.filter (fun x => x ∈ V)
  exact S.attach.image (fun x =>
    pottsESInteriorVertex V x.1 (Finset.mem_filter.mp x.2).2)

/-- Prescribed colors on graph vertices, with the fixed exterior color at the ghost. -/
def pottsESObservedGraphColor (V : Finset (ℤ × ℤ)) {q : ℕ}
    (i : Fin q) (ξ : ℤ × ℤ → Fin q) : PottsESVertex V → Fin q
  | none => i
  | some x => ξ x.1

/-- Exterior observations are redundant once they prescribe the fixed boundary color. -/
theorem pottsESObservedInteriorPattern_iff (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (observed : Finset (ℤ × ℤ))
    (ξ : ℤ × ℤ → Fin q) (σ : V → Fin q)
    (houtside : ∀ x ∈ observed, x ∉ V → ξ x = i) :
    (∀ x ∈ observed, pottsExtend V i σ x = ξ x) ↔
      ∀ y ∈ pottsESObservedInteriorVertices V observed,
        pottsESSpin V i σ y = pottsESObservedGraphColor V i ξ y := by
  classical
  let S := observed.filter (fun x => x ∈ V)
  constructor
  · intro h y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
    have hxData := Finset.mem_filter.mp x.2
    subst y
    have hspin := h x.1 hxData.1
    simpa [pottsESObservedGraphColor, pottsESInteriorVertex, pottsESSpin,
      pottsExtend, hxData.2] using hspin
  · intro h x hxObs
    by_cases hxV : x ∈ V
    · have hxS : x ∈ S := Finset.mem_filter.mpr ⟨hxObs, hxV⟩
      let y := pottsESInteriorVertex V x hxV
      have hy : y ∈ pottsESObservedInteriorVertices V observed := by
        apply Finset.mem_image.mpr
        refine ⟨⟨x, hxS⟩, Finset.mem_attach S ⟨x, hxS⟩, ?_⟩
        rfl
      have hcolor := h y hy
      simpa [pottsESObservedGraphColor, y, pottsESInteriorVertex,
        pottsESSpin, pottsExtend, hxV] using hcolor
    · have hcolor := houtside x hxObs hxV
      simpa [pottsExtend, hxV] using hcolor.symm

/-- Cylinder constraints reduce to the graph vertices inside the volume. -/
def pottsESPatternColorings_equiv_graph (V : Finset (ℤ × ℤ))
    {q : ℕ} (i : Fin q) (A : Configuration (pottsESGraph V))
    (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (houtside : ∀ x ∈ observed, x ∉ V → ξ x = i) :
    pottsESPatternColorings V i observed ξ A ≃
      pottsESGraphPatternColorings V i A
        (pottsESObservedInteriorVertices V observed)
        (pottsESObservedGraphColor V i ξ) := by
  classical
  let hpattern := fun σ : V → Fin q =>
    pottsESObservedInteriorPattern_iff V i observed ξ σ houtside
  exact
    { toFun := fun σ => ⟨σ.1, σ.2.1, (hpattern σ.1).mp σ.2.2⟩
      invFun := fun σ => ⟨σ.1, σ.2.1, (hpattern σ.1).mpr σ.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Under exact class compatibility, the cylinder coloring count is a power
whose exponent depends only on observed quotient classes and the ghost class. -/
theorem pottsESPatternColorings_card_of_signature_compatibility
    (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (A : Configuration (pottsESGraph V))
    (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (houtside : ∀ x ∈ observed, x ∉ V → ξ x = i)
    (hstable : ∀ x ∈ pottsESObservedInteriorVertices V observed,
      ∀ y ∈ pottsESObservedInteriorVertices V observed,
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x y →
        pottsESObservedGraphColor V i ξ x = pottsESObservedGraphColor V i ξ y)
    (hghost : ∀ x ∈ pottsESObservedInteriorVertices V observed,
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x none →
        pottsESObservedGraphColor V i ξ x = i) :
    Nat.card (pottsESPatternColorings V i observed ξ A) =
      q ^ (Nat.card (Quotient (componentSetoid (pottsESGraph V)
        (pottsESBoundaryCondition V) A)) -
        (insert (Quotient.mk _ none)
          (pottsESObservedComponentClasses
            (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
            (pottsESObservedInteriorVertices V observed))).card) := by
  classical
  let R := componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A
  let e := pottsESPatternColorings_equiv_graph V i A observed ξ houtside
  calc
    Nat.card (pottsESPatternColorings V i observed ξ A) =
        Nat.card (pottsESGraphPatternColorings V i A
          (pottsESObservedInteriorVertices V observed)
          (pottsESObservedGraphColor V i ξ)) := Nat.card_congr e
    _ = q ^ (Nat.card (Quotient R) -
        (insert (Quotient.mk R none)
          (pottsESObservedComponentClasses R
            (pottsESObservedInteriorVertices V observed))).card) := by
      exact pottsESGraphPatternColorings_card V i A
        (pottsESObservedInteriorVertices V observed)
        (pottsESObservedGraphColor V i ξ) hstable hghost


theorem pottsESConnectivityPatternFunctional_eq_inv_pow
    (V : Finset (ℤ × ℤ)) {q : ℕ} (hq : 1 ≤ q) (i : Fin q)
    (observed : Finset (ℤ × ℤ)) (ξ : ℤ × ℤ → Fin q)
    (A : Configuration (pottsESGraph V))
    (houtside : ∀ x ∈ observed, x ∉ V → ξ x = i)
    (hstable : ∀ x ∈ pottsESObservedInteriorVertices V observed,
      ∀ y ∈ pottsESObservedInteriorVertices V observed,
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x y →
        pottsESObservedGraphColor V i ξ x = pottsESObservedGraphColor V i ξ y)
    (hghost : ∀ x ∈ pottsESObservedInteriorVertices V observed,
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r x none →
        pottsESObservedGraphColor V i ξ x = i) :
    pottsESConnectivityPatternFunctional V i observed ξ A =
      1 / (q : ℝ) ^ ((insert (Quotient.mk _ none)
        (pottsESObservedComponentClasses
          (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
          (pottsESObservedInteriorVertices V observed))).card - 1) := by
  classical
  let R := componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A
  let T := insert (Quotient.mk R none)
    (pottsESObservedComponentClasses R (pottsESObservedInteriorVertices V observed))
  let N := Nat.card (Quotient R)
  let : Fintype (Quotient R) := Fintype.ofFinite _
  have hTle : T.card ≤ N := by
    dsimp [N]
    rw [Nat.card_eq_fintype_card]
    exact Finset.card_le_univ T
  have hTpos : 1 ≤ T.card := by
    have hmem : Quotient.mk R none ∈ T := Finset.mem_insert_self _ _
    exact Finset.one_le_card.mpr ⟨Quotient.mk R none, hmem⟩
  have hsum : N - T.card + (T.card - 1) = N - 1 := by omega
  have hpowNat : q ^ (N - T.card) * q ^ (T.card - 1) = q ^ (N - 1) := by
    rw [← pow_add, hsum]
  have hpowReal : (q : ℝ) ^ (N - T.card) * (q : ℝ) ^ (T.card - 1) =
      (q : ℝ) ^ (N - 1) := by
    exact_mod_cast hpowNat
  have hqReal : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < q))
  have hleft :
      (Nat.card (pottsESPatternColorings V i observed ξ A) : ℝ) =
        (q : ℝ) ^ (N - T.card) := by
    rw [pottsESPatternColorings_card_of_signature_compatibility
      V i A observed ξ houtside hstable hghost]
    simp [N, T, R, Nat.cast_pow]
  have hright :
      (Nat.card {σ : V → Fin q // pottsESCompatible V i A σ} : ℝ) =
        (q : ℝ) ^ (N - 1) := by
    rw [card_pottsESCompatibleColorings]
    simp [N, R, componentCount, Nat.cast_pow]
  unfold pottsESConnectivityPatternFunctional
  rw [hleft, hright]
  have hden : (q : ℝ) ^ (N - 1) ≠ 0 := pow_ne_zero _ hqReal
  have hmarked : (q : ℝ) ^ (T.card - 1) ≠ 0 := pow_ne_zero _ hqReal
  field_simp [hden, hmarked]
  nlinarith [hpowReal]


end

end PottsContinuity.Thm1
