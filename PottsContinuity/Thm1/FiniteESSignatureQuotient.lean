module

public import PottsContinuity.Thm1.FiniteESPatternSignature
public import PottsContinuity.Thm1.ShellFullSignatures

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open MeasureTheory Filter Topology
open PottsContinuity
open PottsContinuity.PD.FK

noncomputable section

local instance pottsESSignatureQuotientVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (PottsESVertex V) := Fintype.ofFinite _

local instance pottsESSignatureQuotientEdgeFintype (V : Finset (ℤ × ℤ)) :
    Fintype (pottsESGraph V).edgeSet := Fintype.ofFinite _

local instance pottsESSignatureQuotientConfigDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (pottsESGraph V).edgeSet := Classical.decEq _

abbrev pottsESObservedSite (observed : Finset (ℤ × ℤ)) :=
  {x : ℤ × ℤ // x ∈ observed}

abbrev pottsESObservedPair (observed : Finset (ℤ × ℤ)) :=
  pottsESObservedSite observed × pottsESObservedSite observed

abbrev pottsESStatusSignature (observed : Finset (ℤ × ℤ)) :=
  (pottsESObservedPair observed → Bool) × (pottsESObservedSite observed → Bool)

def pottsESStatusRawRelation (observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) :
    Option (pottsESObservedSite observed) → Option (pottsESObservedSite observed) → Prop
  | none, none => True
  | some x, some y => s.1 (x, y) = true
  | some x, none => s.2 x = true
  | none, some y => s.2 y = true

def pottsESStatusSetoid (observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) :
    Setoid (Option (pottsESObservedSite observed)) :=
  Relation.EqvGen.setoid (pottsESStatusRawRelation observed s)

def pottsESStatusColor {q : ℕ} (i : Fin q) (ξ : ℤ × ℤ → Fin q)
    (observed : Finset (ℤ × ℤ))
    (x : Option (pottsESObservedSite observed)) : Fin q :=
  match x with
  | none => i
  | some x => ξ x.1

def pottsESStatusPatternCompatible {q : ℕ} (i : Fin q)
    (ξ : ℤ × ℤ → Fin q) (observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) : Prop :=
  ∀ x y, (pottsESStatusSetoid observed s).r x y →
    pottsESStatusColor i ξ observed x = pottsESStatusColor i ξ observed y

def pottsESStatusPatternFunctional {q : ℕ} (_hq : 1 ≤ q) (i : Fin q)
    (ξ : ℤ × ℤ → Fin q) (observed : Finset (ℤ × ℤ))
    (s : pottsESStatusSignature observed) : ℝ :=
  if _h : pottsESStatusPatternCompatible i ξ observed s then
    1 / (q : ℝ) ^ (Nat.card (Quotient (pottsESStatusSetoid observed s)) - 1)
  else 0

noncomputable def pottsESObservedStatusSignature (V observed : Finset (ℤ × ℤ))
    (A : Configuration (pottsESGraph V)) : pottsESStatusSignature observed := by
  classical
  exact (fun p => decide (pottsESShellBondExtension V A ∈
      pottsESLatticePairRelationEvent V p.1.1 p.2.1),
    fun x => decide (pottsESShellBondExtension V A ∈
      pottsESLatticeExitEventFrom V x.1))

noncomputable def pottsESObservedGraphVertexEquiv (V observed : Finset (ℤ × ℤ))
    (hObs : observed ⊆ V) :
    pottsESObservedSite observed ≃
      {v : PottsESVertex V // v ∈ pottsESObservedInteriorVertices V observed} := by
  classical
  let f : pottsESObservedSite observed →
      {v : PottsESVertex V // v ∈ pottsESObservedInteriorVertices V observed} :=
    fun x => ⟨pottsESInteriorVertex V x.1 (hObs x.2), by
      unfold pottsESObservedInteriorVertices
      apply Finset.mem_image.mpr
      let xV : {z : ℤ × ℤ // z ∈ observed.filter (fun z => z ∈ V)} :=
        ⟨x.1, Finset.mem_filter.mpr ⟨x.2, hObs x.2⟩⟩
      exact ⟨xV, Finset.mem_attach _ xV, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hval : pottsESInteriorVertex V x.1 (hObs x.2) =
        pottsESInteriorVertex V y.1 (hObs y.2) := congrArg Subtype.val hxy
    have hsub : (⟨x.1, Finset.mem_union.mpr (Or.inl (hObs x.2))⟩ : PottsESSite V) =
        ⟨y.1, Finset.mem_union.mpr (Or.inl (hObs y.2))⟩ := by
      simpa [pottsESInteriorVertex] using Option.some.inj hval
    exact congrArg (fun z : PottsESSite V => z.1) hsub
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨x, hxV, hxObs, hvx⟩ :=
      pottsESObservedInteriorVertex_exists V observed v.1 v.2
    refine ⟨⟨x, hxObs⟩, ?_⟩
    apply Subtype.ext
    change pottsESInteriorVertex V x (hObs hxObs) = v.1
    simpa [pottsESInteriorVertex] using hvx
  exact Equiv.ofBijective f ⟨hinj, hsurj⟩


@[simp] theorem pottsESObservedGraphVertexEquiv_apply
    (V observed : Finset (ℤ × ℤ)) (hObs : observed ⊆ V)
    (x : pottsESObservedSite observed) :
    (pottsESObservedGraphVertexEquiv V observed hObs x).1 =
      pottsESInteriorVertex V x.1 (hObs x.2) := rfl

noncomputable def pottsESObservedMarkedLabelEquiv (V observed : Finset (ℤ × ℤ))
    (hObs : observed ⊆ V) :
    Option (pottsESObservedSite observed) ≃
      Option {v : PottsESVertex V // v ∈ pottsESObservedInteriorVertices V observed} where
  toFun := Option.map (pottsESObservedGraphVertexEquiv V observed hObs)
  invFun := Option.map (pottsESObservedGraphVertexEquiv V observed hObs).symm
  left_inv := by intro x; cases x <;> simp
  right_inv := by intro x; cases x <;> simp

def pottsESObservedGraphRelation (V observed : Finset (ℤ × ℤ))
    (hObs : observed ⊆ V) (A : Configuration (pottsESGraph V)) :
    Setoid (Option (pottsESObservedSite observed)) where
  r x y :=
    (pottsESMarkedRelation
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
      (pottsESObservedInteriorVertices V observed) none).r
      ((pottsESObservedMarkedLabelEquiv V observed hObs) x)
      ((pottsESObservedMarkedLabelEquiv V observed hObs) y)
  iseqv := {
    refl := by intro x; exact (pottsESMarkedRelation
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
      (pottsESObservedInteriorVertices V observed) none).iseqv.refl _
    symm := by intro x y h; exact (pottsESMarkedRelation
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
      (pottsESObservedInteriorVertices V observed) none).iseqv.symm h
    trans := by intro x y z hxy hyz; exact (pottsESMarkedRelation
      (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
      (pottsESObservedInteriorVertices V observed) none).iseqv.trans hxy hyz }

theorem pottsESObservedStatusSignature_pair_iff
    (V observed : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (x y : pottsESObservedSite observed) :
    (pottsESObservedStatusSignature V observed A).1 (x, y) = true ↔
      pottsESShellBondExtension V A ∈
        pottsESLatticePairRelationEvent V x.1 y.1 := by
  simp [pottsESObservedStatusSignature]

theorem pottsESObservedStatusSignature_ghost_iff
    (V observed : Finset (ℤ × ℤ)) (A : Configuration (pottsESGraph V))
    (x : pottsESObservedSite observed) :
    (pottsESObservedStatusSignature V observed A).2 x = true ↔
      pottsESShellBondExtension V A ∈ pottsESLatticeExitEventFrom V x.1 := by
  simp [pottsESObservedStatusSignature]

theorem pottsESStatusRawRelation_iff_observedGraphRelation
    (V observed : Finset (ℤ × ℤ)) (hObs : observed ⊆ V)
    (A : Configuration (pottsESGraph V))
    (x y : Option (pottsESObservedSite observed)) :
    pottsESStatusRawRelation observed
        (pottsESObservedStatusSignature V observed A) x y ↔
      (pottsESObservedGraphRelation V observed hObs A).r x y := by
  let R := componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A
  let M := pottsESMarkedRelation R (pottsESObservedInteriorVertices V observed) none
  change pottsESStatusRawRelation observed
      (pottsESObservedStatusSignature V observed A) x y ↔
    M.r ((pottsESObservedMarkedLabelEquiv V observed hObs) x)
      ((pottsESObservedMarkedLabelEquiv V observed hObs) y)
  cases x with
  | none =>
    cases y with
    | none =>
      simp [pottsESStatusRawRelation, M]
    | some y =>
      change (pottsESObservedStatusSignature V observed A).2 y = true ↔ _
      rw [pottsESObservedStatusSignature_ghost_iff]
      change pottsESShellBondExtension V A ∈ pottsESLatticeExitEventFrom V y.1 ↔
        R.r none (pottsESInteriorVertex V y.1 (hObs y.2))
      have hsupport : y.1 ∈ pottsESSupport V :=
        Finset.mem_union.mpr (Or.inl (hObs y.2))
      have hrel := pottsESComponentRelation_iff_shellExitAtGhost
        V A y.1 hsupport (hObs y.2)
      constructor
      · intro hev
        exact R.iseqv.symm (hrel.mpr hev)
      · intro hconn
        exact hrel.mp (R.iseqv.symm hconn)
  | some x =>
    cases y with
    | none =>
      change (pottsESObservedStatusSignature V observed A).2 x = true ↔ _
      rw [pottsESObservedStatusSignature_ghost_iff]
      change pottsESShellBondExtension V A ∈ pottsESLatticeExitEventFrom V x.1 ↔
        R.r (pottsESInteriorVertex V x.1 (hObs x.2)) none
      have hsupport : x.1 ∈ pottsESSupport V :=
        Finset.mem_union.mpr (Or.inl (hObs x.2))
      have hrel := pottsESComponentRelation_iff_shellExitAtGhost
        V A x.1 hsupport (hObs x.2)
      exact hrel.symm
    | some y =>
      change (pottsESObservedStatusSignature V observed A).1 (x, y) = true ↔ _
      rw [pottsESObservedStatusSignature_pair_iff]
      change pottsESShellBondExtension V A ∈
          pottsESLatticePairRelationEvent V x.1 y.1 ↔
        R.r (pottsESInteriorVertex V x.1 (hObs x.2))
          (pottsESInteriorVertex V y.1 (hObs y.2))
      have hsupportX : x.1 ∈ pottsESSupport V :=
        Finset.mem_union.mpr (Or.inl (hObs x.2))
      have hsupportY : y.1 ∈ pottsESSupport V :=
        Finset.mem_union.mpr (Or.inl (hObs y.2))
      have hrel := pottsESComponentRelation_iff_shellPairEvent
        V A x.1 y.1 hsupportX hsupportY (hObs x.2) (hObs y.2)
      exact hrel.symm

theorem pottsESStatusSetoid_eq_observedGraphRelation
    (V observed : Finset (ℤ × ℤ)) (hObs : observed ⊆ V)
    (A : Configuration (pottsESGraph V)) :
    pottsESStatusSetoid observed (pottsESObservedStatusSignature V observed A) =
      pottsESObservedGraphRelation V observed hObs A := by
  apply Setoid.ext
  intro x y
  let R := pottsESStatusRawRelation observed
    (pottsESObservedStatusSignature V observed A)
  let G := pottsESObservedGraphRelation V observed hObs A
  have hRaw : ∀ x y, R x y ↔ G.r x y := by
    intro x y
    exact pottsESStatusRawRelation_iff_observedGraphRelation
      V observed hObs A x y
  have hEquiv : Equivalence R := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (hRaw x x).mpr (G.iseqv.refl x)
    · intro x y hxy
      exact (hRaw y x).mpr (G.iseqv.symm ((hRaw x y).mp hxy))
    · intro x y z hxy hyz
      exact (hRaw x z).mpr (G.iseqv.trans
        ((hRaw x y).mp hxy) ((hRaw y z).mp hyz))
  change Relation.EqvGen R x y ↔ G.r x y
  rw [hEquiv.eqvGen_iff]
  exact hRaw x y

theorem pottsESStatusQuotient_card_eq_markedClasses
    (V observed : Finset (ℤ × ℤ)) (hObs : observed ⊆ V)
    (A : Configuration (pottsESGraph V)) :
    Nat.card (Quotient
      (pottsESStatusSetoid observed (pottsESObservedStatusSignature V observed A))) =
      (pottsESMarkedComponentClasses
        (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
        (pottsESObservedInteriorVertices V observed) none).card := by
  classical
  let R := componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A
  let M := pottsESMarkedRelation R (pottsESObservedInteriorVertices V observed) none
  let G := pottsESObservedGraphRelation V observed hObs A
  let e := pottsESObservedMarkedLabelEquiv V observed hObs
  have heq : ∀ x y, G.r x y ↔ M.r (e x) (e y) := by
    intro x y
    rfl
  calc
    Nat.card (Quotient
        (pottsESStatusSetoid observed (pottsESObservedStatusSignature V observed A))) =
        Nat.card (Quotient G) := by
      rw [pottsESStatusSetoid_eq_observedGraphRelation V observed hObs A]
    _ = Nat.card (Quotient M) := Nat.card_congr (Quotient.congr e heq)
    _ = (pottsESMarkedComponentClasses R
        (pottsESObservedInteriorVertices V observed) none).card :=
      (pottsESMarkedComponentClasses_card_eq_quotient R
        (pottsESObservedInteriorVertices V observed) none).symm


def pottsESObservedGraphMarkedColor {q : ℕ} (V observed : Finset (ℤ × ℤ))
    (i : Fin q) (ξ : ℤ × ℤ → Fin q) :
    Option {v : PottsESVertex V // v ∈ pottsESObservedInteriorVertices V observed} → Fin q
  | none => i
  | some v => pottsESObservedGraphColor V i ξ v.1

private theorem pottsESPatternClassCompatible_iff_graphMarkedColor
    (V observed : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (ξ : ℤ × ℤ → Fin q) (A : Configuration (pottsESGraph V))
    (hObs : observed ⊆ V) :
    pottsESPatternClassCompatible V i observed ξ A ↔
      ∀ x y : Option {v : PottsESVertex V //
        v ∈ pottsESObservedInteriorVertices V observed},
        (pottsESMarkedRelation
          (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
          (pottsESObservedInteriorVertices V observed) none).r x y →
        pottsESObservedGraphMarkedColor V observed i ξ x =
          pottsESObservedGraphMarkedColor V observed i ξ y := by
  constructor
  · rintro ⟨_, hpair, hghost⟩ x y hxy
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y =>
        have hforward :
            (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A).r
              none y.1 := by
          change (componentSetoid
            (pottsESGraph V) (pottsESBoundaryCondition V) A).r none y.1 at hxy
          exact hxy
        have hrel := (componentSetoid
          (pottsESGraph V) (pottsESBoundaryCondition V) A).iseqv.symm hforward
        have hcol := hghost y.1 y.2 hrel
        simpa [pottsESObservedGraphMarkedColor, pottsESObservedGraphColor,
          pottsESMarkedRelation, pottsESMarkedVertex] using hcol.symm
    | some x =>
      cases y with
      | none =>
        have hcol := hghost x.1 x.2 hxy
        simpa [pottsESObservedGraphMarkedColor, pottsESObservedGraphColor,
          pottsESMarkedRelation, pottsESMarkedVertex] using hcol
      | some y =>
        have hcol := hpair x.1 x.2 y.1 y.2 hxy
        simpa [pottsESObservedGraphMarkedColor, pottsESObservedGraphColor,
          pottsESMarkedRelation, pottsESMarkedVertex] using hcol
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x hx hxnot
      exact (False.elim (hxnot (hObs hx)))
    · intro x hx y hy hxy
      exact h (some ⟨x, hx⟩) (some ⟨y, hy⟩) hxy
    · intro x hx hxy
      exact h (some ⟨x, hx⟩) none hxy

private theorem pottsESStatusColor_eq_graphMarkedColor
    (V observed : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (ξ : ℤ × ℤ → Fin q) (hObs : observed ⊆ V)
    (x : Option (pottsESObservedSite observed)) :
    pottsESStatusColor i ξ observed x =
      pottsESObservedGraphMarkedColor V observed i ξ
        ((pottsESObservedMarkedLabelEquiv V observed hObs) x) := by
  cases x with
  | none => rfl
  | some x =>
    simp [pottsESStatusColor, pottsESObservedMarkedLabelEquiv,
      pottsESObservedGraphVertexEquiv_apply,
      pottsESObservedGraphMarkedColor, pottsESObservedGraphColor,
      pottsESInteriorVertex]

theorem pottsESPatternClassCompatible_iff_statusSignature
    (V observed : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (ξ : ℤ × ℤ → Fin q) (A : Configuration (pottsESGraph V))
    (hObs : observed ⊆ V) :
    pottsESPatternClassCompatible V i observed ξ A ↔
      pottsESStatusPatternCompatible i ξ observed
        (pottsESObservedStatusSignature V observed A) := by
  rw [pottsESPatternClassCompatible_iff_graphMarkedColor V observed i ξ A hObs]
  unfold pottsESStatusPatternCompatible
  let e := pottsESObservedMarkedLabelEquiv V observed hObs
  let G := pottsESObservedGraphRelation V observed hObs A
  let S := pottsESStatusSetoid observed
    (pottsESObservedStatusSignature V observed A)
  have hSetoid : S = G :=
    pottsESStatusSetoid_eq_observedGraphRelation V observed hObs A
  constructor
  · intro h x y hxy
    have hxyG : G.r x y := by
      rw [← hSetoid]
      exact hxy
    have hcolor := h (e x) (e y) hxyG
    exact (pottsESStatusColor_eq_graphMarkedColor V observed i ξ hObs x).trans
      (hcolor.trans (pottsESStatusColor_eq_graphMarkedColor V observed i ξ hObs y).symm)
  · intro h x y hxy
    let x' := e.symm x
    let y' := e.symm y
    have hxyS : S.r x' y' := by
      rw [hSetoid]
      change (pottsESMarkedRelation
        (componentSetoid (pottsESGraph V) (pottsESBoundaryCondition V) A)
        (pottsESObservedInteriorVertices V observed) none).r
        (e x') (e y')
      simpa [x', y'] using hxy
    have hcolor := h x' y' hxyS
    have hmapX : pottsESStatusColor i ξ observed x' =
        pottsESObservedGraphMarkedColor V observed i ξ x := by
      rw [pottsESStatusColor_eq_graphMarkedColor V observed i ξ hObs]
      simp [x', e]
    have hmapY : pottsESStatusColor i ξ observed y' =
        pottsESObservedGraphMarkedColor V observed i ξ y := by
      rw [pottsESStatusColor_eq_graphMarkedColor V observed i ξ hObs]
      simp [y', e]
    exact hmapX.symm.trans (hcolor.trans hmapY)


theorem pottsESConnectivityPatternFunctional_eq_statusSignature
    (V observed : Finset (ℤ × ℤ)) {q : ℕ} (hq : 1 ≤ q) (i : Fin q)
    (ξ : ℤ × ℤ → Fin q) (A : Configuration (pottsESGraph V))
    (hObs : observed ⊆ V) :
    pottsESConnectivityPatternFunctional V i observed ξ A =
      pottsESStatusPatternFunctional hq i ξ observed
        (pottsESObservedStatusSignature V observed A) := by
  have hCompatible := pottsESPatternClassCompatible_iff_statusSignature
    V observed i ξ A hObs
  have hClasses := pottsESStatusQuotient_card_eq_markedClasses
    V observed hObs A
  by_cases hA : pottsESPatternClassCompatible V i observed ξ A
  · have hS := hCompatible.mp hA
    rcases hA with ⟨houtside, hstable, hghost⟩
    rw [pottsESConnectivityPatternFunctional_eq_inv_pow
      V hq i observed ξ A houtside hstable hghost]
    simp only [pottsESStatusPatternFunctional, dite_eq_left hS]
    rw [hClasses]
    simp [pottsESMarkedComponentClasses]
  · have hS : ¬ pottsESStatusPatternCompatible i ξ observed
        (pottsESObservedStatusSignature V observed A) := by
      intro h
      exact hA (hCompatible.mpr h)
    rw [pottsESConnectivityPatternFunctional_eq_if_classCompatible
      V hq i observed ξ A]
    simp [pottsESStatusPatternFunctional, hA, hS]


end

end PottsContinuity.Thm1
