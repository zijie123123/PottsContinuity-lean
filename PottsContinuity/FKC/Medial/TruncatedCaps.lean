-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/TruncatedCaps.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.BoundaryCaps
public import PottsContinuity.FKC.Domains.WiredArcEdges

/-!
# The two terminals left by deleting a proper wired arc's exterior ports

Both actual exterior ports of each original edge in the selected forward arc
are deleted. On surviving occurrences the original cyclic cap is retained
exactly when its partner survives; otherwise that occurrence is fixed. Cyclic
interval arithmetic proves that precisely the two marked endpoint occurrences
are fixed. The mask agrees with the existing geometric removed-edge predicate.
The supplied cyclic order is not asserted to be counterclockwise here.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set Medial

noncomputable section

variable {m : ℕ}

/-- Exactly the half-open sequence of original edge indices on the forward arc. -/
def WiredArcIndex (a : ZMod (m + 3)) (k : ℕ) (i : ZMod (m + 3)) : Prop :=
  ∃ t : ℕ, t < k ∧ i = a + t

theorem not_wiredArcIndex_before (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    ¬WiredArcIndex a k (a - 1) := by
  rintro ⟨t, ht, he⟩
  have hc : ((t + 1 : ℕ) : ZMod (m + 3)) = 0 := by
    push_cast
    linear_combination -he
  have hn : t + 1 = 0 := Schoenflies.ClosedPolygon.natCast_inj (m := m)
    (by omega) (by omega) (by simpa only [Nat.cast_zero] using hc)
  omega

theorem not_wiredArcIndex_finish (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    ¬WiredArcIndex a k (a + k) := by
  rintro ⟨t, ht, he⟩
  have hn : k = t := Schoenflies.ClosedPolygon.natCast_inj (m := m)
    (by omega) (by omega) (add_left_cancel he)
  omega

theorem wiredArcIndex_start (a : ZMod (m + 3)) {k : ℕ} (hk : 1 ≤ k) :
    WiredArcIndex a k a := ⟨0, by omega, by simp⟩

theorem wiredArcIndex_before_finish (a : ZMod (m + 3)) {k : ℕ} (hk : 1 ≤ k) :
    WiredArcIndex a k (a + k - 1) := by
  refine ⟨k - 1, by omega, ?_⟩
  rw [Nat.cast_sub hk, Nat.cast_one]
  ring

/-- Entering the deleted interval from a surviving edge happens only at its initial mark. -/
theorem wiredArcIndex_next_of_not {a i : ZMod (m + 3)} {k : ℕ}
    (hi : ¬WiredArcIndex a k i) (hn : WiredArcIndex a k (i + 1)) : i = a - 1 := by
  obtain ⟨t, ht, he⟩ := hn
  by_cases hzero : t = 0
  · subst t
    simp only [Nat.cast_zero, add_zero] at he
    linear_combination he
  · exfalso
    apply hi
    refine ⟨t - 1, by omega, ?_⟩
    rw [Nat.cast_sub (show 1 ≤ t by omega), Nat.cast_one]
    linear_combination he

/-- Leaving the deleted interval reaches only its final marked edge occurrence. -/
theorem wiredArcIndex_prev_of_not {a i : ZMod (m + 3)} {k : ℕ}
    (hi : ¬WiredArcIndex a k i) (hp : WiredArcIndex a k (i - 1)) : i = a + k := by
  obtain ⟨t, ht, he⟩ := hp
  have hk : k ≤ t + 1 := by
    by_contra h
    apply hi
    refine ⟨t + 1, by omega, ?_⟩
    push_cast
    linear_combination he
  have hkt : k = t + 1 := by omega
  rw [hkt]
  push_cast
  linear_combination he

/-- Both endpoint flags survive precisely for those original edges not on the deleted arc. -/
abbrev SurvivingCapLabel (a : ZMod (m + 3)) (k : ℕ) :=
  {r : ZMod (m + 3) × Bool // ¬WiredArcIndex a k r.1}

/-- Keep the actual cap partner when it survives, and fix a surviving unmatched occurrence. -/
def truncatedCapPartner (a : ZMod (m + 3)) (k : ℕ)
    (r : SurvivingCapLabel a k) : SurvivingCapLabel a k := by
  classical
  exact if h : ¬WiredArcIndex a k (boundaryCapPartner r.val).1
    then ⟨boundaryCapPartner r.val, h⟩ else r

theorem truncatedCapPartner_involutive (a : ZMod (m + 3)) (k : ℕ) :
    Function.Involutive (truncatedCapPartner a k) := by
  classical
  intro r
  by_cases h : ¬WiredArcIndex a k (boundaryCapPartner r.val).1
  · apply Subtype.ext
    simp [truncatedCapPartner, h, boundaryCapPartner_involutive r.val, r.property]
  · simp [truncatedCapPartner, h]

theorem truncatedCapPartner_eq_self_iff_partner_deleted (a : ZMod (m + 3)) (k : ℕ)
    (r : SurvivingCapLabel a k) :
    truncatedCapPartner a k r = r ↔ WiredArcIndex a k (boundaryCapPartner r.val).1 := by
  classical
  by_cases h : ¬WiredArcIndex a k (boundaryCapPartner r.val).1
  · simp only [truncatedCapPartner, dite_eq_left h]
    constructor
    · intro he
      exact (boundaryCapPartner_ne r.val (congrArg Subtype.val he)).elim
    · exact fun hd => (h hd).elim
  · simp [truncatedCapPartner, Classical.not_not.mp h]

/-- The only unmatched surviving labels occur at the two marks. -/
theorem truncatedCapPartner_eq_self_iff (a : ZMod (m + 3)) {k : ℕ} (hk : 1 ≤ k)
    (r : SurvivingCapLabel a k) :
    truncatedCapPartner a k r = r ↔
      r.val = (a - 1, true) ∨ r.val = (a + k, false) := by
  rw [truncatedCapPartner_eq_self_iff_partner_deleted]
  constructor
  · intro h
    rcases r with ⟨⟨i, b⟩, hi⟩
    cases b
    · change WiredArcIndex a k (i - 1) at h
      exact Or.inr (Prod.ext (wiredArcIndex_prev_of_not hi h) rfl)
    · change WiredArcIndex a k (i + 1) at h
      exact Or.inl (Prod.ext (wiredArcIndex_next_of_not hi h) rfl)
  · rintro (h | h)
    · rw [h]
      simpa [boundaryCapPartner] using wiredArcIndex_start a hk
    · rw [h]
      exact wiredArcIndex_before_finish a hk

/-- The last occurrence of the edge preceding the wired arc survives. -/
def capStartTerminal (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    SurvivingCapLabel a k := ⟨(a - 1, true), not_wiredArcIndex_before a hk⟩

/-- The first occurrence of the edge following the wired arc survives. -/
def capFinishTerminal (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    SurvivingCapLabel a k := ⟨(a + k, false), not_wiredArcIndex_finish a hk⟩

theorem capTerminals_ne (a : ZMod (m + 3)) {k : ℕ} (hk : k ≤ m + 2) :
    capStartTerminal a hk ≠ capFinishTerminal a hk := by
  intro h
  have hb := congrArg (fun r : SurvivingCapLabel a k => r.val.2) h
  cases hb

/-- The two fixed labels are actual distinct elements of the surviving carrier. -/
theorem truncatedCapPartner_fixed_iff (a : ZMod (m + 3)) {k : ℕ}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2) (r : SurvivingCapLabel a k) :
    truncatedCapPartner a k r = r ↔
      r = capStartTerminal a hk2 ∨ r = capFinishTerminal a hk2 := by
  rw [truncatedCapPartner_eq_self_iff a hk1]
  constructor
  · exact fun h => h.elim (fun h => Or.inl (Subtype.ext h))
      (fun h => Or.inr (Subtype.ext h))
  · exact fun h => h.elim (fun h => Or.inl (congrArg Subtype.val h))
      (fun h => Or.inr (congrArg Subtype.val h))

variable (P : LatticePolygon m)

/-- The combinatorial deletion mask is exactly membership in the existing geometric
removed-edge set for each actual exterior port, independently of its endpoint flag. -/
theorem boundaryCapPort_removed_iff (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (r : ZMod (m + 3) × Bool) :
    (P.boundaryCapPort δ r).bond.toGraphEdge ∈ P.forwardArcRemovedEdges δ a k ↔
      WiredArcIndex a k r.1 := by
  rw [P.domainBond_mem_forwardArcRemovedEdges_iff]
  change (∃ t : ℕ, t < k ∧ P.boundaryBond r.1 = P.boundaryBond (a + t)) ↔ _
  simp only [P.boundaryBond_injective.eq_iff, WiredArcIndex]

/-- The first terminal's actual primal endpoint is the initial mark. -/
theorem capStartTerminal_primalVertex (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk : k ≤ m + 2) :
    (P.boundaryCapPort δ (capStartTerminal a hk).val).toLatticePort.primalVertex =
      P.vertex a := by
  simp only [capStartTerminal, boundaryCapPort_finish, sub_add_cancel]

/-- The second terminal's actual primal endpoint is the final mark. -/
theorem capFinishTerminal_primalVertex (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk : k ≤ m + 2) :
    (P.boundaryCapPort δ (capFinishTerminal a hk).val).toLatticePort.primalVertex =
      P.vertex (a + k) := P.boundaryCapPort_start δ (a + k)

/-- The surviving actual exterior cap ports, selected by the geometric removal predicate. -/
abbrev SurvivingBoundaryCapPort (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :=
  {p : P.BoundaryCapPort δ // p.val.bond.toGraphEdge ∉ P.forwardArcRemovedEdges δ a k}

/-- The surviving labels are exactly the actual constructed exterior ports whose bonds
are not removed. No outside ports on undeleted edges are discarded. -/
def survivingBoundaryCapEquiv (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ) :
    SurvivingCapLabel a k ≃ P.SurvivingBoundaryCapPort δ a k where
  toFun r := ⟨P.boundaryCapEquiv δ r.val, by
    simpa only [P.boundaryCapEquiv_val, P.boundaryCapPort_removed_iff] using r.property⟩
  invFun p := ⟨(P.boundaryCapEquiv δ).symm p.val, by
    have h := p.property
    rw [← (P.boundaryCapEquiv δ).apply_symm_apply p.val] at h
    simpa only [P.boundaryCapEquiv_val, P.boundaryCapPort_removed_iff] using h⟩
  left_inv := by intro r; apply Subtype.ext; exact (P.boundaryCapEquiv δ).symm_apply_apply r.val
  right_inv := by intro p; apply Subtype.ext; exact (P.boundaryCapEquiv δ).apply_symm_apply p.val

@[simp] theorem survivingBoundaryCapEquiv_val (δ : PositiveMesh)
    (a : ZMod (m + 3)) (k : ℕ) (r : SurvivingCapLabel a k) :
    (P.survivingBoundaryCapEquiv δ a k r).val.val = P.boundaryCapPort δ r.val := rfl

theorem survivingBoundaryCapTerminals_ne (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk : k ≤ m + 2) :
    P.survivingBoundaryCapEquiv δ a k (capStartTerminal a hk) ≠
      P.survivingBoundaryCapEquiv δ a k (capFinishTerminal a hk) :=
  fun h => capTerminals_ne a hk ((P.survivingBoundaryCapEquiv δ a k).injective h)

/-- Truncated caps on actual surviving ports, transported through the faithful label equivalence. -/
def truncatedBoundaryCapPair (δ : PositiveMesh) (a : ZMod (m + 3)) (k : ℕ)
    (p : P.SurvivingBoundaryCapPort δ a k) : P.SurvivingBoundaryCapPort δ a k :=
  P.survivingBoundaryCapEquiv δ a k
    (truncatedCapPartner a k ((P.survivingBoundaryCapEquiv δ a k).symm p))

@[simp] theorem truncatedBoundaryCapPair_equiv (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) (r : SurvivingCapLabel a k) :
    P.truncatedBoundaryCapPair δ a k (P.survivingBoundaryCapEquiv δ a k r) =
      P.survivingBoundaryCapEquiv δ a k (truncatedCapPartner a k r) := by
  simp [truncatedBoundaryCapPair]

theorem truncatedBoundaryCapPair_involutive (δ : PositiveMesh) (a : ZMod (m + 3))
    (k : ℕ) : Function.Involutive (P.truncatedBoundaryCapPair δ a k) := by
  intro p
  obtain ⟨r, rfl⟩ := (P.survivingBoundaryCapEquiv δ a k).surjective p
  rw [P.truncatedBoundaryCapPair_equiv, P.truncatedBoundaryCapPair_equiv,
    truncatedCapPartner_involutive]

/-- Exactly two actual surviving cap ports are fixed, with no extra fixed-point premise. -/
theorem truncatedBoundaryCapPair_fixed_iff (δ : PositiveMesh) (a : ZMod (m + 3))
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 2)
    (p : P.SurvivingBoundaryCapPort δ a k) :
    P.truncatedBoundaryCapPair δ a k p = p ↔
      p = P.survivingBoundaryCapEquiv δ a k (capStartTerminal a hk2) ∨
      p = P.survivingBoundaryCapEquiv δ a k (capFinishTerminal a hk2) := by
  obtain ⟨r, rfl⟩ := (P.survivingBoundaryCapEquiv δ a k).surjective p
  rw [P.truncatedBoundaryCapPair_equiv]
  simp only [(P.survivingBoundaryCapEquiv δ a k).injective.eq_iff]
  exact truncatedCapPartner_fixed_iff a hk1 hk2 r

end
end PottsContinuity.FKC.LatticePolygon
