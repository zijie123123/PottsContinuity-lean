/- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
accessible (see `related_formalizations` in formalization.yaml): file
`Medial/PairingGraph.lean`.
Adaptation: namespace/import relocation only.
-/
module

public import PottsContinuity.Thm4.TwoTerminalGraph

/-!
# A layered simple graph retaining two pairing identities

Each port has a false-layer vertex and a true-layer vertex, joined vertically.
The A-pairing acts horizontally in the false layer and the B-pairing in the
true layer. Fixed points give no horizontal self-edge. Even when A and B pair
the same ports, their horizontal edges have different layer endpoints.

For involutions with A fixed-point-free and B fixing exactly two distinct ports,
the graph has exactly one simple walk between those ports in the true layer.
No connectedness or acyclicity is assumed. The construction is applied to FK
configurations on finite boxes of the universal cover in `Thm4.PrimalConnectivity`
(`parafermionicCoverFinitePairingGraph`).
-/

@[expose] public section

namespace PottsContinuity.Thm4.Medial

open SimpleGraph

variable {P : Type*} (A B : Equiv.Perm P)
    (hA : Function.Involutive A) (hB : Function.Involutive B)

/-- Each pairing has its own layer, joined by one vertical edge at every port. -/
def pairingGraph : SimpleGraph (P × Bool) where
  Adj x y :=
    (x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.2 = false ∧ y.2 = false ∧ A x.1 = y.1 ∧ x.1 ≠ y.1) ∨
    (x.2 = true ∧ y.2 = true ∧ B x.1 = y.1 ∧ x.1 ≠ y.1)
  symm := ⟨by
    intro x y h
    rcases h with ⟨hp, hb⟩ | ⟨hx, hy, hp, hne⟩ | ⟨hx, hy, hp, hne⟩
    · exact Or.inl ⟨hp.symm, hb.symm⟩
    · right; left
      exact ⟨hy, hx, hp ▸ hA x.1, hne.symm⟩
    · right; right
      exact ⟨hy, hx, hp ▸ hB x.1, hne.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> exact h rfl⟩

instance pairingGraph_decidableAdj [DecidableEq P] :
    DecidableRel (pairingGraph A B hA hB).Adj := by
  intro x y
  change Decidable ((x.1 = y.1 ∧ x.2 ≠ y.2) ∨
    (x.2 = false ∧ y.2 = false ∧ A x.1 = y.1 ∧ x.1 ≠ y.1) ∨
    (x.2 = true ∧ y.2 = true ∧ B x.1 = y.1 ∧ x.1 ≠ y.1))
  infer_instance

@[simp] theorem pairingGraph_adj_false_false (p q : P) :
    (pairingGraph A B hA hB).Adj (p, false) (q, false) ↔ A p = q ∧ p ≠ q := by
  simp only [pairingGraph, Bool.false_eq_true, and_false, false_and, or_false, false_or,
    ne_eq, not_true_eq_false, true_and]

@[simp] theorem pairingGraph_adj_true_true (p q : P) :
    (pairingGraph A B hA hB).Adj (p, true) (q, true) ↔ B p = q ∧ p ≠ q := by
  simp only [pairingGraph, Bool.true_eq_false, and_false, false_and, false_or,
    ne_eq, not_true_eq_false, true_and]

@[simp] theorem pairingGraph_adj_false_true (p q : P) :
    (pairingGraph A B hA hB).Adj (p, false) (q, true) ↔ p = q := by
  simp [pairingGraph]

@[simp] theorem pairingGraph_adj_true_false (p q : P) :
    (pairingGraph A B hA hB).Adj (p, true) (q, false) ↔ p = q := by
  simp [pairingGraph]

variable [Fintype P] [DecidableEq P]

/-- A false-layer vertex has its vertical neighbor and its A-partner. -/
theorem pairingGraph_neighborFinset_false (hfree : ∀ p, A p ≠ p) (p : P) :
    (pairingGraph A B hA hB).neighborFinset (p, false) = {(p, true), (A p, false)} := by
  ext ⟨q, b⟩
  cases b <;> simp only [mem_neighborFinset, pairingGraph_adj_false_false,
    pairingGraph_adj_false_true, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, and_false, false_or, or_false, and_true]
  · constructor
    · rintro ⟨h, _⟩
      exact h.symm
    · intro h
      refine ⟨h.symm, ?_⟩
      intro hpq
      exact hfree p (h.symm.trans hpq.symm)
  · exact eq_comm

/-- A B-fixed point has only the vertical neighbor in the true layer. -/
theorem pairingGraph_neighborFinset_true_of_fixed {p : P} (hp : B p = p) :
    (pairingGraph A B hA hB).neighborFinset (p, true) = {(p, false)} := by
  ext ⟨q, b⟩
  cases b <;> simp [hp, eq_comm]

/-- A nonfixed true-layer vertex has its vertical neighbor and its B-partner. -/
theorem pairingGraph_neighborFinset_true_of_ne {p : P} (hp : B p ≠ p) :
    (pairingGraph A B hA hB).neighborFinset (p, true) = {(p, false), (B p, true)} := by
  ext ⟨q, b⟩
  cases b <;> simp only [mem_neighborFinset, pairingGraph_adj_true_false,
    pairingGraph_adj_true_true, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true, and_false, false_or, or_false,
    and_true]
  · exact eq_comm
  · constructor
    · rintro ⟨h, _⟩
      exact h.symm
    · intro h
      refine ⟨h.symm, ?_⟩
      intro hpq
      exact hp (h.symm.trans hpq.symm)

/-- Every false-layer vertex has degree two when A has no fixed point. -/
theorem pairingGraph_degree_false (hfree : ∀ p, A p ≠ p) (p : P) :
    (pairingGraph A B hA hB).degree (p, false) = 2 := by
  rw [SimpleGraph.degree, pairingGraph_neighborFinset_false A B hA hB hfree]
  simp

/-- Exactly the B-fixed ports are missing a horizontal true-layer edge. -/
theorem pairingGraph_degree_true_of_fixed {p : P} (hp : B p = p) :
    (pairingGraph A B hA hB).degree (p, true) = 1 := by
  rw [SimpleGraph.degree, pairingGraph_neighborFinset_true_of_fixed A B hA hB hp]
  simp

/-- All other true-layer vertices have degree two. -/
theorem pairingGraph_degree_true_of_ne {p : P} (hp : B p ≠ p) :
    (pairingGraph A B hA hB).degree (p, true) = 2 := by
  rw [SimpleGraph.degree, pairingGraph_neighborFinset_true_of_ne A B hA hB hp]
  simp

/-- Two involutive pairings with precisely two unpaired B-ports determine a unique
simple walk between those actual true-layer ports, allowing separate closed components. -/
theorem pairingGraph_existsUnique_isPath (hfree : ∀ p, A p ≠ p) {s t : P}
    (hst : s ≠ t) (hfixed : ∀ p, B p = p ↔ p = s ∨ p = t) :
    ∃! p : (pairingGraph A B hA hB).Walk (s, true) (t, true), p.IsPath := by
  apply existsUnique_isPath_of_two_terminal_degrees
  · intro h
    exact hst (congrArg Prod.fst h)
  · exact pairingGraph_degree_true_of_fixed A B hA hB ((hfixed s).mpr (Or.inl rfl))
  · exact pairingGraph_degree_true_of_fixed A B hA hB ((hfixed t).mpr (Or.inr rfl))
  · rintro ⟨p, b⟩ hps hpt
    cases b with
    | false => exact pairingGraph_degree_false A B hA hB hfree p
    | true =>
      apply pairingGraph_degree_true_of_ne A B hA hB
      intro h
      rcases (hfixed p).mp h with hs | ht
      · exact hps (Prod.ext hs rfl)
      · exact hpt (Prod.ext ht rfl)

end PottsContinuity.Thm4.Medial
