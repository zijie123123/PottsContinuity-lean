-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Medial/ParafermionicCoverExplorationToggleAvoidance.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Medial.ParafermionicCoverExploration
public import PottsContinuity.FKC.Medial.ParafermionicCoverToggle
public import PottsContinuity.FKC.Medial.ParafermionicCoverEdgePorts
public import PottsContinuity.FKC.Medial.PairingPathSupport
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

open PottsContinuity.FKC.Medial
open SimpleGraph

/-- If the actual old exploration path avoids every false-layer port above the
finite edge being toggled, the new unique exploration path has the same ordered
support list. This is only the zero-visit case; it makes no claim about toggles
whose edge is visited. -/
theorem parafermionicCoverFiniteCornerCut_toggle_same_support_of_no_false_visit
    (n : ℕ) (hn : 1 ≤ n) (A : Configuration (ParafermionicAmbientGraph n))
    (e : (ParafermionicAmbientGraph n).edgeSet)
    (p : (parafermionicCoverFiniteCornerCutPairingGraph n hn A).Walk
      (parafermionicCoverFiniteOriginCornerPort n hn, true)
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true))
    (hp : p.IsPath)
    (havoid : ∀ c : ParafermionicCoverFinitePort n,
      (c, false) ∈ p.support →
        parafermionicCoverPortEdge c.1 ≠ parafermionicCoverFiniteEdgeEmbedding n e)
    (p' : (parafermionicCoverFiniteCornerCutPairingGraph n hn
      (toggleEdgeConfiguration e A)).Walk
      (parafermionicCoverFiniteOriginCornerPort n hn, true)
      (parafermionicCoverFiniteCornerPairPerm n
        (parafermionicCoverFiniteOriginCornerPort n hn), true))
    (hp' : p'.IsPath) :
    p'.support = p.support := by
  classical
  let Aperm := parafermionicCoverFiniteLocalPairPerm n A
  let Aperm' := parafermionicCoverFiniteLocalPairPerm n (toggleEdgeConfiguration e A)
  let G := parafermionicCoverFiniteCornerCutPairingGraph n hn A
  let G' := parafermionicCoverFiniteCornerCutPairingGraph n hn
    (toggleEdgeConfiguration e A)
  have hadj (u v : ParafermionicCoverFinitePort n × Bool)
      (hu : u ∈ p.support) (hv : v ∈ p.support) (h : G.Adj u v) : G'.Adj u v := by
    rcases u with ⟨u, bu⟩
    rcases v with ⟨v, bv⟩
    cases bu <;> cases bv
    · simp only [G, G', parafermionicCoverFiniteCornerCutPairingGraph, pairingGraph,
        Bool.false_eq_true, and_false, false_and, or_false, false_or, ne_eq,
        not_true_eq_false, true_and] at h ⊢
      have hno := havoid u (by simpa using hu)
      have hpair := parafermionicCoverLocalPair_toggle_eq_of_edge_ne n A e u.1 hno
      have heq : Aperm' u = Aperm u := by
        apply Subtype.ext
        simpa [Aperm', Aperm, parafermionicCoverFiniteLocalPairPerm_val] using hpair
      exact ⟨by rw [heq]; exact h.1, h.2⟩
    · simp only [G, G', parafermionicCoverFiniteCornerCutPairingGraph, pairingGraph,
        Bool.true_eq_false, and_false, false_and, false_or, ne_eq,
        true_and] at h ⊢
      exact h
    · simp only [G, G', parafermionicCoverFiniteCornerCutPairingGraph, pairingGraph,
        Bool.true_eq_false, false_and, false_or, ne_eq,
        true_and] at h ⊢
      exact h
    · simp only [G, G', parafermionicCoverFiniteCornerCutPairingGraph, pairingGraph,
        Bool.true_eq_false, and_false, false_and, false_or, ne_eq,
        not_true_eq_false, true_and] at h ⊢
      exact h
  have hwalk : ∀ {u v} (w : G.Walk u v),
      (∀ x ∈ w.support, x ∈ p.support) →
      ∃ q : G'.Walk u v, q.support = w.support := by
    intro u v w
    induction w with
    | nil =>
        intro _
        exact ⟨Walk.nil, rfl⟩
    | @cons u v w h0 w ih =>
        intro hsub
        have hu : u ∈ (Walk.cons h0 w).support := by simp
        have hv : v ∈ (Walk.cons h0 w).support := by
          simp only [Walk.support_cons, List.mem_cons]
          exact Or.inr w.start_mem_support
        obtain ⟨q, hq⟩ := ih (fun x hx =>
          hsub x (Walk.support_subset_support_cons w h0 hx))
        refine ⟨Walk.cons (hadj u v ?_ ?_ h0) q, ?_⟩
        · exact hsub u (by simp [Walk.support_cons])
        · exact hsub v (by simp [Walk.support_cons])
        · simp [Walk.support_cons, hq]
  have hwalk' := hwalk p (fun _ hx => hx)
  obtain ⟨q, hqsupport⟩ := hwalk'
  have hqpath : q.IsPath := by
    apply Walk.IsPath.mk'
    rw [hqsupport]
    exact hp.support_nodup
  obtain ⟨r, hrpath, hrunique⟩ :=
    parafermionicCoverFiniteCornerCut_existsUnique_isPath n hn
      (toggleEdgeConfiguration e A)
  have hqr : q = r := hrunique q hqpath
  have hp'r : p' = r := hrunique p' hp'
  calc
    p'.support = r.support := by rw [hp'r]
    _ = q.support := by rw [hqr]
    _ = p.support := hqsupport

end PottsContinuity.FKC.FiniteFK
