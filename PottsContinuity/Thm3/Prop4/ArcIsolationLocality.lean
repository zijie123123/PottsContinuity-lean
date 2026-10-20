module

public import PottsContinuity.Thm3.Prop4.ArcPathLocality
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Actual isolation is determined by edges incident to its target -/

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
variable {V : Type*} {G H : SimpleGraph V}

/-- Actual connection to the target arc, with every escaping walk visiting that arc. -/
def graphArcIsolation (G : SimpleGraph V) (D W : Set V) (x : V) : Prop :=
  (∃ y ∈ W, G.Reachable x y) ∧
    ∀ y : V, y ∉ D → ∀ p : G.Walk x y, ∃ z ∈ p.support, z ∈ W

/-- Incident-edge agreement is enough to transfer every walk supported on those edges. -/
theorem incident_supported_walk_transfer (D : Set V)
    (hagree : ∀ a ∈ D, ∀ b : V, G.Adj a b ↔ H.Adj a b)
    {x y : V} (p : G.Walk x y)
    (hp : ∀ e ∈ p.edges, ∃ a ∈ e, a ∈ D) :
    ∃ q : H.Walk x y, q.support = p.support := by
  have hedges : ∀ e ∈ p.edges, e ∈ H.edgeSet := by
    intro e he
    obtain ⟨a,ha,haD⟩ := hp e he
    obtain ⟨b,heq⟩ := Sym2.mem_iff_exists.mp ha
    have heG := p.edges_subset_edgeSet he
    rw [heq] at heG ⊢
    exact H.mem_edgeSet.mpr ((hagree a haD b).mp (G.mem_edgeSet.mp heG))
  exact ⟨p.transfer H hedges,SimpleGraph.Walk.support_transfer _ _⟩

/-- A confined walk uses only edges incident to the region containing its support. -/
theorem walk_edges_incident_of_support {x y : V} (p : G.Walk x y) (D : Set V)
    (hp : ∀ z ∈ p.support, z ∈ D) :
    ∀ e ∈ p.edges, ∃ z ∈ e, z ∈ D := by
  intro e he
  obtain ⟨⟨a,b⟩,hab⟩ := Sym2.mk_surjective e
  have ha : a ∈ e := by rw [← hab]; exact Sym2.mem_iff'.mpr (Or.inl rfl)
  exact ⟨a,ha,hp a (p.mem_support_of_mem_edges he ha)⟩

/-- The full isolation predicate depends on no edge disjoint from the target region. -/
theorem graphArcIsolation_iff_of_incident_agreement (D W : Set V) (hWD : W ⊆ D)
    (x : V) (hx : x ∈ D)
    (hagree : ∀ a ∈ D, ∀ b : V, G.Adj a b ↔ H.Adj a b) :
    graphArcIsolation G D W x ↔ graphArcIsolation H D W x := by
  classical
  have hforward : ∀ {G H : SimpleGraph V},
      (∀ a ∈ D, ∀ b : V, G.Adj a b ↔ H.Adj a b) →
      graphArcIsolation G D W x → graphArcIsolation H D W x := by
    intro G H hagree hG
    obtain ⟨y,hy,⟨p⟩⟩ := hG.1
    obtain ⟨z,hz,q,hqD⟩ := walk_to_arc_confined_of_no_escape D W hWD hx hy p hG.2
    obtain ⟨r,_⟩ := incident_supported_walk_transfer D hagree q
      (walk_edges_incident_of_support q D hqD)
    refine ⟨⟨z,hz,⟨r⟩⟩,?_⟩
    intro y hy p
    by_contra hbad
    push Not at hbad
    obtain ⟨z,hz,q,hqE,hqW⟩ := first_exit_avoiding_walk D W hx hy p hbad
    obtain ⟨r,hr⟩ := incident_supported_walk_transfer D
      (fun a ha b => (hagree a ha b).symm) q hqE
    obtain ⟨a,ha,haW⟩ := hG.2 z hz r
    rw [hr] at ha
    exact hqW a ha haW
  exact ⟨hforward hagree,hforward (fun a ha b => (hagree a ha b).symm)⟩

end PottsContinuity.Thm3.Prop4
