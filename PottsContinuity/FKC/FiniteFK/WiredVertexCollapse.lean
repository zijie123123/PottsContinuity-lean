-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `FiniteFK/WiredVertexCollapse.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.FiniteFK.Graph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC.FiniteFK

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The carrier obtained by replacing a wired set by one ghost vertex. -/
abbrev WiredVertexCarrier (S : Set V) := Option {v : V // v ∉ S}

def wiredVertexMap (S : Set V) (_hne : S.Nonempty) : V → WiredVertexCarrier S :=
  by
    classical
    exact fun v => if hv : v ∈ S then none else some ⟨v, hv⟩

omit [DecidableEq V] in
theorem wiredVertexMap_surjective (S : Set V) (hne : S.Nonempty) :
    Function.Surjective (wiredVertexMap S hne) := by
  classical
  intro w
  cases w with
  | none =>
      obtain ⟨s, hs⟩ := hne
      exact ⟨s, by simp [wiredVertexMap, hs]⟩
  | some v => exact ⟨v.1, by simp [wiredVertexMap, v.2]⟩

omit [DecidableEq V] in
theorem wired_boundary_partition_eq_ker (S : Set V) (hne : S.Nonempty) :
    (BoundaryCondition.wired S).partition = Setoid.ker (wiredVertexMap S hne) := by
  classical
  apply Setoid.ext
  intro u v
  simp only [BoundaryCondition.wired_rel]
  change (u = v ∨ u ∈ S ∧ v ∈ S) ↔ wiredVertexMap S hne u = wiredVertexMap S hne v
  constructor
  · rintro (rfl | ⟨hu, hv⟩)
    · rfl
    · simp [wiredVertexMap, hu, hv]
  · intro h
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
    · exact Or.inr ⟨hu, hv⟩
    · simp [wiredVertexMap, hu, hv] at h
    · simp [wiredVertexMap, hu, hv] at h
    · simp [wiredVertexMap, hu, hv] at h
      exact Or.inl h

omit [DecidableEq V] in
 theorem wiredVertexMap_adj_ne (S : Set V) (hne : S.Nonempty)
    (G : SimpleGraph V) (hno : ∀ ⦃u v⦄, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S))
    {u v : V} (huv : G.Adj u v) :
    wiredVertexMap S hne u ≠ wiredVertexMap S hne v := by
  classical
  intro h
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
  · exact (hno huv ⟨hu, hv⟩).elim
  · simp [wiredVertexMap, hu, hv] at h
  · simp [wiredVertexMap, hu, hv] at h
  · simp [wiredVertexMap, hu, hv] at h
    exact (G.ne_of_adj huv h).elim

/-- Quotient graph on the ghost carrier. -/
def wiredVertexGraph (S : Set V) (hne : S.Nonempty) (G : SimpleGraph V)
    (_hno : ∀ ⦃u v⦄, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S)) :
    SimpleGraph (WiredVertexCarrier S) :=
  G.map (wiredVertexMap S hne)

omit [DecidableEq V] in
private theorem wiredVertexMap_eq_cases (S : Set V) (hne : S.Nonempty)
    {u v : V} (h : wiredVertexMap S hne u = wiredVertexMap S hne v) :
    u = v ∨ u ∈ S ∧ v ∈ S := by
  classical
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S
  · exact Or.inr ⟨hu, hv⟩
  · simp [wiredVertexMap, hu, hv] at h
  · simp [wiredVertexMap, hu, hv] at h
  · simp [wiredVertexMap, hu, hv] at h
    exact Or.inl h

omit [DecidableEq V] in
private theorem wired_edge_endpoints_eq (S : Set V) (hne : S.Nonempty)
    (G : SimpleGraph V)
    (hno : ∀ ⦃u v⦄, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S))
    (hunique : ∀ ⦃x s t⦄, x ∉ S → s ∈ S → t ∈ S →
      G.Adj s x → G.Adj t x → s = t)
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : wiredVertexMap S hne a = wiredVertexMap S hne c)
    (hbd : wiredVertexMap S hne b = wiredVertexMap S hne d) :
    a = c ∧ b = d := by
  rcases wiredVertexMap_eq_cases S hne hac with hac | ⟨haS, hcS⟩
  · subst c
    rcases wiredVertexMap_eq_cases S hne hbd with hbd | ⟨hbS, hdS⟩
    · exact ⟨rfl, hbd⟩
    · have haOut : a ∉ S := fun ha => hno hab ⟨ha, hbS⟩
      exact ⟨rfl, hunique (x := a) (s := b) (t := d) haOut hbS hdS
        hab.symm (by simpa [hbd] using hcd.symm)⟩
  · rcases wiredVertexMap_eq_cases S hne hbd with hbd | ⟨hbS, hdS⟩
    · have hbOut : b ∉ S := fun hb => hno hab ⟨haS, hb⟩
      exact ⟨hunique (x := b) (s := a) (t := c) hbOut haS hcS
        hab (by simpa [hbd] using hcd), hbd⟩
    · exact False.elim (hno hab ⟨haS, hbS⟩)

def wiredVertexEdgeMap (S : Set V) (hne : S.Nonempty)
    (G : SimpleGraph V)
    (hno : ∀ ⦃u v⦄, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S)) :
    G.edgeSet → (wiredVertexGraph S hne G hno).edgeSet :=
  fun e => ⟨Sym2.map (wiredVertexMap S hne) e.val,
    (SimpleGraph.Hom.map (wiredVertexMap S hne) G
      (wiredVertexMap_adj_ne S hne G hno)).map_mem_edgeSet e.property⟩

omit [DecidableEq V] in
 theorem wiredVertexEdgeMap_injective (S : Set V) (hne : S.Nonempty)
    (G : SimpleGraph V)
    (hno : ∀ ⦃u v⦄, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S))
    (hunique : ∀ ⦃x s t⦄, x ∉ S → s ∈ S → t ∈ S →
      G.Adj s x → G.Adj t x → s = t) :
    Function.Injective (wiredVertexEdgeMap S hne G hno) := by
  classical
  intro e₁ e₂ h
  apply Subtype.ext
  obtain ⟨⟨a, b⟩, hab⟩ := Sym2.mk_surjective e₁.val
  obtain ⟨⟨c, d⟩, hcd⟩ := Sym2.mk_surjective e₂.val
  have hadj : G.Adj a b := by
    have hp := e₁.property
    rw [← hab] at hp
    exact G.mem_edgeSet.mp hp
  have hcdAdj : G.Adj c d := by
    have hp := e₂.property
    rw [← hcd] at hp
    exact G.mem_edgeSet.mp hp
  have heq : Sym2.map (wiredVertexMap S hne) s(a,b) =
      Sym2.map (wiredVertexMap S hne) s(c,d) := by
    have heq0 := congrArg Subtype.val h
    change Sym2.map (wiredVertexMap S hne) e₁.val =
      Sym2.map (wiredVertexMap S hne) e₂.val at heq0
    rw [← hab, ← hcd] at heq0
    exact heq0
  rw [Sym2.map_mk, Sym2.map_mk] at heq
  rcases Sym2.eq_iff.mp heq with ⟨hac, hbd⟩ | ⟨had, hbc⟩
  · rcases wired_edge_endpoints_eq S hne G hno hunique hadj hcdAdj hac hbd with ⟨rfl, rfl⟩
    rw [← hab, ← hcd]
  · have hpair := wired_edge_endpoints_eq S hne G hno hunique hadj hcdAdj.symm had hbc
    rcases hpair with ⟨rfl, rfl⟩
    rw [← hab, ← hcd]
    simp

omit [DecidableEq V] in
 theorem wiredVertexEdgeMap_surjective (S : Set V) (hne : S.Nonempty)
    (G : SimpleGraph V)
    (hno : ∀ ⦃u v⦄, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S)) :
    Function.Surjective (wiredVertexEdgeMap S hne G hno) := by
  classical
  intro e
  obtain ⟨⟨x, y⟩, hxy⟩ := Sym2.mk_surjective e.val
  have hxyAdj : (wiredVertexGraph S hne G hno).Adj x y := by
    have hp := e.property
    rw [← hxy] at hp
    exact (wiredVertexGraph S hne G hno).mem_edgeSet.mp hp
  change x ≠ y ∧ ∃ a b, G.Adj a b ∧ wiredVertexMap S hne a = x ∧
    wiredVertexMap S hne b = y at hxyAdj
  rcases hxyAdj with ⟨hxyNe, a, b, hab, hax, hby⟩
  refine ⟨⟨s(a,b), G.mem_edgeSet.mpr hab⟩, ?_⟩
  apply Subtype.ext
  change Sym2.map (wiredVertexMap S hne) s(a,b) = e.val
  rw [Sym2.map_mk, hax, hby]
  simpa using hxy

/-- The graph quotient induces an actual edge-set equivalence. Its injectivity
uses both the absence of edges internal to the wired set and uniqueness of a
wired neighbor at each outside vertex. -/
def wiredVertexEdgeEquiv (S : Set V) (hne : S.Nonempty)
    (G : SimpleGraph V)
    (hno : ∀ ⦃u v⦄, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S))
    (hunique : ∀ ⦃x s t⦄, x ∉ S → s ∈ S → t ∈ S →
      G.Adj s x → G.Adj t x → s = t) :
    G.edgeSet ≃ (wiredVertexGraph S hne G hno).edgeSet :=
  Equiv.ofBijective (wiredVertexEdgeMap S hne G hno)
    ⟨wiredVertexEdgeMap_injective S hne G hno hunique,
      wiredVertexEdgeMap_surjective S hne G hno⟩

omit [DecidableEq V] in
theorem wiredVertexEdgeEquiv_val (S : Set V) (hne : S.Nonempty)
    (G : SimpleGraph V)
    (hno : ∀ ⦃u v⦄, G.Adj u v → ¬ (u ∈ S ∧ v ∈ S))
    (hunique : ∀ ⦃x s t⦄, x ∉ S → s ∈ S → t ∈ S →
      G.Adj s x → G.Adj t x → s = t)
    (e : G.edgeSet) :
    (wiredVertexEdgeEquiv S hne G hno hunique e).val =
      Sym2.map (wiredVertexMap S hne) e.val := rfl

end
end PottsContinuity.FKC.FiniteFK
