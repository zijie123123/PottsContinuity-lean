module

public import Mathlib
public import PottsContinuity.Frozen.Defs
public import PottsContinuity.PD.FK.Model

@[expose] public section

namespace PottsContinuity.Thm1

open Classical
open PottsContinuity
open PottsContinuity.PD.FK
attribute [local instance] configurationMeasurableSpace

/-! The Edwards--Sokal graph keeps the outer endpoints of edges meeting `V`
as distinct vertices and wires them in the boundary condition. -/

def pottsESDirections : Finset (ℤ × ℤ) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1)}

/-- The finite set of sites in `V` and all their nearest neighbours. -/
def pottsESSupport (V : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  V ∪ V.biUnion (fun x => pottsESDirections.image (fun d => x + d))

abbrev PottsESSite (V : Finset (ℤ × ℤ)) :=
  {x : ℤ × ℤ // x ∈ pottsESSupport V}

private theorem pottsESSupport_of_mem (V : Finset (ℤ × ℤ)) {x : ℤ × ℤ}
    (hx : x ∈ V) : x ∈ pottsESSupport V := by
  exact Finset.mem_union.mpr (Or.inl hx)

private theorem pottsESSupport_neighbor (V : Finset (ℤ × ℤ)) {x d : ℤ × ℤ}
    (hx : x ∈ V) (hd : d ∈ pottsESDirections) : x + d ∈ pottsESSupport V := by
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_biUnion.mpr ⟨x, hx,
    Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩

theorem pottsEdges_endpoints_support (V : Finset (ℤ × ℤ))
    {e : Sym2 (ℤ × ℤ)} (he : e ∈ pottsEdges V) {x : ℤ × ℤ} (hx : x ∈ e) :
    x ∈ pottsESSupport V := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pottsEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_insert, Finset.mem_singleton] at he
    obtain ⟨y, hy, d, hd, hEq⟩ := he
    have hxy : x = y ∨ x = y + d := by
      rw [← hEq] at hx
      simpa only [Sym2.mem_iff] using hx
    rcases hxy with hxy | hxy
    · rw [hxy]
      exact pottsESSupport_of_mem V hy
    · rw [hxy]
      exact pottsESSupport_neighbor V hy (by simpa [pottsESDirections] using hd)

theorem pottsEdges_not_diag (V : Finset (ℤ × ℤ))
    {e : Sym2 (ℤ × ℤ)} (he : e ∈ pottsEdges V) : ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pottsEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_insert, Finset.mem_singleton] at he
    obtain ⟨x, hx, d, hd, hEq⟩ := he
    have hne : x ≠ x + d := by
      intro h
      rcases (by simpa [pottsESDirections] using hd) with hd | hd | hd | hd
      · subst d
        have hfst := congrArg Prod.fst h
        simp at hfst
      · subst d
        have hfst := congrArg Prod.fst h
        simp at hfst
      · subst d
        have hsnd := congrArg Prod.snd h
        simp at hsnd
      · subst d
        have hsnd := congrArg Prod.snd h
        simp at hsnd
    rw [← hEq]
    simpa only [Sym2.mk_isDiag_iff] using hne

abbrev PottsESVertex (V : Finset (ℤ × ℤ)) := Option (PottsESSite V)

def pottsESForgetVertex (V : Finset (ℤ × ℤ)) :
    PottsESVertex V → Option (ℤ × ℤ) := Option.map Subtype.val

noncomputable def pottsESLiftEdge (V : Finset (ℤ × ℤ))
    (e : pottsEdges V) : Sym2 (PottsESVertex V) :=
  (e.1.attachWith (fun _x hx => pottsEdges_endpoints_support V e.2 hx)).map some

private theorem pottsESLiftEdge_map_forget (V : Finset (ℤ × ℤ))
    (e : pottsEdges V) :
    Sym2.map (pottsESForgetVertex V) (pottsESLiftEdge V e) = Sym2.map some e.1 := by
  simp only [pottsESLiftEdge, pottsESForgetVertex, Sym2.map_map,
    Function.comp_apply, Option.map_some]
  rw [show (fun x : PottsESSite V => some x.1) = some ∘ Subtype.val from rfl]
  rw [← Sym2.map_map, Sym2.attachWith_map_subtypeVal]

private theorem pottsESLiftEdge_injective (V : Finset (ℤ × ℤ)) :
    Function.Injective (pottsESLiftEdge V) := by
  intro e f h
  apply Subtype.ext
  have h' : Sym2.map some e.1 = Sym2.map some f.1 := by
    rw [← pottsESLiftEdge_map_forget V e, ← pottsESLiftEdge_map_forget V f]
    exact congrArg (Sym2.map (pottsESForgetVertex V)) h
  exact (Sym2.map.injective (Option.some_injective _)) h'

private theorem pottsESLiftEdge_not_diag (V : Finset (ℤ × ℤ))
    (e : pottsEdges V) : ¬ (pottsESLiftEdge V e).IsDiag := by
  intro hdiag
  have hglobal : (Sym2.map some e.1).IsDiag := by
    rw [← pottsESLiftEdge_map_forget V e]
    exact Sym2.IsDiag.map hdiag
  have hglobal' : e.1.IsDiag :=
    (Sym2.isDiag_map (Option.some_injective _)).mp hglobal
  exact pottsEdges_not_diag V e.2 hglobal'

/-- The finite graph has one extra isolated ghost vertex. Its edges are in
bijection with exactly the lattice edges meeting `V`; outer endpoints remain
distinct physical vertices and are wired to the ghost. -/
noncomputable def pottsESGraph (V : Finset (ℤ × ℤ)) : SimpleGraph (PottsESVertex V) :=
  SimpleGraph.fromEdgeSet (Set.range (pottsESLiftEdge V))

/-- The graph edges are in bijection with the unordered lattice edges meeting
`V`; the shell remains a set of distinct vertices for the wiring. -/
noncomputable def pottsESEdgeEquiv (V : Finset (ℤ × ℤ)) :
    pottsEdges V ≃ (pottsESGraph V).edgeSet := by
  let f : pottsEdges V ↪ (pottsESGraph V).edgeSet :=
    { toFun := fun e => ⟨pottsESLiftEdge V e, by
        rw [pottsESGraph, SimpleGraph.edgeSet_fromEdgeSet]
        exact ⟨Set.mem_range_self e, pottsESLiftEdge_not_diag V e⟩⟩
      inj' := by
        intro e e' h
        apply pottsESLiftEdge_injective V
        exact congrArg Subtype.val h }
  apply Equiv.ofBijective f
  constructor
  · exact f.injective
  · intro e
    have he : e.1 ∈ Set.range (pottsESLiftEdge V) := by
      have hp := e.2
      simp only [pottsESGraph, SimpleGraph.edgeSet_fromEdgeSet,
        Set.mem_sdiff] at hp
      exact hp.1
    obtain ⟨e', he'⟩ := he
    exact ⟨e', Subtype.ext he'⟩

@[simp] theorem pottsESEdgeEquiv_apply_val (V : Finset (ℤ × ℤ))
    (e : pottsEdges V) :
    (pottsESEdgeEquiv V e).1 = pottsESLiftEdge V e := rfl

theorem pottsESEdgeEquiv_map_forget (V : Finset (ℤ × ℤ))
    (e : pottsEdges V) :
    Sym2.map (fun x : PottsESVertex V => Option.map Subtype.val x)
      (pottsESEdgeEquiv V e).1 = Sym2.map some e.1 := by
  rw [pottsESEdgeEquiv_apply_val]
  exact pottsESLiftEdge_map_forget V e

/-- The exterior endpoint sites and the ghost form the wired boundary. -/
def pottsESBoundary (V : Finset (ℤ × ℤ)) : Set (PottsESVertex V) :=
  {x | x = none ∨ ∃ y, x = some y ∧ y.1 ∉ V}

/-- All exterior endpoint sites are in one wired class. -/
def pottsESBoundaryCondition (V : Finset (ℤ × ℤ)) : BoundaryCondition (PottsESVertex V) :=
  BoundaryCondition.wired (pottsESBoundary V)

/-- Extend a finite-volume spin assignment to every vertex of the finite
Edwards--Sokal graph, fixing the exterior shell to `i`. -/
def pottsESSpin (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (σ : V → Fin q) (x : PottsESVertex V) : Fin q :=
  match x with
  | none => i
  | some y => pottsExtend V i σ y.1

@[simp] theorem pottsESSpin_ghost (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (σ : V → Fin q) : pottsESSpin V i σ none = i := rfl

/-- Every exterior shell vertex and the ghost carry the fixed boundary colour. -/
theorem pottsESSpin_eq_boundary_colour (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (σ : V → Fin q) {x : PottsESVertex V} (hx : x ∈ pottsESBoundary V) :
    pottsESSpin V i σ x = i := by
  have hx' : x = none ∨ ∃ y, x = some y ∧ y.1 ∉ V := by
    simpa [pottsESBoundary] using hx
  rcases hx' with hghost | ⟨y, hxy, hy⟩
  · rw [hghost]
    rfl
  · rw [hxy]
    simp [pottsESSpin, pottsExtend, hy]

/-- An FK configuration is compatible with a Potts spin assignment precisely
when every open edge has equal endpoint spins. -/
def pottsESCompatible (V : Finset (ℤ × ℤ)) {q : ℕ} (i : Fin q)
    (A : Configuration (pottsESGraph V)) (σ : V → Fin q) : Prop :=
  ∀ e ∈ A, ∀ x ∈ e.1, ∀ y ∈ e.1,
    pottsESSpin V i σ x = pottsESSpin V i σ y

end PottsContinuity.Thm1
