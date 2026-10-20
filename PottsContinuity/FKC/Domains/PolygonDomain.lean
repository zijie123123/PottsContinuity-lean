-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/PolygonDomain.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.LatticePolygon
public import PottsContinuity.FKC.Domains.JordanInside

/-!
# The actual domain and full closure graph of a lattice polygon

The bounded interior and all its Jordan-domain properties are derived from the
original cyclic nearest-neighbor vertices. Every boundary vertex and edge is
retained in the closure graph, including the vertices along straight boundary
runs. No independent domain-existence or graph-finiteness premise is added.
-/

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

open Set OAI.SLEExactGauge

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

/-- The bounded complementary region of the embedded polygon. -/
def domain (δ : PositiveMesh) : Set ℂ := complexInside (P.carrier δ)

theorem isJordanDomain (δ : PositiveMesh) : TauCeti.IsJordanDomain (P.domain δ) :=
  isJordanDomain_complexInside (P.isJordanCurve_carrier δ)

theorem frontier_domain (δ : PositiveMesh) : frontier (P.domain δ) = P.carrier δ :=
  frontier_complexInside (P.isJordanCurve_carrier δ)

theorem closure_domain (δ : PositiveMesh) :
    closure (P.domain δ) = P.domain δ ∪ P.carrier δ :=
  complexInside_closure (P.isJordanCurve_carrier δ)

theorem carrier_subset_closure_domain (δ : PositiveMesh) :
    P.carrier δ ⊆ closure (P.domain δ) := by
  rw [P.closure_domain]
  exact subset_union_right

theorem finite_domainVertex (δ : PositiveMesh) : Finite (DomainVertex δ (P.domain δ)) :=
  domainVertex_finite δ (P.isJordanDomain δ).isBounded

/-- The original polygon vertex as a vertex of the entire closure graph. -/
def boundaryVertex (δ : PositiveMesh) (i : ZMod (m + 3)) : DomainVertex δ (P.domain δ) :=
  ⟨P.vertex i, P.carrier_subset_closure_domain δ (P.vertex_mem_carrier δ i)⟩

@[simp] theorem boundaryVertex_val (δ : PositiveMesh) (i : ZMod (m + 3)) :
    (P.boundaryVertex δ i).val = P.vertex i := rfl

theorem boundaryVertex_injective (δ : PositiveMesh) : Function.Injective (P.boundaryVertex δ) := by
  intro i j h
  exact P.vertex_injective (congrArg Subtype.val h)

/-- Unit lattice edges have no additional lattice points between their vertices. -/
theorem latticeEmbed_mem_carrier_iff (δ : PositiveMesh) (v : LatticeVertex) :
    latticeEmbed δ v ∈ P.carrier δ ↔ ∃ i, P.vertex i = v := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    rcases (latticeEmbed_mem_segment_iff δ (P.adjacent i)).mp hi with h | h
    · exact ⟨i, h.symm⟩
    · exact ⟨i + 1, h.symm⟩
  · rintro ⟨i, rfl⟩
    exact P.vertex_mem_carrier δ i

/-- Distinct cyclic vertices provide actual distinct boundary marks on the derived domain. -/
def markedDomain (δ : PositiveMesh) (i j : ZMod (m + 3)) (hij : i ≠ j) :
    MarkedJordanDomain :=
  markedComplexInside (P.isJordanCurve_carrier δ)
    (latticeEmbed δ (P.vertex i)) (latticeEmbed δ (P.vertex j))
    (P.vertex_mem_carrier δ i) (P.vertex_mem_carrier δ j)
    (fun h => hij (P.vertex_injective (latticeEmbed_injective δ h)))

@[simp] theorem markedDomain_domain (δ : PositiveMesh) (i j : ZMod (m + 3)) (hij : i ≠ j) :
    (P.markedDomain δ i j hij).domain = P.domain δ := rfl

@[simp] theorem markedDomain_a (δ : PositiveMesh) (i j : ZMod (m + 3)) (hij : i ≠ j) :
    (P.markedDomain δ i j hij).a = latticeEmbed δ (P.vertex i) := rfl

@[simp] theorem markedDomain_b (δ : PositiveMesh) (i j : ZMod (m + 3)) (hij : i ≠ j) :
    (P.markedDomain δ i j hij).b = latticeEmbed δ (P.vertex j) := rfl

end

end PottsContinuity.FKC.LatticePolygon
