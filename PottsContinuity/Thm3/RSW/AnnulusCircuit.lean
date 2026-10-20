module

public import PottsContinuity.Thm3.RSW.SelfDualSetup
public import PottsContinuity.FKC.Domains.PolygonDomain

/-!
# The source annulus circuit event, with genuine Jordan enclosure

DCST TeX lines 984–987. The circuit is a cyclic simple unit lattice polygon,
all of whose sampled edges are actually open. Its vertices lie in
z+(box(2n) \ box n), and z belongs to its actual bounded Jordan interior.
The Jordan theorem is supplied by FKC's q-independent polygon library;
no winding-number or enclosing-region premise is hidden in a carrier.
-/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory

/-- Actual open simple circuit in the source annulus, surrounding its center
in the genuine bounded Jordan region. Unit mesh is used throughout. -/
def annulusCircuitEvent (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (n : ℕ) :
    Set ((squareLattice.induce (V : Set (ℤ × ℤ))).edgeSet → Bool) :=
  {ω | ∃ m : ℕ, ∃ P : FKC.LatticePolygon m,
    FKC.latticeEmbed ⟨1, zero_lt_one⟩ z ∈ P.domain ⟨1, zero_lt_one⟩ ∧
    (∀ i : ZMod (m+3),
      (n : ℤ) < max |(P.vertex i).1-z.1| |(P.vertex i).2-z.2| ∧
      max |(P.vertex i).1-z.1| |(P.vertex i).2-z.2| ≤ 2*(n : ℤ)) ∧
    ∀ i : ZMod (m+3), ∃ hi : P.vertex i ∈ V, ∃ hj : P.vertex (i+1) ∈ V,
      (rcOpenGraph V ω).Adj ⟨P.vertex i, hi⟩ ⟨P.vertex (i+1), hj⟩}

/-- The source A_n probability in the genuine free box of radius R*n.
R and n range over all naturals; the definition has no exceptional scale. -/
noncomputable def annulusProbability (θ : PD.FK.Parameters) (R n : ℕ) : ℝ :=
  finiteBoundaryEventProbability (box (R*n)) θ (PD.FK.frozenBoundaryCondition (box (R*n)) 0)
    (fun ω => ω ∈ annulusCircuitEvent (box (R*n)) (0, 0) n)

/-- The annulus event is increasing in actual sampled edge states. -/
theorem annulusCircuitEvent_isUpperSet (V : Finset (ℤ × ℤ)) (z : ℤ × ℤ) (n : ℕ) :
    IsUpperSet (annulusCircuitEvent V z n) := by
  rintro ω η h ⟨m, P, hcenter, hannulus, hopen⟩
  refine ⟨m, P, hcenter, hannulus, ?_⟩
  intro i
  obtain ⟨hi, hj, hij⟩ := hopen i
  exact ⟨hi, hj, rcOpenGraph_mono V h hij⟩

/-- Nonnegativity on the full carrier of the annulus probability. -/
theorem annulusProbability_nonneg (θ : PD.FK.Parameters) (R n : ℕ) :
    0 ≤ annulusProbability θ R n := ENNReal.toReal_nonneg

end PottsContinuity.RSW
