-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Domains/LatticePolygonFiniteCellFilling.lean`, with
-- module and namespace relocated (wrappers of the SLE development replaced by `PottsContinuity.FKC.SLEWrap`)
-- and declarations not used here removed.
module

public import PottsContinuity.FKC.Domains.BoundaryCellSides

@[expose] public section

namespace PottsContinuity.FKC.LatticePolygon

noncomputable section

variable {m : ℕ} (P : LatticePolygon m)

/-- Base points whose open unit cells have centers in the actual polygon domain. -/
def interiorCellBaseSet (δ : PositiveMesh) : Set LatticeVertex :=
  {c | latticeCellCenter δ c ∈ P.domain δ}

theorem interiorCellBaseSet_finite (δ : PositiveMesh) :
    (P.interiorCellBaseSet δ).Finite := by
  have hbounded : Bornology.IsBounded (P.domain δ) := (P.isJordanDomain δ).isBounded
  obtain ⟨M, hM⟩ := hbounded.exists_norm_le
  obtain ⟨r, hr⟩ := exists_nat_gt (M / δ.val + 1)
  have hrreal : M / δ.val + 1 < (r : ℝ) := by exact_mod_cast hr
  apply (latticeBox (0, 0) r).finite_toSet.subset
  intro c hc
  have hnorm := hM (latticeCellCenter δ c) hc
  have hx : |(δ.val * ((c.1 : ℝ) + 1 / 2))| ≤ M := by
    calc
      |δ.val * ((c.1 : ℝ) + 1 / 2)| = |(latticeCellCenter δ c).re| := by
        rfl
      _ ≤ ‖latticeCellCenter δ c‖ := Complex.abs_re_le_norm _
      _ ≤ M := hnorm
  have hy : |(δ.val * ((c.2 : ℝ) + 1 / 2))| ≤ M := by
    calc
      |δ.val * ((c.2 : ℝ) + 1 / 2)| = |(latticeCellCenter δ c).im| := by
        rfl
      _ ≤ ‖latticeCellCenter δ c‖ := Complex.abs_im_le_norm _
      _ ≤ M := hnorm
  have hxscaled : |(c.1 : ℝ) + 1 / 2| ≤ M / δ.val := by
    rw [abs_mul, abs_of_pos δ.property] at hx
    apply (le_div_iff₀ δ.property).2
    simpa [mul_comm] using hx
  have hyscaled : |(c.2 : ℝ) + 1 / 2| ≤ M / δ.val := by
    rw [abs_mul, abs_of_pos δ.property] at hy
    apply (le_div_iff₀ δ.property).2
    simpa [mul_comm] using hy
  have hxreal : |(c.1 : ℝ)| ≤ M / δ.val + 1 := by
    calc
      |(c.1 : ℝ)| = |((c.1 : ℝ) + 1 / 2) - 1 / 2| := by ring_nf
      _ ≤ |(c.1 : ℝ) + 1 / 2| + |(1 / 2 : ℝ)| := abs_sub _ _
      _ ≤ M / δ.val + 1 / 2 := add_le_add hxscaled (by norm_num)
      _ ≤ M / δ.val + 1 := by norm_num
  have hyreal : |(c.2 : ℝ)| ≤ M / δ.val + 1 := by
    calc
      |(c.2 : ℝ)| = |((c.2 : ℝ) + 1 / 2) - 1 / 2| := by ring_nf
      _ ≤ |(c.2 : ℝ) + 1 / 2| + |(1 / 2 : ℝ)| := abs_sub _ _
      _ ≤ M / δ.val + 1 / 2 := add_le_add hyscaled (by norm_num)
      _ ≤ M / δ.val + 1 := by norm_num
  have hxint : |c.1| ≤ (r : ℤ) := by
    exact_mod_cast (le_of_lt (lt_of_le_of_lt hxreal hrreal))
  have hyint : |c.2| ≤ (r : ℤ) := by
    exact_mod_cast (le_of_lt (lt_of_le_of_lt hyreal hrreal))
  change c ∈ latticeBox (0, 0) r
  rw [mem_latticeBox]
  simp only [zero_sub, zero_add]
  exact ⟨⟨(abs_le.mp hxint).1, (abs_le.mp hxint).2⟩,
    ⟨(abs_le.mp hyint).1, (abs_le.mp hyint).2⟩⟩

noncomputable def interiorCellBases (δ : PositiveMesh) : Finset LatticeVertex :=
  (P.interiorCellBaseSet_finite δ).toFinset

theorem mem_interiorCellBases_iff (δ : PositiveMesh) (c : LatticeVertex) :
    c ∈ P.interiorCellBases δ ↔ latticeCellCenter δ c ∈ P.domain δ := by
  simp [interiorCellBases, interiorCellBaseSet]

/-- Every polygon boundary bond has its two adjacent cell centers on opposite
sides of the actual Jordan domain. -/
theorem boundaryBond_cellCenters_differ (δ : PositiveMesh) (e : Medial.LatticeBond)
    (he : ∃ i : ZMod (m + 3), e = P.boundaryBond i) :
    (latticeCellCenter δ (e.faceBase true) ∈ P.domain δ) ≠
      (latticeCellCenter δ (e.faceBase false) ∈ P.domain δ) := by
  obtain ⟨i, rfl⟩ := he
  rcases P.boundary_bond_cells_opposite δ i (P.boundaryBond i)
      (P.boundaryBond_toSym2 i) with ⟨hfalse, htrue⟩ | ⟨hfalse, htrue⟩
  · intro hsame
    have hfalseCenter : latticeCellCenter δ ((P.boundaryBond i).faceBase false) ∈
        P.domain δ := hfalse (latticeCellCenter_mem δ _)
    have htrueCenter : latticeCellCenter δ ((P.boundaryBond i).faceBase true) ∈
        P.exterior δ := htrue (latticeCellCenter_mem δ _)
    exact (Set.disjoint_left.mp (P.disjoint_domain_exterior δ)
      (hsame ▸ hfalseCenter) htrueCenter)
  · intro hsame
    have htrueCenter : latticeCellCenter δ ((P.boundaryBond i).faceBase true) ∈
        P.domain δ := htrue (latticeCellCenter_mem δ _)
    have hfalseCenter : latticeCellCenter δ ((P.boundaryBond i).faceBase false) ∈
        P.exterior δ := hfalse (latticeCellCenter_mem δ _)
    exact (Set.disjoint_left.mp (P.disjoint_domain_exterior δ)
      (hsame ▸ htrueCenter) hfalseCenter)

end
end PottsContinuity.FKC.LatticePolygon
