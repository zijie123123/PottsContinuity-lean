module

public import PottsContinuity.Thm3.RSW.AnnulusCircuit

/-! # Translation of the actual polygon and its bounded Jordan interior -/

@[expose] public section

namespace PottsContinuity.RSW
noncomputable section

/-- Translate every vertex of a genuine simple lattice polygon. -/
def translatedLatticePolygon {m : ℕ} (P : FKC.LatticePolygon m) (c : ℤ × ℤ) :
    FKC.LatticePolygon m where
  vertex i := FKC.latticeTranslate c (P.vertex i)
  vertex_injective := (FKC.latticeTranslationIso c).injective.comp P.vertex_injective
  adjacent i := (FKC.squareLattice_adj_translate_iff c _ _).mpr (P.adjacent i)

/-- The actual complex lattice embedding intertwines lattice and plane translations. -/
theorem latticeEmbed_translate (δ : FKC.PositiveMesh) (c v : ℤ × ℤ) :
    FKC.latticeEmbed δ (FKC.latticeTranslate c v) =
      FKC.latticeEmbed δ c + FKC.latticeEmbed δ v := by
  apply Complex.ext <;>
    simp [FKC.latticeEmbed,FKC.latticeTranslate,mul_add,add_comm]

/-- Translation carries the entire geometric boundary, including every edge. -/
theorem translatedLatticePolygon_carrier {m : ℕ} (P : FKC.LatticePolygon m)
    (c : ℤ × ℤ) (δ : FKC.PositiveMesh) :
    (translatedLatticePolygon P c).carrier δ =
      (Homeomorph.addLeft (FKC.latticeEmbed δ c)) '' P.carrier δ := by
  simp only [FKC.LatticePolygon.carrier,Set.image_iUnion]
  apply Set.iUnion_congr
  intro i
  change segment ℝ (FKC.latticeEmbed δ (FKC.latticeTranslate c (P.vertex i)))
      (FKC.latticeEmbed δ (FKC.latticeTranslate c (P.vertex (i+1)))) = _
  rw [latticeEmbed_translate,latticeEmbed_translate]
  change segment ℝ (FKC.latticeEmbed δ c + FKC.latticeEmbed δ (P.vertex i))
      (FKC.latticeEmbed δ c + FKC.latticeEmbed δ (P.vertex (i+1))) =
    (fun z => FKC.latticeEmbed δ c + z) ''
      segment ℝ (FKC.latticeEmbed δ (P.vertex i)) (FKC.latticeEmbed δ (P.vertex (i+1)))
  exact (vadd_segment (𝕜 := ℝ) (FKC.latticeEmbed δ c)
    (FKC.latticeEmbed δ (P.vertex i)) (FKC.latticeEmbed δ (P.vertex (i+1)))).symm

/-- The actual bounded Jordan region translates along with the boundary.
This uses the proved q-independent Jordan-inside homeomorphism theorem. -/
theorem translatedLatticePolygon_domain {m : ℕ} (P : FKC.LatticePolygon m)
    (c : ℤ × ℤ) (δ : FKC.PositiveMesh) :
    (translatedLatticePolygon P c).domain δ =
      (Homeomorph.addLeft (FKC.latticeEmbed δ c)) '' P.domain δ := by
  unfold FKC.LatticePolygon.domain
  rw [translatedLatticePolygon_carrier]
  exact (OAI.SLEExactGauge.complexInside_transport
    (Homeomorph.addLeft (FKC.latticeEmbed δ c)) (P.carrier δ)).symm

/-- Jordan enclosure of a lattice point is preserved under the same translation. -/
theorem translatedLatticePolygon_center {m : ℕ} (P : FKC.LatticePolygon m)
    (c z : ℤ × ℤ) (δ : FKC.PositiveMesh) (hz : FKC.latticeEmbed δ z ∈ P.domain δ) :
    FKC.latticeEmbed δ (FKC.latticeTranslate c z) ∈ (translatedLatticePolygon P c).domain δ := by
  rw [translatedLatticePolygon_domain,latticeEmbed_translate]
  exact ⟨FKC.latticeEmbed δ z,hz,rfl⟩

end
end PottsContinuity.RSW
