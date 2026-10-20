module

public import PottsContinuity.PlanarTopology.BalancedSeedCell
public import PottsContinuity.PlanarTopology.SeedSquareCore
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK
noncomputable section

/-- One fixed marked box at the base anchor contains every nearby seed and
its vertical translates by any integer from zero through d. -/
theorem seed_vertical_shift_subset_translated_marked_box
    (W H s d e : ℕ) (he : e ≤ d) (v y : Fin (W+1) × Fin (H+1))
    (hx : y.1.val ≤ v.1.val+1 ∧ v.1.val ≤ y.1.val+1)
    (hy : y.2.val ≤ v.2.val+1 ∧ v.2.val ≤ y.2.val+1) :
    latticeTranslate (0,(e:ℤ)) ''
      (latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) s s : Set LatticeVertex) ⊆
      ((latticeBox (0,0) (s+d+1)).image
        (latticeTranslate ((v.1.val:ℤ),(v.2.val:ℤ))) : Set LatticeVertex) := by
  rintro z ⟨q,hq,rfl⟩
  have hq := (mem_latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) q s s).mp hq
  let u : LatticeVertex := (q.1-(v.1.val:ℤ),q.2+(e:ℤ)-(v.2.val:ℤ))
  refine Finset.mem_image.mpr ⟨u,?_,?_⟩
  · apply (mem_latticeBox (0,0) u (s+d+1)).mpr
    dsimp [u] at *
    omega
  · ext <;> dsimp [u,latticeTranslate] <;> omega

theorem seed_subset_translated_marked_box
    (W H s d : ℕ) (v y : Fin (W+1) × Fin (H+1))
    (hx : y.1.val ≤ v.1.val+1 ∧ v.1.val ≤ y.1.val+1)
    (hy : y.2.val ≤ v.2.val+1 ∧ v.2.val ≤ y.2.val+1) :
    (latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) s s : Set LatticeVertex) ⊆
      ((latticeBox (0,0) (s+d+1)).image
        (latticeTranslate ((v.1.val:ℤ),(v.2.val:ℤ))) : Set LatticeVertex) := by
  intro z hz
  apply seed_vertical_shift_subset_translated_marked_box W H s d 0 (Nat.zero_le _) v y hx hy
  exact ⟨z,hz,by ext <;> simp [latticeTranslate]⟩

theorem balanced_cell_core_subset_top_seed
    {μ : MeasureTheory.Measure LatticeConfiguration} {W H r : ℕ}
    {v x y : Fin (W+1) × Fin (H+1)}
    (hc : RectangleSeedBalancedCell μ W H (2*r+2) v x y) :
    (latticeBox ((v.1.val:ℤ)+(r:ℤ)+1,(v.2.val:ℤ)+(r:ℤ)+1) r : Set LatticeVertex) ⊆
      latticeRectangle ((y.1.val:ℤ),(y.2.val:ℤ)) (2*r+2) (2*r+2) := by
  apply latticeBox_core_subset_nearby_seed r ((v.1.val:ℤ),(v.2.val:ℤ)) ((y.1.val:ℤ),(y.2.val:ℤ))
  · dsimp only [Prod.fst,Prod.snd]
    exact_mod_cast hc.top_close_fst
  · dsimp only [Prod.fst,Prod.snd]
    exact_mod_cast hc.top_close_snd

end
end PottsContinuity.PlanarTopology
