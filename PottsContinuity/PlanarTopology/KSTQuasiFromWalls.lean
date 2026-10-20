module

public import PottsContinuity.PlanarTopology.KSTRectangleWitness
public import PottsContinuity.PlanarTopology.KSTCorridorAttachment
public import PottsContinuity.PlanarTopology.KSTVerticalCorridor
public import Mathlib.Tactic
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace PottsContinuity.PlanarTopology
open PD.FK BD12
noncomputable section

/-- The two source vertical attachments and the two prescribed horizontal
crossings force the actual quasi-crossing. Both corridor applications are
proved internally; all final connectors are original open lattice walks. -/
theorem kst_quasi_of_vertical_walls (n : ℕ) (hn : 1 ≤ n) (ω : LatticeConfiguration)
    {a b c d s t : LatticeVertex}
    (g : PD.squareLattice.Walk a b) (g' : PD.squareLattice.Walk c d)
    (B : PD.squareLattice.Walk s a) (T : PD.squareLattice.Walk t c)
    (hg : kstMPath (192*n) g) (hg' : kstMPath (192*n) g')
    (hgO : kstPathOpen ω g) (hgO' : kstPathOpen ω g')
    (hBO : kstPathOpen ω B) (hTO : kstPathOpen ω T)
    (hs : s.2 = -768*(n : ℤ)) (ht : t.2 = 768*(n : ℤ))
    (hB : ∀ w ∈ B.support, |w.1| ≤ 528*(n : ℤ) ∧
      -768*(n : ℤ) ≤ w.2 ∧ w.2 ≤ 192*(n : ℤ))
    (hT : ∀ w ∈ T.support, |w.1| ≤ 528*(n : ℤ) ∧
      -192*(n : ℤ) ≤ w.2 ∧ w.2 ≤ 768*(n : ℤ))
    (hleft : ω ∈ horizontalRectangle (-960*(n : ℤ),-768*(n : ℤ)) (1488*n) (1536*n))
    (hright : ω ∈ horizontalRectangle (-528*(n : ℤ),-768*(n : ℤ)) (1488*n) (1536*n)) :
    ω ∈ kstQuasiCrossing (768*n) (192*n) := by
  obtain ⟨u,v,p,hp,hpO,hu,hv,hpBox⟩ := kst_horizontal_crossing_witness _ _ _ ω hleft
  obtain ⟨u',v',p',hp',hpO',hu',hv',hpBox'⟩ := kst_horizontal_crossing_witness _ _ _ ω hright
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hu hv hpBox hu' hv' hpBox'
  have hscale : 12*(16*n) = 192*n := by omega
  have hG : kstMPath (12*(16*n)) g := by rwa [hscale]
  have hG' : kstMPath (12*(16*n)) g' := by rwa [hscale]
  have hPi : kstPathIn p (-960*(n : ℤ)) (528*(n : ℤ)) (-768*(n : ℤ)) (768*(n : ℤ)) := by
    intro w hw
    have h := hpBox w hw
    exact ⟨h.1,by omega,h.2.2.1,by omega⟩
  have hPi' : kstPathIn p' (-528*(n : ℤ)) (960*(n : ℤ)) (-768*(n : ℤ)) (768*(n : ℤ)) := by
    intro w hw
    have h := hpBox' w hw
    exact ⟨h.1,by omega,h.2.2.1,by omega⟩
  have wall_boxes (l r : ℤ) (hl : l ≤ -528*(n : ℤ)) (hr : 528*(n : ℤ) ≤ r) :
      kstPathIn B l r (-768*(n : ℤ)) (768*(n : ℤ)) ∧
      kstPathIn T l r (-768*(n : ℤ)) (768*(n : ℤ)) := by
    constructor
    · intro w hw
      have h := hB w hw
      have hx := abs_le.mp h.1
      exact ⟨by omega,by omega,h.2.1,by omega⟩
    · intro w hw
      have h := hT w hw
      have hx := abs_le.mp h.1
      exact ⟨by omega,by omega,by omega,h.2.2⟩
  have hWB := wall_boxes (-960*(n : ℤ)) (528*(n : ℤ)) (by omega) le_rfl
  have hWB' := wall_boxes (-528*(n : ℤ)) (960*(n : ℤ)) le_rfl (by omega)
  have hCorr := kst_corridor_vertical_attachments (16*n) (by omega)
    (-960*(n : ℤ)) (528*(n : ℤ)) (-768*(n : ℤ)) (768*(n : ℤ))
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    g g' B T p hG hG' hWB.1 hWB.2 hs ht hp hPi hu (by omega)
  have hCorr' := kst_corridor_vertical_attachments (16*n) (by omega)
    (-528*(n : ℤ)) (960*(n : ℤ)) (-768*(n : ℤ)) (768*(n : ℤ))
    (by push_cast; omega) (by push_cast; omega) (by push_cast; omega) (by push_cast; omega)
    g g' B T p' hG hG' hWB'.1 hWB'.2 hs ht hp' hPi' hu' (by omega)
  rw [hscale] at hCorr hCorr'
  have space_wall (w : LatticeVertex)
      (hw : w ∈ g.support ∨ w ∈ g'.support ∨ w ∈ B.support ∨ w ∈ T.support) :
      4*|w.1| ≤ 5*((768*n : ℕ) : ℤ) ∧ |w.2| ≤ ((768*n : ℕ) : ℤ) := by
    rcases hw with hw | hw | hw | hw
    · have h := hg.2.2.2.2.2 w hw
      push_cast at h ⊢
      constructor <;> omega
    · have h := hg'.2.2.2.2.2 w hw
      push_cast at h ⊢
      constructor <;> omega
    · have h := hB w hw
      have hy : |w.2| ≤ 768*(n : ℤ) := abs_le.mpr ⟨h.2.1,by omega⟩
      push_cast
      constructor <;> omega
    · have h := hT w hw
      have hy : |w.2| ≤ 768*(n : ℤ) := abs_le.mpr ⟨by omega,h.2.2⟩
      push_cast
      constructor <;> omega
  have hAttach : kstAttached (768*n) (192*n) true ω := by
    apply kst_attached_of_corridor_cases (768*n) (192*n) true ω g g' B T p
      hg hg' hgO hgO' hBO hTO hpO (by dsimp; omega) _ hCorr
    intro w hw
    rcases hw with hw | hw | hw | hw | hw
    · exact space_wall w (Or.inl hw)
    · exact space_wall w (Or.inr (Or.inl hw))
    · exact space_wall w (Or.inr (Or.inr (Or.inl hw)))
    · exact space_wall w (Or.inr (Or.inr (Or.inr hw)))
    · have h := hPi w hw
      have hx : |w.1| ≤ 960*(n : ℤ) := abs_le.mpr ⟨h.1,by omega⟩
      have hy : |w.2| ≤ 768*(n : ℤ) := abs_le.mpr ⟨by omega,h.2.2.2⟩
      push_cast
      exact ⟨by omega,hy⟩
  have hRevCases : (∃ x y, ∃ q : PD.squareLattice.Walk x y,
      kstMPath (192*n) q ∧ (q.IsSubwalk p'.reverse ∨ q.reverse.IsSubwalk p'.reverse)) ∨
      (∃ z ∈ p'.reverse.support,
        z ∈ g.support ∨ z ∈ g'.support ∨ z ∈ B.support ∨ z ∈ T.support) := by
    rcases hCorr' with hq | ⟨z,hz,hw⟩
    · exact Or.inl (kst_contained_mpath_reverse _ p' hq)
    · exact Or.inr ⟨z,by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz,hw⟩
  have hAttach' : kstAttached (768*n) (192*n) false ω := by
    apply kst_attached_of_corridor_cases (768*n) (192*n) false ω g g' B T p'.reverse
      hg hg' hgO hgO' hBO hTO ((kstPathOpen_reverse_iff ω p').mpr hpO')
      (by dsimp; omega) _ hRevCases
    intro w hw
    rcases hw with hw | hw | hw | hw | hw
    · exact space_wall w (Or.inl hw)
    · exact space_wall w (Or.inr (Or.inl hw))
    · exact space_wall w (Or.inr (Or.inr (Or.inl hw)))
    · exact space_wall w (Or.inr (Or.inr (Or.inr hw)))
    · have hw' : w ∈ p'.support := by
        simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hw
      have h := hPi' w hw'
      have hx : |w.1| ≤ 960*(n : ℤ) := abs_le.mpr ⟨by omega,h.2.1⟩
      have hy : |w.2| ≤ 768*(n : ℤ) := abs_le.mpr ⟨by omega,h.2.2.2⟩
      push_cast
      exact ⟨by omega,hy⟩
  exact ⟨hAttach,hAttach'⟩

end
end PottsContinuity.PlanarTopology
