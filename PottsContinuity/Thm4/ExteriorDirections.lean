module

public import PottsContinuity.Thm4.WindingVisitMass

@[expose] public section

namespace PottsContinuity.Thm4
open PottsContinuity.PD.FK PottsContinuity.Thm4.Medial
noncomputable section
attribute [local instance] Classical.propDecidable

/-- At every retained vertex at least one vertical direction stays in the box.
At the top use the downward direction; elsewhere use the upward direction. -/
theorem vertical_port_internal (n : ℕ) (hn : 1 ≤ n)
    (c : ParafermionicCoverFinitePort n)
    (ha : c.1.1.bond.axis = LatticeAxis.vertical)
    (ht : c.1.1.tip = decide ((parafermionicCoverPortVertex c.1).1.2 = (n : ℤ))) :
    parafermionicCoverFinitePortOtherEndpointInBox n c := by
  rcases c with ⟨⟨⟨⟨⟨x, y⟩, a⟩, t, s⟩, k⟩, hc⟩
  change a = LatticeAxis.vertical at ha
  subst a
  have hshift : parafermionicCoverSheetShift (x, y) (x, y + 1) = 0 := by
    simp [parafermionicCoverSheetShift]
  cases t <;>
    simp only [parafermionicCoverPortVertex, LatticePort.primalVertex,
      LatticeBond.endpoint, LatticeBond.source, LatticeBond.target, Bool.false_eq_true,
      ↓reduceIte, parafermionicCoverBoxVertices_mem] at hc ht
  all_goals
    simp only [parafermionicCoverFinitePortOtherEndpointInBox,
      parafermionicCoverPortOtherVertex, Bool.false_eq_true, ↓reduceIte,
      LatticeBond.source, LatticeBond.target, hshift, add_zero, sub_zero,
      parafermionicCoverBoxVertices_mem]
    simp only [false_eq_decide_iff, true_eq_decide_iff] at ht
    have hnZ : (1 : ℤ) ≤ n := by exact_mod_cast hn
    omega

/-- Flags of an incoming port determine the side once axis and tip are fixed. -/
theorem incoming_port_side_eq (n : ℕ) (c d : ParafermionicCoverFinitePort n)
    (ha : c.1.1.bond.axis = d.1.1.bond.axis) (ht : c.1.1.tip = d.1.1.tip)
    (hc : parafermionicCoverIncomingPrimalLeft c.1 = true)
    (hd : parafermionicCoverIncomingPrimalLeft d.1 = true) :
    c.1.1.side = d.1.1.side := by
  change medialIncomingPrimalLeft c.1.1 = true at hc
  change medialIncomingPrimalLeft d.1.1 = true at hd
  unfold medialIncomingPrimalLeft at hc hd
  rw [← ha, ← ht] at hd
  cases hax : c.1.1.bond.axis <;> cases htt : c.1.1.tip <;>
    cases hda : d.1.1.bond.axis <;> cases hdt : d.1.1.tip <;>
    cases hsc : c.1.1.side <;> cases hsd : d.1.1.side <;> simp_all

/-- At any retained primal vertex at most three incoming port directions lead
outside the box, including the extreme sheets along the seam. -/
theorem exterior_incoming_ports_at_vertex_card_le_three (n : ℕ) (hn : 1 ≤ n)
    (v : ParafermionicAmbientVertex n) :
    (Finset.univ.filter fun c : ParafermionicCoverFinitePort n =>
      parafermionicCoverPortVertex c.1 = v.1 ∧
        ¬ parafermionicCoverFinitePortOtherEndpointInBox n c ∧
        parafermionicCoverIncomingPrimalLeft c.1 = true).card ≤ 3 := by
  classical
  let S := Finset.univ.filter fun c : ParafermionicCoverFinitePort n =>
    parafermionicCoverPortVertex c.1 = v.1 ∧
      ¬ parafermionicCoverFinitePortOtherEndpointInBox n c ∧
      parafermionicCoverIncomingPrimalLeft c.1 = true
  let d₀ : LatticeAxis × Bool := (.vertical, decide (v.1.1.2 = (n : ℤ)))
  let T : Finset (LatticeAxis × Bool) := Finset.univ.erase d₀
  let f := fun c : ParafermionicCoverFinitePort n => (c.1.1.bond.axis, c.1.1.tip)
  have hmap : Set.MapsTo f (S : Set _) (T : Set _) := by
    intro c hc
    obtain ⟨hv, he, hf⟩ := (Finset.mem_filter.mp hc).2
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have ha : c.1.1.bond.axis = LatticeAxis.vertical := congrArg Prod.fst h
    have ht : c.1.1.tip = decide (v.1.1.2 = (n : ℤ)) := congrArg Prod.snd h
    apply he
    apply vertical_port_internal n hn c ha
    simpa only [hv] using ht
  have hinj : (S : Set _).InjOn f := by
    intro c hc d hd h
    obtain ⟨hvc, hec, hfc⟩ := (Finset.mem_filter.mp hc).2
    obtain ⟨hvd, hed, hfd⟩ := (Finset.mem_filter.mp hd).2
    have ha := congrArg Prod.fst h
    have ht := congrArg Prod.snd h
    have hs := incoming_port_side_eq n c d ha ht hfc hfd
    apply (parafermionicCoverFinitePortCoordinatesEmbedding n).injective
    apply Prod.ext
    · exact Subtype.ext (hvc.trans hvd.symm)
    · exact Prod.ext ha (Prod.ext ht hs)
  have hcard := Finset.card_le_card_of_injOn f hmap hinj
  have hT : T.card = 3 := by
    change (Finset.univ.erase d₀).card = 3
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    have hfour : Fintype.card (LatticeAxis × Bool) = 4 := by decide
    rw [Finset.card_univ, hfour]
  rw [hT] at hcard
  exact hcard

end
end PottsContinuity.Thm4
