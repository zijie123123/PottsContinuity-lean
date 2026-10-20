module

public import PottsContinuity.Thm3.RSW.StripEventMonotone
public import PottsContinuity.Thm3.RSW.StripEvents

/-! # Positive probability of nonempty increasing finite-support strip events -/

@[expose] public section

namespace PottsContinuity.RSW
open MeasureTheory PD.FK

/-- A nonempty increasing event with finite edge support has positive
probability in every genuine top-wired strip limit. The finite-window witness
opens the entire window and matches the all-open state on the event support. -/
theorem strip_finiteSupport_event_pos
    (θ : Parameters) (n : ℕ)
    (μ : Measure (StripConfiguration n)) (hμ : IsTopWiredStripLimit θ n 0 μ)
    (F : Finset (stripGraph n).edgeSet) (E : Set (StripConfiguration n))
    (hsupport : ∀ ω η : StripConfiguration n,
      (∀ e ∈ F, ω e = η e) → (ω ∈ E ↔ η ∈ E))
    (hupper : IsUpperSet E) (hne : E.Nonempty) : 0 < μ.real E := by
  classical
  obtain ⟨m,hm⟩ := (eventually_stripWindow_finset_edge_lift n F).exists
  let G := squareLattice.induce (stripWindow n m : Set (ℤ × ℤ))
  let StripFiniteSupport_edgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
  let C : Configuration G := Finset.univ
  let η := stripPlaneRestriction n (stripWindowPlaneConfiguration n m C)
  have hη : ∀ e ∈ F, η e = true := by
    intro e he
    obtain ⟨f,hf⟩ := hm e he
    simp only [η,stripPlaneRestriction,stripWindowPlaneConfiguration,decide_eq_true_eq]
    apply Finset.mem_map.mpr
    refine ⟨f,Finset.mem_univ _,?_⟩
    apply Subtype.ext
    exact hf
  have htop : (fun _ => true) ∈ E := by
    obtain ⟨ω,hω⟩ := hne
    apply hupper (show ω ≤ fun _ => true from fun _ => Bool.le_true _) hω
  have hEη : η ∈ E := (hsupport (fun _ => true) η
    (fun e he => (hη e he).symm)).mp htop
  exact strip_event_pos_of_finite_window_witness θ n m μ hμ E
    (strip_isClopen_of_finite_support n F E hsupport) hupper C hEη

end PottsContinuity.RSW
