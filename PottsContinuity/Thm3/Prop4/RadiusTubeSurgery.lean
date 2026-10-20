module

public import PottsContinuity.Thm3.Prop4.RadiusTube
public import PottsContinuity.Thm3.Prop4.TubeSurgery

/-!
# Closing costs for the corrected wider tube

The radius-four enlargement restores the source square-arm cutoff while
retaining a parameter-only exp(-C n^ε) surgery cost. The original tube and
all previous declarations are preserved.
-/

@[expose] public section

open MeasureTheory

namespace PottsContinuity.Thm3.Prop4

noncomputable section

local instance radiusSurgeryEdgeFintype (n : ℕ) :
    Fintype (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Fintype.ofFinite _
local instance radiusSurgeryEdgeDecidableEq (n : ℕ) :
    DecidableEq (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := Classical.decEq _

/-- Original finite-box edges in the literal radius-parametrized cut. -/
def radiusTubeCutEdges (n : ℕ) (r : ℝ) (u v : ℤ × ℤ) (k : ℤ) :
    Finset (squareLattice.induce (box n : Set (ℤ × ℤ))).edgeSet := by
  classical
  exact Finset.univ.filter (fun e => Sym2.map Subtype.val e.val ∈ radiusTubeCut n r u v k)

theorem radiusTubeCutEdges_card_le {n : ℕ} (hn : 1 ≤ n) (r : ℝ)
    (u v : ℤ × ℤ) (hu : u ∈ box n) (hv : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = (n : ℤ)) (k : ℤ) :
    (radiusTubeCutEdges n r u v k).card ≤ 4*⌈r⌉₊+1 := by
  classical
  obtain ⟨t,b,ht,hu',hv'⟩ := inductionTube_supporting_line hn u v hu hv huX hvX
  let f : {e // e ∈ radiusTubeCutEdges n r u v k} →
      {e // e ∈ radiusTubeCut n r u v k} := fun e =>
    ⟨Sym2.map Subtype.val e.val.val,(Finset.mem_filter.mp e.property).2⟩
  have hinj : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    apply Subtype.ext
    exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hinj
  have hc' : (radiusTubeCutEdges n r u v k).card ≤ (radiusTubeCut n r u v k).card := by
    simpa using hc
  exact hc'.trans (radiusTubeCut_card_le n r u v t b ht hu' hv' k)

/-- Every radius ≥1 has the same parameter-only linear-exponent closing cost. -/
theorem radiusTube_closing_cost_lower (θ : PD.FK.Parameters) {n : ℕ} (hn : 1 ≤ n)
    (r : ℝ) (hr : 1 ≤ r) (u v : ℤ × ℤ) (hu : u ∈ box n) (hv : v ∈ box n)
    (huX : u.1 = -(n : ℤ)) (hvX : v.1 = (n : ℤ)) (k : ℤ) :
    Real.exp (-tubeClosingCoefficient θ*r) ≤
      (1-PD.FK.edgeParameter θ)^(radiusTubeCutEdges n r u v k).card := by
  have hceil := Nat.ceil_lt_add_one (by linarith only [hr] : 0 ≤ r)
  have hc := radiusTubeCutEdges_card_le hn r u v hu hv huX hvX k
  have hcR : ((radiusTubeCutEdges n r u v k).card : ℝ) ≤ 4*(⌈r⌉₊ : ℝ)+1 := by
    exact_mod_cast hc
  have hbound : ((radiusTubeCutEdges n r u v k).card : ℝ) ≤ 9*r := by
    linarith only [hcR,hceil,hr]
  have hs := PD.FK.one_sub_edgeParameter_pos θ
  have hlog := Real.log_neg hs
    (show 1-PD.FK.edgeParameter θ < 1 by linarith only [PD.FK.edgeParameter_pos θ])
  calc
    _ ≤ Real.exp ((radiusTubeCutEdges n r u v k).card*
        Real.log (1-PD.FK.edgeParameter θ)) := by
      apply Real.exp_le_exp.mpr
      unfold tubeClosingCoefficient
      nlinarith only [mul_le_mul_of_nonpos_right hbound hlog.le]
    _ = _ := by rw [Real.exp_nat_mul,Real.exp_log hs]

end

end PottsContinuity.Thm3.Prop4
