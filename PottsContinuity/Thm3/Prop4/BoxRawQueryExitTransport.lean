module

public import PottsContinuity.Thm3.Prop4.RawQueryTubeSides
public import PottsContinuity.Thm3.Prop4.MarkedBoxRawSourceIdentity

@[expose] public section

namespace PottsContinuity.Thm3.Prop4
open PD.FK PD.RCInfinite PlanarTopology
noncomputable section
local instance boxRawQueryExitTransportEdgeEq (n : ℕ) :
    DecidableEq (finiteLatticeGraph (box n)).edgeSet := Classical.decEq _

/-- Every endpoint of a transported original query has an original endpoint
preimage with the identical lattice label. -/
theorem boxMappedQuery_endpoint_preimage (n : ℕ)
    (Q : Configuration (finiteLatticeGraph (box n)))
    (e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet)
    (he : e ∈ configurationIso (boxTubeRectangleIso n) Q)
    (z : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (hz : z ∈ e.val) :
    ∃ e₀ ∈ Q, ∃ z₀ : (box n : Set LatticeVertex), z₀ ∈ e₀.val ∧ z₀.val = z.val := by
  change e ∈ Q.map (configurationIsoEdgeEquiv (boxTubeRectangleIso n)).toEmbedding at he
  obtain ⟨e₀,he₀,rfl⟩ := Finset.mem_map.mp he
  change z ∈ Sym2.map (boxTubeRectangleIso n) e₀.val at hz
  obtain ⟨z₀,hz₀,rfl⟩ := Sym2.mem_map.mp hz
  exact ⟨e₀,he₀,z₀,hz₀,rfl⟩

/-- Signed lower raw-query exit heights on the exact sampled rectangle
carrier follow from the unchanged source box trace event. -/
theorem sourceBox_lower_raw_query_exit_height_le
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 < R)
    (u v : (box n : Set LatticeVertex)) (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (t b : ℝ) (hut : (u.val.2 : ℝ) = t*u.val.1+b) (hvt : (v.val.2 : ℝ) = t*v.val.1+b)
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v)
    (htrace : ∀ z ∈ markedLowerBoxTrace n u v A,
      z.val ∈ radiusTube n R u.val v.val ∨ (z.val.2 : ℝ)-(t*z.val.1+b) ≤ 0)
    (e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet)
    (he : e ∈ sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val)
      (configurationIso (boxTubeRectangleIso n) A))
    (z : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (hz : z ∈ e.val)
    (hout : z.val ∉ radiusTube n R u.val v.val) :
    (z.val.2 : ℝ)-(t*z.val.1+b) ≤ -R := by
  have hm : configurationIso (boxTubeRectangleIso n) (markedLowerBoxRawReveal n u v A) =
      sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
        (rectangleLowerDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val)
        (configurationIso (boxTubeRectangleIso n) A) := by
    rw [sampledRawDualReveal_lower_arc_eq]
    exact (configurationIso (boxTubeRectangleIso n)).apply_symm_apply _
  rw [← hm] at he
  obtain ⟨e₀,he₀,z₀,hz₀,hval⟩ := boxMappedQuery_endpoint_preimage n _ e he z hz
  have h := markedLowerBoxRawReveal_outside_endpoint_height_le n hn R hR u v hu hv t b hut hvt A hA htrace e₀ he₀ z₀ hz₀ (by simpa only [hval] using hout)
  simpa only [hval] using h

/-- Signed upper raw-query exit heights preserve every original source
label and the very same upper trace event. -/
theorem sourceBox_upper_raw_query_exit_height_ge
    (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 < R)
    (u v : (box n : Set LatticeVertex)) (hu : u.val.1 = -(n : ℤ)) (hv : v.val.1 = (n : ℤ))
    (t b : ℝ) (hut : (u.val.2 : ℝ) = t*u.val.1+b) (hvt : (v.val.2 : ℝ) = t*v.val.1+b)
    (A : Configuration (finiteLatticeGraph (box n)))
    (hA : ActualConnected (finiteLatticeGraph (box n)) A u v)
    (htrace : ∀ z ∈ markedUpperBoxTrace n u v A,
      z.val ∈ radiusTube n R u.val v.val ∨ 0 ≤ (z.val.2 : ℝ)-(t*z.val.1+b))
    (e : (rectangleGraph (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)).edgeSet)
    (he : e ∈ sampledRawDualReveal (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)
      (rectangleUpperDualArc (-(n : ℤ),-(n : ℤ)) (2*n) (2*n) u.val v.val)
      (configurationIso (boxTubeRectangleIso n) A))
    (z : RectangleVertex (-(n : ℤ),-(n : ℤ)) (2*n) (2*n)) (hz : z ∈ e.val)
    (hout : z.val ∉ radiusTube n R u.val v.val) :
    R ≤ (z.val.2 : ℝ)-(t*z.val.1+b) := by
  rw [← markedUpperBoxRawReveal_eq_source_upper n u v A] at he
  obtain ⟨e₀,he₀,z₀,hz₀,hval⟩ := boxMappedQuery_endpoint_preimage n _ e he z hz
  have h := markedUpperBoxRawReveal_outside_endpoint_height_ge n hn R hR u v hu hv t b hut hvt A hA htrace e₀ he₀ z₀ hz₀ (by simpa only [hval] using hout)
  simpa only [hval] using h

end
end PottsContinuity.Thm3.Prop4
