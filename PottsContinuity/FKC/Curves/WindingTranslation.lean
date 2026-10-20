-- Adapted from FKconvergence, an earlier formalization by the same author that is not publicly
-- accessible (see `related_formalizations` in formalization.yaml): file `Curves/WindingTranslation.lean`, with
-- module and namespace relocated and declarations not used here removed.
module

public import PottsContinuity.FKC.Curves.Winding
public import Mathlib.Tactic

@[expose] public section

namespace PottsContinuity.FKC

open Set
open scoped unitInterval
noncomputable section

def translateLoop {a : ℂ} (γ : Path a a) (c : ℂ) : Path (a - c) (a - c) :=
  γ.map (continuous_id.sub (continuous_const : Continuous (fun _ : ℂ => c)))

@[simp] theorem translateLoop_apply {a : ℂ} (γ : Path a a) (c : ℂ) (t : I) :
    translateLoop γ c t = γ t - c := rfl

theorem not_mem_range_translateLoop {a z c : ℂ} (γ : Path a a)
    (hz : z ∉ range γ) : z - c ∉ range (translateLoop γ c) := by
  rintro ⟨t, ht⟩
  apply hz ⟨t, ?_⟩
  have ht' : γ t - c = z - c := by simpa [translateLoop] using ht
  have heq := congrArg (fun w : ℂ => w + c) ht'
  simpa using heq

theorem normalizedLoop_translateLoop_apply {a z c : ℂ} (γ : Path a a)
    (hz : z ∉ range γ) (t : I) :
    normalizedLoop (translateLoop γ c) (z - c)
      (not_mem_range_translateLoop γ hz) t = normalizedLoop γ z hz t := by
  apply Subtype.ext
  simp only [normalizedLoop_coe_apply, translateLoop_apply]
  rw [show γ t - c - (z - c) = γ t - z by ring]

theorem windingNumber_translateLoop {a z c : ℂ} (γ : Path a a)
    (hz : z ∉ range γ) :
    windingNumber (translateLoop γ c) (z - c)
      (not_mem_range_translateLoop γ hz) = windingNumber γ z hz := by
  let F : C(I × I, Circle) :=
    ⟨fun u => normalizedLoop γ z hz u.2,
      (normalizedLoop γ z hz).continuous.comp continuous_snd⟩
  unfold windingNumber
  exact Circle.degree_eq_of_homotopy
    (normalizedLoop (translateLoop γ c) (z - c) (not_mem_range_translateLoop γ hz))
    (normalizedLoop γ z hz) F
    (fun t => (normalizedLoop_translateLoop_apply γ hz t).symm)
    (fun _ => rfl)
    (fun s => by simp [F, Path.source, Path.target])

end
end PottsContinuity.FKC
