module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Positive integral bookkeeping for a countable geometric dissection. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

/-- Disjoint selected cells can be enlarged to their complete deterministic
layers before summing any positive energy density. This requires no
independence between the cells and the fields. -/
theorem grouped_disjoint_cell_integrals_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {ι κ : Type*} [Countable ι] [Countable κ]
    (U : ι → Set X) (E : κ → Set X) (layer : ι → κ)
    (hU : ∀ i, MeasurableSet (U i)) (hE : ∀ k, MeasurableSet (E k))
    (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (hsub : ∀ i, U i ⊆ E (layer i)) (f : κ → X → ℝ)
    (hf0 : ∀ k x, 0 ≤ f k x) (hfi : ∀ k, IntegrableOn (f k) (E k) μ) :
    (∑' i, ENNReal.ofReal (∫ x in U i, f (layer i) x ∂μ)) ≤
      ∑' k, ENNReal.ofReal (∫ x in E k, f k x ∂μ) := by
  classical
  have he (A : Set X) (g : X → ℝ) :
      (fun x => ENNReal.ofReal (A.indicator g x))=A.indicator (fun x => ENNReal.ofReal (g x)) := by
    funext x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx,ENNReal.ofReal_zero]
  have hUi (i : ι) : Integrable (U i |>.indicator (f (layer i))) μ :=
    (integrable_indicator_iff (hU i)).mpr ((hfi (layer i)).mono_set (hsub i))
  have hEi (k : κ) : Integrable (E k |>.indicator (f k)) μ :=
    (integrable_indicator_iff (hE k)).mpr (hfi k)
  have hUm (i : ι) : AEMeasurable ((U i).indicator (fun x => ENNReal.ofReal (f (layer i) x))) μ := by
    rw [← he]
    exact (hUi i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hEm (k : κ) : AEMeasurable ((E k).indicator (fun x => ENNReal.ofReal (f k x))) μ := by
    rw [← he]
    exact (hEi k).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hUeq (i : ι) : ENNReal.ofReal (∫ x in U i, f (layer i) x ∂μ)=
      ∫⁻ x, (U i).indicator (fun x => ENNReal.ofReal (f (layer i) x)) x ∂μ := by
    rw [lintegral_indicator (hU i)]
    exact ofReal_integral_eq_lintegral_ofReal ((hfi (layer i)).mono_set (hsub i))
      (Filter.Eventually.of_forall (fun x => hf0 _ x))
  have hEeq (k : κ) : ENNReal.ofReal (∫ x in E k, f k x ∂μ)=
      ∫⁻ x, (E k).indicator (fun x => ENNReal.ofReal (f k x)) x ∂μ := by
    rw [lintegral_indicator (hE k)]
    exact ofReal_integral_eq_lintegral_ofReal (hfi k) (Filter.Eventually.of_forall (fun x => hf0 _ x))
  simp_rw [hUeq,hEeq]
  rw [← lintegral_tsum hUm,← lintegral_tsum hEm]
  apply lintegral_mono
  intro x
  change (∑' i, (U i).indicator (fun x => ENNReal.ofReal (f (layer i) x)) x) ≤
    ∑' k, (E k).indicator (fun x => ENNReal.ofReal (f k x)) x
  by_cases hx : ∃ i, x ∈ U i
  · obtain ⟨i,hi⟩ := hx
    rw [tsum_eq_single i]
    · rw [Set.indicator_of_mem hi]
      have hh := ENNReal.le_tsum (f := fun k => (E k).indicator (fun x => ENNReal.ofReal (f k x)) x) (layer i)
      rw [Set.indicator_of_mem (hsub i hi)] at hh
      exact hh
    · intro j hji
      exact Set.indicator_of_notMem (fun hj => Set.disjoint_left.mp (hdisj hji) hj hi) _
  · have hz (i : ι) : (U i).indicator (fun x => ENNReal.ofReal (f (layer i) x)) x=0 :=
      Set.indicator_of_notMem (fun hi => hx ⟨i,hi⟩) _
    simp only [hz,tsum_zero,zero_le]

end
end ASDExplicitGamma.Inverse
