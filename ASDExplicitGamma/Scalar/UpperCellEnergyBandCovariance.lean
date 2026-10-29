module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandGaussian
public import ASDExplicitGamma.Gaussian.DerivativeLaw
public import Mathlib.Probability.Independence.Integration

/-! Exact covariance of the actual weighted finite-band stored jets. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Gaussian
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped BigOperators ENNReal
noncomputable section

/-- The finite actual shell carrier family is independent. -/
theorem upper_cell_band_shells_independent {b : ℕ} (M : ABKModel 2)
    (k : Fin b → ℤ) (hk : Function.Injective k) :
    iIndepFun (fun i => fun ω : Cutoff.CutoffSample 2 => ω.val (k i))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
  iIndepFun_of_map _ _ Subtype.val measurable_subtype_coe
    (Cutoff.map_cutoffSampleLaw_val M) (fun i ω => ω (k i))
    (fun i => measurable_pi_apply (k i)) ((Model.shellLevels_independent M).precomp hk)

/-- Square integrability of the literal stored derivative on the actual law. -/
theorem upper_cell_shell_jet_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ)
    (o : ShellDerivativeObservation) :
    MemLp (fun ω : Cutoff.CutoffSample 2 => shellDerivativeEval o (ω.val k)) 2
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hmp : MeasurePreserving (fun ω : Cutoff.CutoffSample 2 => ω.val k)
      (Cutoff.cutoffSampleLaw M).toMeasure (ShellField.shellMarginalLaw M.P k).toMeasure :=
    ⟨(measurable_pi_apply k).comp measurable_subtype_coe,upper_cell_shell_marginal M k⟩
  exact ((q3Shell_stored_derivatives_gaussian M h hM k).memLp o 2 (by simp)).comp_measurePreserving hmp

/-- Every band shell derivative is centered on the original sample space. -/
theorem upper_cell_shell_jet_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (k : ℤ)
    (o : ShellDerivativeObservation) :
    (∫ ω : Cutoff.CutoffSample 2,shellDerivativeEval o (ω.val k)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = 0 := by
  obtain ⟨v,hv⟩ := (q3Shell_stored_derivatives_gaussian M h hM k).map_single o
  have he : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => shellDerivativeEval o (ω.val k)) = gaussianReal 0 v := by
    rw [← hv,← upper_cell_shell_marginal M k,
      Measure.map_map (shellDerivativeEval_continuous o).measurable
        ((measurable_pi_apply k).comp measurable_subtype_coe)]
    rfl
  exact integral_of_map_gaussianReal
    (((shellDerivativeEval_continuous o).measurable.comp
      ((measurable_pi_apply k).comp measurable_subtype_coe)).aemeasurable) he

/-- Cross-shell covariance vanishes by actual shell independence, while
same-shell covariance is the physical differentiated q3 covariance. -/
theorem upper_cell_shell_jet_product {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (i j : Fin b)
    (o p : ShellDerivativeObservation) :
    (∫ ω : Cutoff.CutoffSample 2,
      shellDerivativeEval o (ω.val (k i))*shellDerivativeEval p (ω.val (k j))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      if i=j then q3ShellDerivativeCovariance M h (k i) o p else 0 := by
  split_ifs with hij
  · subst j
    have hm : Measurable (fun x => shellDerivativeEval o x*shellDerivativeEval p x) :=
      (shellDerivativeEval_continuous o).measurable.mul (shellDerivativeEval_continuous p).measurable
    have ht := integral_map (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (f := fun x => shellDerivativeEval o x*shellDerivativeEval p x)
      (((measurable_pi_apply (k i)).comp measurable_subtype_coe) :
        Measurable (fun ω : Cutoff.CutoffSample 2 => ω.val (k i))).aemeasurable
      hm.aestronglyMeasurable
    simp only [Function.comp_def] at ht
    rw [upper_cell_shell_marginal M (k i)] at ht
    exact ht.symm.trans (q3Shell_stored_derivative_covariance M h hM (k i) o p)
  · have hi := ((upper_cell_band_shells_independent M k hk).indepFun hij).comp
      (shellDerivativeEval_continuous o).measurable (shellDerivativeEval_continuous p).measurable
    have ho := upper_cell_shell_jet_memLp M h hM (k i) o
    have hp := upper_cell_shell_jet_memLp M h hM (k j) p
    have hh := hi.integral_mul_eq_mul_integral ho.aestronglyMeasurable hp.aestronglyMeasurable
    change (∫ ω : Cutoff.CutoffSample 2,
      shellDerivativeEval o (ω.val (k i))*shellDerivativeEval p (ω.val (k j))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _ at hh
    simp only [Function.comp_apply] at hh
    rw [upper_cell_shell_jet_mean M h hM (k i) o,zero_mul] at hh
    exact hh

/-- Exact full-band covariance sum, with squared weights and every mixed jet.
No shellwise supremum bound or fictitious single-shell law is substituted. -/
theorem upper_cell_band_jet_covariance {b : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (w : Fin b → ℝ)
    (o p : ShellDerivativeObservation) :
    (∫ ω,upperCellBandJet k w o ω*upperCellBandJet k w p ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      ∑ i,w i^2*q3ShellDerivativeCovariance M h (k i) o p := by
  have hint (i j : Fin b) : Integrable (fun ω : Cutoff.CutoffSample 2 =>
      (w i*w j)*(shellDerivativeEval o (ω.val (k i))*shellDerivativeEval p (ω.val (k j))))
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    ((upper_cell_shell_jet_memLp M h hM (k i) o).integrable_mul
      (upper_cell_shell_jet_memLp M h hM (k j) p)).const_mul _
  have heq : (fun ω => upperCellBandJet k w o ω*upperCellBandJet k w p ω) =
      (fun ω : Cutoff.CutoffSample 2 => ∑ i,∑ j,
        (w i*w j)*(shellDerivativeEval o (ω.val (k i))*shellDerivativeEval p (ω.val (k j)))) := by
    funext ω
    unfold upperCellBandJet
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq,integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  simp only [integral_const_mul,upper_cell_shell_jet_product M h hM k hk]
  simp [mul_ite,pow_two]

end
end ASDExplicitGamma.Scalar
