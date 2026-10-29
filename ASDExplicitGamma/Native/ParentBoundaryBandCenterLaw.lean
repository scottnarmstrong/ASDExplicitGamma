module

public import ASDExplicitGamma.Native.ParentBoundaryShearTrace
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandBank
public import ASDExplicitGamma.Gaussian.GaussCentering
public import ASDExplicitGamma.Gaussian.Q3ModelCovariance
public import ASDExplicitGamma.Gaussian.NormalScaledMoments

/-! The actual scalar center of a finite band has the summed physical variance. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Response Scalar Gaussian Inverse Triadic Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open scoped ENNReal
noncomputable section

/-- Exact scalar normal law of the actual fresh physical band at any point.
Only independence of distinct SHELLS is used; spatial images remain coupled. -/
theorem parent_boundary_band_point_law
    {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (x : K) :
    (Cutoff.cutoffSampleLaw M).toMeasure.map (fun ω => modelBand K k ω x)=
      gaussianReal 0 (Real.toNNReal (∑ i,(q3ModelAmplitude M h (k i))^2)) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun i (ω : Cutoff.CutoffSample 2) => shellFieldScalarRestriction K (ω.1 (k i)) x
  let s := fun i => Real.toNNReal ((q3ModelAmplitude M h (k i))^2)
  have hX (i : Fin b) : Measurable (X i) :=
    (ContinuousMap.evalCLM ℝ x).continuous.measurable.comp
      ((measurable_shellFieldScalarRestriction K).comp ((measurable_pi_apply (k i)).comp measurable_subtype_coe))
  have hi : iIndepFun X μ :=
    (iIndepFun_shellRestrictions K M k hk).comp (fun _ => fun f : C(K,ℝ) => f x)
      (fun _ => (ContinuousMap.evalCLM ℝ x).continuous.measurable)
  have hlaw (i : Fin b) : μ.map (X i)=gaussianReal 0 (s i) := by
    have hm := shellMarginalLaw_finite_observation M h hM (k i) (fun _ : Fin 1 => x) (fun _ => 1)
    simp only [Fin.sum_univ_one,one_mul,sub_self,zero_div,ASDExplicitGamma.Model.q3Cov_at_zero,mul_one] at hm
    have hc : μ.map (fun ω : Cutoff.CutoffSample 2 => ω.1 (k i))=
        (ShellField.shellMarginalLaw M.P (k i)).toMeasure := by
      simpa only [sub_add_cancel] using Model.map_freshShell_eq_shellMarginalLaw M (k i-1)
    have he : X i=(fun j : ShellField 2 => j x.1 1 0) ∘ (fun ω : Cutoff.CutoffSample 2 => ω.1 (k i)) := by
      funext ω
      rfl
    rw [he,←Measure.map_map (ShellField.measurable_eval_entry x.1 1 0)
      ((measurable_pi_apply (k i)).comp measurable_subtype_coe),hc]
    exact hm
  have hh := independent_gaussian_sum_law μ X s hX hi hlaw
  have he : (fun ω => modelBand K k ω x)=(fun ω => ∑ i,X i ω) := by
    funext ω
    simp only [modelBand,ContinuousMap.sum_apply,X]
  rw [he]
  have hs : (∑ i,s i)=Real.toNNReal (∑ i,(q3ModelAmplitude M h (k i))^2) := by
    dsimp only [s]
    exact (Real.toNNReal_sum_of_nonneg (fun i _ => sq_nonneg (q3ModelAmplitude M h (k i)))).symm
  simpa only [hs] using hh

end
end ASDExplicitGamma.Native
