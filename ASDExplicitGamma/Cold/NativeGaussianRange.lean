module

public import ASDExplicitGamma.Cold.NativeGaussianProcess
public import ASDExplicitGamma.Model.Q3Cov

/-! # Sharp coordinate range of the frozen product-q3 Gaussian stream -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The frozen q3 covariance has exact unit diagonal. -/
theorem cold_q3_cov_zero : q3Cov 0 = 1 := by
  unfold q3Cov
  simpa only [add_zero,← pow_two] using Model.q3Kernel_sq_integral

/-- Product covariance vanishes when either coordinate is separated by one. -/
theorem cold_q3_cov_product_zero {x y : Vec 2}
    (hsep : ∃ i : Fin 2, 1 ≤ |(x-y) i|) : q3Cov ((x-y) 0)*q3Cov ((x-y) 1) = 0 := by
  obtain ⟨i,hi⟩ := hsep
  fin_cases i
  · change 1 ≤ |(x-y) 0| at hi
    rw [Model.q3Cov_zero_of_abs_ge_one (u := (x-y) 0) hi,zero_mul]
  · change 1 ≤ |(x-y) 1| at hi
    rw [Model.q3Cov_zero_of_abs_ge_one (u := (x-y) 1) hi,mul_zero]

/-- The exact one-point stream law of the model. -/
theorem cold_zeroShell_point_law (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (x : Vec 2) :
    Measure.map (fun j : ShellField 2 => j x 1 0) (ShellField.zeroShellLaw M.P).toMeasure =
      gaussianReal 0 (Real.toNNReal (h^2)) := by
  have hlaw := hM.2 1 (fun _ => x) (fun _ => 1)
  simpa only [Fin.sum_univ_one,one_mul,sub_self,Pi.zero_apply,cold_q3_cov_zero,mul_one] using hlaw

/-- Separated point streams have the exact centered Gaussian sum law with variance 2h². -/
theorem cold_zeroShell_separated_sum_law (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {x y : Vec 2} (hsep : ∃ i : Fin 2, 1 ≤ |(x-y) i|) :
    Measure.map (fun j : ShellField 2 => j x 1 0+j y 1 0) (ShellField.zeroShellLaw M.P).toMeasure =
      gaussianReal 0 (Real.toNNReal (2*h^2)) := by
  have hxy := cold_q3_cov_product_zero hsep
  have hyx : q3Cov ((y-x) 0)*q3Cov ((y-x) 1) = 0 := by
    rw [← neg_sub x y]
    simpa only [Pi.neg_apply,Model.q3Cov_even] using hxy
  have hlaw := hM.2 2 ![x,y] (fun _ => 1)
  simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul,
    sub_self,Pi.zero_apply,cold_q3_cov_zero,mul_one,hxy,hyx,add_zero,zero_add] at hlaw
  convert hlaw using 1
  congr 2
  ring

/-- Exact real variance can be read directly from an actual Gaussian pushforward law. -/
theorem cold_variance_of_gaussian_law {Ω : Type*} [MeasurableSpace Ω] {μprob : Measure Ω}
    {X : Ω → ℝ} {v : ℝ} (hX : AEMeasurable X μprob) (hv : 0 ≤ v)
    (hlaw : Measure.map X μprob = gaussianReal 0 (Real.toNNReal v)) : Var[X;μprob] = v := by
  rw [← variance_id_map hX,hlaw,variance_id_gaussianReal,Real.coe_toNNReal _]
  exact hv

/-- Separated stream values are uncorrelated at the sharp product-q3 coordinate range. -/
theorem cold_zeroShell_covariance_zero (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {x y : Vec 2} (hsep : ∃ i : Fin 2, 1 ≤ |(x-y) i|) :
    cov[fun j : ShellField 2 => j x 1 0,fun j : ShellField 2 => j y 1 0;(ShellField.zeroShellLaw M.P).toMeasure] = 0 := by
  let μprob := (ShellField.zeroShellLaw M.P).toMeasure
  let X := fun j : ShellField 2 => j x 1 0
  let Y := fun j : ShellField 2 => j y 1 0
  have hproc := cold_zeroShell_isGaussianProcess M h hM
  have hX := hproc.hasGaussianLaw_eval x
  have hY := hproc.hasGaussianLaw_eval y
  have hvx : Var[X;μprob] = h^2 := cold_variance_of_gaussian_law hX.aemeasurable (sq_nonneg h)
    (cold_zeroShell_point_law M h hM x)
  have hvy : Var[Y;μprob] = h^2 := cold_variance_of_gaussian_law hY.aemeasurable (sq_nonneg h)
    (cold_zeroShell_point_law M h hM y)
  have hvs : Var[X+Y;μprob] = 2*h^2 := cold_variance_of_gaussian_law
    (hX.aemeasurable.add hY.aemeasurable) (by positivity) (cold_zeroShell_separated_sum_law M h hM hsep)
  have hv := variance_add hX.memLp_two hY.memLp_two
  change Var[X+Y;μprob] = Var[X;μprob]+2*cov[X,Y;μprob]+Var[Y;μprob] at hv
  rw [hvx,hvy,hvs] at hv
  change cov[X,Y;μprob] = 0
  linarith only [hv]

end ASDExplicitGamma.Cold
