module

public import ASDExplicitGamma.Main.InverseLowerCenteredBankRow
public import ASDExplicitGamma.Gaussian.Q3Directions

/-! The open-cube two-load response trace of the uncentered q3 directions is the physical inverse
observable trace on the closed cube. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Model
open Algsuperdiff.Section3
open scoped BigOperators

private theorem obs_fderiv_fderiv_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have hfdF : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfdG : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfirst : (fun y => fderiv ℝ (fun z => f z + g z) y) =
      fun y => fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_fun_add (hfdF y) (hfdG y)
  have hsecondF : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have hsecondG : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  change fderiv ℝ (fun y => fderiv ℝ (fun z => f z + g z) y) x = _
  rw [hfirst, fderiv_fun_add (hsecondF x) (hsecondG x)]

private theorem obs_modelCovarianceTrace_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    modelCovarianceTrace (fun y => f y + g y) H x =
      modelCovarianceTrace f H x + modelCovarianceTrace g H x := by
  rw [modelCovarianceTrace_eq_bilinearTraceMap H hH (hf.add hg) x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hf x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hg x,
    obs_fderiv_fderiv_add hf hg x]
  exact (bilinearTraceMap H hH).map_add _ _

/-- The open-cube two-load covariance trace of the uncentered q3 directions is the physical
inverse-observable trace on the closed cube. -/
theorem obs_response_trace_eq_inverse_trace
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let k := pureFluxOpenResponseRestriction n x
    let H (j : ℕ) := pureFluxMainCubeQ3ResponseCoefficient n b L j
    let E (i : Fin 2) := responseFrameEnergyObservable
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ (0, Pi.single i 1)
    let Eall := fun z => ∑ i : Fin 2, E i z
    modelCovarianceTrace Eall H k =
      modelCovarianceTrace (mainInverseObservable n ν σ)
        (pureFluxMainCubeQ3Directions n b L) x := by
  classical
  intro Q k H E Eall
  let U := openCubeSet Q
  let R := pureFluxOpenResponseRestriction n
  let V (j : ℕ) := pureFluxMainCubeQ3Directions n b L j
  let Hc (j : ℕ) := V j
  let Eload (i : Fin 2) := pureFluxBankLoadEnergy n ν σ hν hσ i
  have hV : Summable (fun j => ‖V j‖ ^ 2) := by
    have hA := mainCubeQ3Directions_summable n b L
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet Q), ℝ) inferInstance
      (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L) hA
      (mainCubeH3Value n b L)
  have hHc : Summable (fun j => ‖Hc j‖ ^ 2) :=
    hV
  have hdirs (j : ℕ) : R (Hc j) = H j := by
    simpa only [Hc, V, R] using
      (main_q3_responseCoefficient_eq_restriction n b L j).symm
  have hE (i : Fin 2) : ContDiff ℝ 2 (Eload i) := by
    exact responseFrameEnergyObservable_contDiff
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ (0, Pi.single i 1)
  have hsplit : modelCovarianceTrace Eall H k =
      ∑ i : Fin 2, modelCovarianceTrace (Eload i) H k := by
    have hEall : Eall = fun z => Eload 0 z + Eload 1 z := by
      funext z
      simp [Eall, E, Eload, Fin.sum_univ_two, pureFluxBankLoadEnergy]
    rw [hEall]
    rw [obs_modelCovarianceTrace_add
      (E := ResponseCoefficient U) H
      (main_q3_responseCoefficient_summable n b L)
      (hE 0) (hE 1) k]
    simp only [Fin.sum_univ_two]
  have hbank := pureFlux_bank_covarianceTrace_eq_open_load_sum
    n ν σ hν hσ Hc hHc x
  have hbank' : modelCovarianceTrace
      (bankInverseTraceObservable n ν σ hν hσ) Hc x =
      ∑ i : Fin 2, modelCovarianceTrace (Eload i) H k := by
    have hdirsFun : (fun j => R (Hc j)) = H := by
      funext j
      exact hdirs j
    rw [hdirsFun] at hbank
    simpa only [Eload, k, R] using hbank
  have hobs : mainInverseObservable n ν σ =
      bankInverseTraceObservable n ν σ hν hσ := by
    funext y
    rw [bank_inverse_trace_observable_eq n ν σ hν hσ y]
    simp [mainInverseObservable, bankInverseTrace, Matrix.trace, Fin.sum_univ_two]
    ring
  calc
    modelCovarianceTrace Eall H k =
        ∑ i : Fin 2, modelCovarianceTrace (Eload i) H k := hsplit
    _ = modelCovarianceTrace (bankInverseTraceObservable n ν σ hν hσ) Hc x :=
      hbank'.symm
    _ = modelCovarianceTrace (mainInverseObservable n ν σ) Hc x := by rw [← hobs]

end ASDExplicitGamma.Main
