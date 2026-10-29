module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankCentering

/-! The physical bank observable is exactly the two open-cube pure-flux energies. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Cold ASDExplicitGamma.Gaussian
open scoped BigOperators
noncomputable section

local instance pureFluxBankLoadsFiniteMeasure (k : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 k))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 k)).isFiniteMeasure_restrict_volume

def pureFluxBankLoadEnergy (k : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (i : Fin 2) : ResponseCoefficient (openCubeSet (originCube 2 k)) → ℝ :=
  responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 k))
    (volume_openCubeSet_originCube_toReal_pos (d := 2) k) ν σ hν hσ (0, Pi.single i 1)

theorem pureFlux_bank_load_energy_eq (k : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (f : C(closure (cubeSet (originCube 2 k)), ℝ)) (i : Fin 2) :
    pureFluxBankLoadEnergy k ν σ hν hσ i (pureFluxOpenResponseRestriction k f) =
      σ*(coarseBlockMatrix (cubeSet (originCube 2 k))
        (responsePlanarCoefficientField ν
          (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ f))).lowerRight i i := by
  let Q := originCube 2 k
  let U := openCubeSet Q
  let K := pureFluxOpenResponseRestriction k f
  let a := responsePlanarCoefficientField ν
    (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ f)
  let af := responseFramePlanarCoefficientField ν σ K
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ K
  have hE : pureFluxBankLoadEnergy k ν σ hν hσ i K =
      2*Mu U (0, Pi.single i 1) af := by
    unfold pureFluxBankLoadEnergy
    rw [lemmaV_observable_eq_twice_muCandidate, ← lemmaV_responseSystem_eq_canonical]
    congr 1
    exact lemmaV_canonical_muCandidate_eq_Mu (isOpenBoundedConvexDomain_openCubeSet Q)
      hEll (volume_openCubeSet_originCube_toReal_pos (d := 2) k) _
  have hEllClosed := responsePlanarCoefficientField_isElliptic
    (measurableSet_cubeSet Q) ν hν
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ f)
  have hcoarse : coarseBlockMatrix U af = frameMatrix σ (coarseBlockMatrix (cubeSet Q) a) := by
    rw [coarseBlockMatrix_congr_of_ae_eq (pureFluxOpenResponseRestriction_frame_ae k ν σ f hσ)]
    rw [← cold_coarse_cube_open Q (σ⁻¹ • a)]
    exact cold_coarse_frame hν hEllClosed hσ
  rw [hE, ← coarseBlockMatrix_lowerRight_apply_diag, hcoarse]
  rfl

theorem pureFlux_bank_observable_eq_open_load_sum (k : ℤ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (f : C(closure (cubeSet (originCube 2 k)), ℝ)) :
    bankInverseTraceObservable k ν σ hν hσ f =
      ∑ i : Fin 2, pureFluxBankLoadEnergy k ν σ hν hσ i
        (pureFluxOpenResponseRestriction k f) := by
  rw [bank_inverse_trace_observable_eq]
  unfold bankInverseTrace
  exact Finset.sum_congr rfl fun i _ => (pureFlux_bank_load_energy_eq k ν σ hν hσ f i).symm
private theorem pureFluxBank_fderiv_fderiv_add
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

private theorem pureFluxBank_modelCovarianceTrace_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    modelCovarianceTrace (fun y => f y + g y) H x =
      modelCovarianceTrace f H x + modelCovarianceTrace g H x := by
  rw [modelCovarianceTrace_eq_bilinearTraceMap H hH (hf.add hg) x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hf x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hg x,
    pureFluxBank_fderiv_fderiv_add hf hg x]
  exact (bilinearTraceMap H hH).map_add _ _

private theorem pureFluxBank_secondDirectionalDerivative_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F) (x v : E) :
    secondDirectionalDerivative (fun y => f (L y)) x v =
      secondDirectionalDerivative f (L x) (L v) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfirst (y : E) :
      fderiv ℝ (fun z => f (L z)) y = (fderiv ℝ f (L y)).comp L :=
    (hfd (L y)).hasFDerivAt.comp y L.hasFDerivAt |>.fderiv
  have hdir : (fun y => fderiv ℝ (fun z => f (L z)) y v) =
      fun y => fderiv ℝ f (L y) (L v) := by
    funext y
    rw [hfirst]
    rfl
  let g : F → ℝ := fun y => fderiv ℝ f y (L v)
  have hg : DifferentiableAt ℝ g (L x) :=
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
      contDiff_const).differentiable_one.differentiableAt
  have hsecond := hg.hasFDerivAt.comp x L.hasFDerivAt
  have hsecond' : fderiv ℝ (fun y : E => g (L y)) x =
      (fderiv ℝ g (L x)).comp L := by
    simpa only [Function.comp_def] using hsecond.fderiv
  unfold secondDirectionalDerivative
  rw [hdir]
  change fderiv ℝ (fun y => g (L y)) x v =
    fderiv ℝ (fun y => fderiv ℝ f y (L v)) (L x) (L v)
  rw [hsecond']
  rfl

private theorem pureFluxBank_modelCovarianceTrace_comp_linear
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F → ℝ) (hf : ContDiff ℝ 2 f) (L : E →L[ℝ] F)
    (H : ℕ → E) (x : E) :
    modelCovarianceTrace (fun y => f (L y)) H x =
      modelCovarianceTrace f (fun j => L (H j)) (L x) := by
  unfold modelCovarianceTrace
  apply tsum_congr
  intro j
  exact pureFluxBank_secondDirectionalDerivative_comp_linear f hf L x (H j)

/-- The actual bank covariance splits over exactly its two pure-flux loads. -/
theorem pureFlux_bank_covarianceTrace_eq_open_load_sum (k : ℤ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (H : ℕ → C(closure (cubeSet (originCube 2 k)), ℝ))
    (hH : Summable (fun j => ‖H j‖^2))
    (x : C(closure (cubeSet (originCube 2 k)), ℝ)) :
    modelCovarianceTrace (bankInverseTraceObservable k ν σ hν hσ) H x =
      ∑ i : Fin 2, modelCovarianceTrace (pureFluxBankLoadEnergy k ν σ hν hσ i)
        (fun j => pureFluxOpenResponseRestriction k (H j))
        (pureFluxOpenResponseRestriction k x) := by
  let L := pureFluxOpenResponseRestriction k
  let E := pureFluxBankLoadEnergy k ν σ hν hσ
  have hE (i : Fin 2) : ContDiff ℝ 2 (E i) :=
    responseFrameEnergyObservable_contDiff _ _ ν σ hν hσ _
  have heq : bankInverseTraceObservable k ν σ hν hσ =
      fun z => E 0 (L z)+E 1 (L z) := by
    funext z
    rw [pureFlux_bank_observable_eq_open_load_sum]
    simp only [Fin.sum_univ_two, E, L]
  have hadd : modelCovarianceTrace (fun z => E 0 (L z)+E 1 (L z)) H x =
      modelCovarianceTrace (fun z => E 0 (L z)) H x +
        modelCovarianceTrace (fun z => E 1 (L z)) H x := by
    simpa only [Function.comp_def] using pureFluxBank_modelCovarianceTrace_add H hH
      ((hE 0).comp L.contDiff) ((hE 1).comp L.contDiff) x
  rw [heq, hadd]
  rw [pureFluxBank_modelCovarianceTrace_comp_linear (E 0) (hE 0) L,
    pureFluxBank_modelCovarianceTrace_comp_linear (E 1) (hE 1) L]
  simp only [Fin.sum_univ_two, E, L]

end
end ASDExplicitGamma.Inverse
