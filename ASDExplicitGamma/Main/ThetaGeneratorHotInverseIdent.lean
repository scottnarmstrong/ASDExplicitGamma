module

public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorIntegrated
public import ASDExplicitGamma.Main.InverseInsertion
public import ASDExplicitGamma.Main.HeatIdentity
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLoads
public import ASDExplicitGamma.Inverse.BankHeatIntegrability

/-! Generator assembly: the observer inverse trace of the bottom covariance row is the
OLD-frame inverse trace `mainInsertionInverseTrace`; hence its mean is `mainInverseHeatAverage`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Native ASDExplicitGamma.Response
  ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff ASDExplicitGamma.Cold

noncomputable section

/-- The coarse block of the frame field on the open cube is the frame matrix of the coarse block
of the raw planar field on the closed cube. -/
theorem hot_open_frame_coarse_Th (k : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (f : C(closure (cubeSet (originCube 2 k)), ℝ)) :
    coarseBlockMatrix (openCubeSet (originCube 2 k))
      (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction k f)) =
      frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 k))
        (responsePlanarCoefficientField ν
          (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ f))) := by
  let Q := originCube 2 k
  have hEllClosed := responsePlanarCoefficientField_isElliptic
    (measurableSet_cubeSet Q) ν hν
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ f)
  rw [coarseBlockMatrix_congr_of_ae_eq (pureFluxOpenResponseRestriction_frame_ae k ν σ f hσ)]
  rw [← cold_coarse_cube_open Q (σ⁻¹ • responsePlanarCoefficientField ν
    (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ f))]
  exact cold_coarse_frame hν hEllClosed hσ

/-- The observer inverse trace is the actual OLD-frame inverse trace. -/
theorem hotInverseTrace_eq_insertion_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (s : ℝ)
    (ω : CutoffSample 2) :
    hotInverseTrace_Th M m hobs s ω = mainInsertionInverseTrace M m (m + (hobs : ℤ)) s ω := by
  rw [← mainInverseObservable_inserted M m (m + (hobs : ℤ)) s ω]
  unfold hotInverseTrace_Th mainInverseObservable
  have hk : mainELinearObsCoefficient (originCube 2 (m + (hobs : ℤ))) m s ω =
      pureFluxOpenResponseRestriction (m + (hobs : ℤ))
        (modelInsertedScalar (closure (cubeSet (originCube 2 (m + (hobs : ℤ))))) m s ω) := rfl
  rw [hk, hot_open_frame_coarse_Th _ M.nu _ M.nu_pos (Annealed.sigmaBar_characterization M m).1]
  simp [frameMatrix, Matrix.trace_smul]

/-- IDENTIFICATION: the observer inverse trace is integrable and its mean is the inverse heat
average at the observer cube. -/
theorem hotInverseTrace_integral_Th (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hobs : ℕ) (s : ℝ) :
    Integrable (hotInverseTrace_Th M m hobs s) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, hotInverseTrace_Th M m hobs s ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        mainInverseHeatAverage (m + (hobs : ℤ)) M m s := by
  have hfun : hotInverseTrace_Th M m hobs s = mainInsertionInverseTrace M m (m + (hobs : ℤ)) s :=
    funext (hotInverseTrace_eq_insertion_Th M m hobs s)
  rw [hfun]
  refine ⟨?_, rfl⟩
  let n := m + (hobs : ℤ)
  let K := closure (cubeSet (originCube 2 n))
  have hΦ := mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  obtain ⟨C, hC, d, hd, -⟩ := hΦ.2
  have hint := bank_model_heat_integrable K M h hM ell m hK
    (mainInverseObservable n M.nu (Annealed.sigmaBar M m : ℝ)) hΦ.1.continuous.measurable
    ⟨C, hC, d, hd⟩ s
  refine hint.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact mainInverseObservable_inserted M m n s ω

end

end ASDExplicitGamma.Main
