module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorBound
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLoads
public import ASDExplicitGamma.Inverse.BankOnePassGenerator

/-! The actual physical generator supplies the exact assembled inverse-bank input. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped BigOperators
noncomputable section

/-- Exact canonical q3 bank generator at an arbitrary continuous base coefficient. -/
theorem pureFlux_bank_generator_of_history_bound (n : ℤ) (s : ℕ) (hs : 1 ≤ s)
    (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (f : C(closure (cubeSet (originCube 2 n)), ℝ)) (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) (pureFluxBankSourceDepth s),
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ (pureFluxOpenResponseRestriction n f))
        ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    (1/2:ℝ)*modelCovarianceTrace (bankInverseTraceObservable n ν σ hν hσ)
      (pureFluxMainCubeQ3Directions n b (q3ModelLength (n+(s:ℤ)))) f ≤
      b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1)) (pureFluxCovarianceB 0 (s-1))*B^2*
        bankInverseTraceObservable n ν σ hν hσ f := by
  let Q := originCube 2 n
  let L := q3ModelLength (n+(s:ℤ))
  let H := pureFluxMainCubeQ3Directions n b L
  let center := pureFluxParentCenter n
  let Hc := fun j => pureFluxCoefficientCentering center (H j)
  let k := pureFluxOpenResponseRestriction n f
  let E := pureFluxBankLoadEnergy n ν σ hν hσ
  have hH : Summable (fun j => ‖H j‖^2) :=
    @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet Q), ℝ) inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L)
      (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
  have hHc : Summable (fun j => ‖Hc j‖^2) :=
    summable_sq_bounded_image H hH (pureFluxCoefficientCentering center)
  have hdirs : (fun j => pureFluxOpenResponseRestriction n (Hc j)) =
      pureFluxMainCubeQ3CenteredResponseCoefficient n b L := by
    funext j
    exact (pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction n b L j).symm
  have htrace : modelCovarianceTrace (bankInverseTraceObservable n ν σ hν hσ) H f =
      ∑ i : Fin 2, modelCovarianceTrace (E i)
        (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k := by
    calc
      _ = modelCovarianceTrace (bankInverseTraceObservable n ν σ hν hσ) Hc f := by
        simpa only [Hc, pureFluxCoefficientCentering_apply] using
          (pureFlux_bank_covarianceTrace_centered n ν σ hν hσ H f center).symm
      _ = _ := by
        rw [pureFlux_bank_covarianceTrace_eq_open_load_sum n ν σ hν hσ Hc hHc f, hdirs]
  have hbound (i : Fin 2) : (1/2:ℝ)*modelCovarianceTrace (E i)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k ≤
      b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1)) (pureFluxCovarianceB 0 (s-1))*B^2*E i k :=
    pureFlux_affine_load_generator_of_history_bound n 0 (s-1) (pureFluxBankSourceDepth s)
      ν σ b hν hσ L (pureFlux_bank_source_rho n s hs) (pureFlux_bank_source_delta n s hs)
      k (0, Pi.single i 1) B hB hhist
  rw [htrace, Finset.mul_sum]
  calc
    _ ≤ ∑ i : Fin 2, b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
        (pureFluxCovarianceB 0 (s-1))*B^2*E i k := Finset.sum_le_sum fun i _ => hbound i
    _ = _ := by
      rw [← Finset.mul_sum, pureFlux_bank_observable_eq_open_load_sum]

/-- The exact source generator input required by the assembled one-pass inverse bank. -/
theorem bankPureFluxGeneratorInput (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (k : ℤ)
    (hpast : ∀ n < k, nativeInductionState M h n) : BankPureFluxGeneratorInput M h k := by
  intro s hs t ht T v hA hlaw
  have hgeometry := bank_one_pass_local_geometry k
  have hbank := first_local_inverse_bank M h hM hg (bankLocalRoots (originCube 2 k) 5) k (k+40)
    (by omega) (bankPartialInsertionWeights k s t)
    (fun i _ => bank_partial_insertion_weights_bounds k s t ht.2 i)
    hgeometry.1 hgeometry.2 hpast
  filter_upwards [hbank.history_finite] with ω hfinite
  let σ := (Annealed.sigmaBar M k : ℝ)
  let b := q3ModelAmplitude M h (k+(s:ℤ))
  let f := modelInsertedScalar (closure (cubeSet (originCube 2 k))) (k+(s:ℤ)-1) t ω
  let B := bankOnePassLocalHistory M k s t ω
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M k).1
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hhist : ∀ U ∈ descendantsAtDepth (originCube 2 k) (pureFluxBankSourceDepth s),
      lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction k f))
        ((3:ℝ)^(1/4:ℝ)) ≤ B := by
    intro U hU
    exact pureFlux_bank_source_mesh_history_le M k s hs t ht ω (pureFluxBankSourceDepth s)
      ((pureFlux_bank_source_depth_le_four s hs.1).trans (by norm_num)) hfinite.ne hU
  have hb := pureFlux_bank_generator_of_history_bound k s hs.1 M.nu σ b M.nu_pos hσ f B hB hhist
  have hcov := pureFlux_bank_covarianceTrace_eq_actual_q3 k M h hM s t T v hA hlaw f
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet (originCube 2 k))) (isBounded_cubeSet (originCube 2 k)).isCompact_closure
  have hphysical := bank_inverse_trace_observable_inserted k M ell (k+(s:ℤ)-1) hK σ hσ t ω
  rw [hphysical] at hb
  rw [hcov]
  exact hb

end
end ASDExplicitGamma.Inverse
