module

public import ASDExplicitGamma.Main.InverseLowerCenteredPairTrace
public import ASDExplicitGamma.Main.InverseHessianCenteredQ3
public import ASDExplicitGamma.Main.InverseObservable
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLoads
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankScales
public import ASDExplicitGamma.Inverse.PureFluxGeneratorDirectionBridge
public import ASDExplicitGamma.Inverse.RawShellBankInputs

/-! Instantiate the actual centered two-load source row on a one-pass OLD-frame
insertion, using its finite local-bank history event. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Model
open Algsuperdiff.Section3
open scoped BigOperators
open scoped ENNReal

/-- For an actual shell of a one-pass insertion, the centered q3 response
covariance trace has the two-load source lower bound. The response minimizers
are selected from the variational problem, and the cell histories are bounded
by the same finite local-bank maximum that controls the insertion. -/
theorem main_actual_q3_centered_two_load_row_of_bank_history
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2)
    (hfinite : bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5)
      M n (n + 40) (bankPartialInsertionWeights n s t) ω ≠ ∞) :
    let Q := originCube 2 n
    let σ := (Annealed.sigmaBar M n : ℝ)
    let x := modelInsertedScalar (closure (cubeSet Q)) (n + (s : ℤ) - 1) t ω
    let k := pureFluxOpenResponseRestriction n x
    let b := q3ModelAmplitude M h (n + (s : ℤ))
    let L := q3ModelLength (n + (s : ℤ))
    let P : Fin 2 → BlockVec 2 := fun i => (0, Pi.single i 1)
    let hU := measurableSet_openCubeSet Q
    let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) n
    let H (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
    let E (i : Fin 2) := responseFrameEnergyObservable hU hvol M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (P i)
    let Eall := fun z => ∑ i : Fin 2, E i z
    let B := (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
      (bankPartialInsertionWeights n s t) ω).toReal
    ∃ (r' : Fin 2 → H10Function (openCubeSet Q))
      (u' : Fin 2 → AHarmonicFunction
        (responseFramePlanarCoefficientField M.nu σ k) (openCubeSet Q))
      (w' : Fin 2 → AHarmonicFunction
        (adjointCoeffField (responseFramePlanarCoefficientField M.nu σ k))
        (openCubeSet Q)),
      (∀ i, hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData hU hvol M.nu σ M.nu_pos
          (Annealed.sigmaBar_characterization M n).1 k).toMuHilbertRealization.minimizerMap
            (P i)) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        (fun y => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField M.nu σ k) (u' i) (w' i)).eval y)) ∧
      (∀ i, (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) (P i).1 (r' i)).grad =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField M.nu σ k) (u' i) (w' i)).potential) ∧
      let Wv' (i : Fin 2) := lemmaVTiledWeakEnergy Q (pureFluxBankSourceDepth s)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (P i).1
          (r' i)).grad
      let Wg' (i : Fin 2) := lemmaVTiledWeakEnergy Q (pureFluxBankSourceDepth s)
        ((1 / 2 : ℝ) • ((w' i).toH1 - (u' i).toH1)).grad
      let Kf' (i : Fin 2) := (63 / 50 : ℝ) * B * (abs σ⁻¹ * abs b) ^ 2 *
        pureFluxCovarianceA 0 (s - 1) * pureFluxCovarianceB 0 (s - 1) *
        Real.sqrt (Wv' i) * Real.sqrt (Wg' i)
      let Kz' (i : Fin 2) := abs σ⁻¹ * abs b * pureFluxCovarianceB 0 (s - 1) *
        Real.sqrt (σ / M.nu) * Real.sqrt (Wg' i)
      (1 / 2 : ℝ) * modelCovarianceTrace Eall H k ≥
        ∑ i : Fin 2, (-2 * Kf' i - (Kz' i) ^ 2) := by
  classical
  intro Q σ x k b L P hU hvol H E Eall B
  have hm : pureFluxBankSourceDepth s ≤ 5 := by
    unfold pureFluxBankSourceDepth
    omega
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ k
  have hhist : ∀ U : TriadicCube 2,
      U ∈ descendantsAtDepth Q (pureFluxBankSourceDepth s) →
      lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu σ k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B := by
    intro U hU'
    exact pureFlux_bank_source_mesh_history_le M n s hs t ht ω
      (pureFluxBankSourceDepth s) hm hfinite hU'
  have hmins (i : Fin 2) := lemmaV_minimizer_pair n hEll (P i)
  choose r' u' w' hrep hgrad hEv hEu using hmins
  rw [lemmaV_responseSystem_eq_canonical hU hvol M.nu σ M.nu_pos hσ k] at hrep hEv hEu
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hrow := main_twoLoad_q3_centered_response_covariance_trace_lower
    n 0 (s - 1) (pureFluxBankSourceDepth s) M.nu σ b B M.nu_pos hσ L
    (pureFlux_bank_source_rho n s hs.1) (pureFlux_bank_source_delta n s hs.1)
    k P r' u' w' hrep hgrad hB hhist
  refine ⟨r', u', w', ?_, ?_, ?_⟩
  · intro i
    simpa only [Q, σ, k, P, hU, hvol] using hrep i
  · intro i
    simpa only [Q, σ, k, P, hU, hvol] using hgrad i
  simpa only [Q, σ, x, k, b, L, P, hU, hvol, H, E, Eall, B] using hrow

/-- The actual centered two-load row holds almost surely for a one-pass
insertion whenever the required native-state history is available. This
packages the concrete local-inverse bank with the row estimate, so a consumer
does not need to supply a separate history-finiteness event. -/
theorem main_actual_q3_centered_two_load_row_ae_of_native_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ (r' : Fin 2 → H10Function (openCubeSet (originCube 2 n)))
        (u' : Fin 2 → AHarmonicFunction
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M n : ℝ)
            (pureFluxOpenResponseRestriction n
              (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
                (n + (s : ℤ) - 1) t ω))) (openCubeSet (originCube 2 n)))
        (w' : Fin 2 → AHarmonicFunction
          (adjointCoeffField (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M n : ℝ)
            (pureFluxOpenResponseRestriction n
              (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
                (n + (s : ℤ) - 1) t ω)))) (openCubeSet (originCube 2 n))),
        let Q := originCube 2 n
        let σ := (Annealed.sigmaBar M n : ℝ)
        let x := modelInsertedScalar (closure (cubeSet Q))
          (n + (s : ℤ) - 1) t ω
        let k := pureFluxOpenResponseRestriction n x
        let b := q3ModelAmplitude M h (n + (s : ℤ))
        let L := q3ModelLength (n + (s : ℤ))
        let P : Fin 2 → BlockVec 2 := fun i => (0, Pi.single i 1)
        let hU := measurableSet_openCubeSet Q
        let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) n
        let H (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
        let E (i : Fin 2) := responseFrameEnergyObservable hU hvol M.nu σ M.nu_pos
          (Annealed.sigmaBar_characterization M n).1 (P i)
        let Eall := fun z => ∑ i : Fin 2, E i z
        let B := (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
          (bankPartialInsertionWeights n s t) ω).toReal
        let Wv' (i : Fin 2) := lemmaVTiledWeakEnergy Q (pureFluxBankSourceDepth s)
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (P i).1
            (r' i)).grad
        let Wg' (i : Fin 2) := lemmaVTiledWeakEnergy Q (pureFluxBankSourceDepth s)
          ((1 / 2 : ℝ) • ((w' i).toH1 - (u' i).toH1)).grad
        let Kf' (i : Fin 2) := (63 / 50 : ℝ) * B * (abs σ⁻¹ * abs b) ^ 2 *
          pureFluxCovarianceA 0 (s - 1) * pureFluxCovarianceB 0 (s - 1) *
          Real.sqrt (Wv' i) * Real.sqrt (Wg' i)
        let Kz' (i : Fin 2) := abs σ⁻¹ * abs b * pureFluxCovarianceB 0 (s - 1) *
          Real.sqrt (σ / M.nu) * Real.sqrt (Wg' i)
        (1 / 2 : ℝ) * modelCovarianceTrace Eall H k ≥
          ∑ i : Fin 2, (-2 * Kf' i - (Kz' i) ^ 2) := by
  let hBank := raw_shell_local_inverse_bank M h hM hg n s t ht hpast
  filter_upwards [hBank.history_finite] with ω hfinite
  obtain ⟨r', u', w', _, _, hrow⟩ :=
    main_actual_q3_centered_two_load_row_of_bank_history
      M h n s hs t ht ω (ne_of_lt hfinite)
  exact ⟨r', u', w', hrow⟩

private theorem main_bank_fderiv_fderiv_add
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

private theorem main_bank_modelCovarianceTrace_add
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    modelCovarianceTrace (fun y => f y + g y) H x =
      modelCovarianceTrace f H x + modelCovarianceTrace g H x := by
  rw [modelCovarianceTrace_eq_bilinearTraceMap H hH (hf.add hg) x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hf x,
    modelCovarianceTrace_eq_bilinearTraceMap H hH hg x,
    main_bank_fderiv_fderiv_add hf hg x]
  exact (bilinearTraceMap H hH).map_add _ _

/-- The open-cube two-load covariance trace used by the centered source row
is exactly the physical inverse-observable trace on the closed cube, with the
same centered q3 coefficient directions. -/
theorem main_actual_q3_centered_response_trace_eq_inverse_trace
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let center := pureFluxParentCenter n
    let k := pureFluxOpenResponseRestriction n x
    let H (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
    let E (i : Fin 2) := responseFrameEnergyObservable
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ (0, Pi.single i 1)
    let Eall := fun z => ∑ i : Fin 2, E i z
    modelCovarianceTrace Eall H k =
      modelCovarianceTrace (mainInverseObservable n ν σ)
        (fun j => pureFluxMainCubeQ3Directions n b L j -
          ContinuousMap.const _
            (pureFluxMainCubeQ3Directions n b L j center)) x := by
  classical
  intro Q center k H E Eall
  let U := openCubeSet Q
  let R := pureFluxOpenResponseRestriction n
  let V (j : ℕ) := pureFluxMainCubeQ3Directions n b L j
  let Hc (j : ℕ) := pureFluxCoefficientCentering center (V j)
  let Eload (i : Fin 2) := pureFluxBankLoadEnergy n ν σ hν hσ i
  have hV : Summable (fun j => ‖V j‖ ^ 2) := by
    have hA := mainCubeQ3Directions_summable n b L
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet Q), ℝ) inferInstance
      (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L) hA
      (mainCubeH3Value n b L)
  have hHc : Summable (fun j => ‖Hc j‖ ^ 2) :=
    summable_sq_bounded_image V hV (pureFluxCoefficientCentering center)
  have hdirs (j : ℕ) : R (Hc j) = H j := by
    simpa only [Hc, V, R] using
      (pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction n b L j).symm
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
    rw [main_bank_modelCovarianceTrace_add
      (E := ResponseCoefficient U) H
      (pureFluxMainCubeQ3CenteredResponseCoefficient_summable n b L)
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
  have hcenter (j : ℕ) : Hc j =
      V j - ContinuousMap.const _ (V j center) := by
    simp [Hc, pureFluxCoefficientCentering_apply]
  calc
    modelCovarianceTrace Eall H k =
        ∑ i : Fin 2, modelCovarianceTrace (Eload i) H k := hsplit
    _ = modelCovarianceTrace (bankInverseTraceObservable n ν σ hν hσ) Hc x :=
      hbank'.symm
    _ = modelCovarianceTrace (mainInverseObservable n ν σ) Hc x := by rw [← hobs]
    _ = modelCovarianceTrace (mainInverseObservable n ν σ)
        (fun j => V j - ContinuousMap.const _ (V j center)) x := by
      rw [show Hc = (fun j => V j - ContinuousMap.const _ (V j center)) from
        funext hcenter]

/-- Any lower row estimate proved for the actual open-cube two-load response
trace transfers verbatim to the closed-cube inverse observable. -/
theorem main_actual_q3_centered_inverse_trace_lower_of_response_row
    (n : ℤ) (ν σ b Krow : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let center := pureFluxParentCenter n
    let k := pureFluxOpenResponseRestriction n x
    let H (j : ℕ) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L j
    let E (i : Fin 2) := responseFrameEnergyObservable
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ (0, Pi.single i 1)
    let Eall := fun z => ∑ i : Fin 2, E i z
    (1 / 2 : ℝ) * modelCovarianceTrace Eall H k ≥ Krow →
      (1 / 2 : ℝ) * modelCovarianceTrace (mainInverseObservable n ν σ)
        (fun j => pureFluxMainCubeQ3Directions n b L j -
          ContinuousMap.const _
            (pureFluxMainCubeQ3Directions n b L j center)) x ≥ Krow := by
  intro Q center k H E Eall hrow
  rw [← main_actual_q3_centered_response_trace_eq_inverse_trace n ν σ b hν hσ L x]
  exact hrow

/-- The native-state one-pass lower row can be read directly on the uncentered
actual q3 directions of the inverse-trace heat generator. The constant-skew
gauge removal is exact, so the row penalty is unchanged. -/
theorem main_actual_q3_inverse_trace_row_ae_of_native_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ (r' : Fin 2 → H10Function (openCubeSet (originCube 2 n)))
        (u' : Fin 2 → AHarmonicFunction
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M n : ℝ)
            (pureFluxOpenResponseRestriction n
              (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
                (n + (s : ℤ) - 1) t ω))) (openCubeSet (originCube 2 n)))
        (w' : Fin 2 → AHarmonicFunction
          (adjointCoeffField (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M n : ℝ)
            (pureFluxOpenResponseRestriction n
              (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
                (n + (s : ℤ) - 1) t ω)))) (openCubeSet (originCube 2 n))),
        let Q := originCube 2 n
        let σ := (Annealed.sigmaBar M n : ℝ)
        let x := modelInsertedScalar (closure (cubeSet Q))
          (n + (s : ℤ) - 1) t ω
        let b := q3ModelAmplitude M h (n + (s : ℤ))
        let L := q3ModelLength (n + (s : ℤ))
        let P : Fin 2 → BlockVec 2 := fun i => (0, Pi.single i 1)
        let Wv' (i : Fin 2) := lemmaVTiledWeakEnergy Q (pureFluxBankSourceDepth s)
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (P i).1
            (r' i)).grad
        let Wg' (i : Fin 2) := lemmaVTiledWeakEnergy Q (pureFluxBankSourceDepth s)
          ((1 / 2 : ℝ) • ((w' i).toH1 - (u' i).toH1)).grad
        let B := (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
          (bankPartialInsertionWeights n s t) ω).toReal
        let Kf' (i : Fin 2) := (63 / 50 : ℝ) * B * (abs σ⁻¹ * abs b) ^ 2 *
          pureFluxCovarianceA 0 (s - 1) * pureFluxCovarianceB 0 (s - 1) *
          Real.sqrt (Wv' i) * Real.sqrt (Wg' i)
        let Kz' (i : Fin 2) := abs σ⁻¹ * abs b * pureFluxCovarianceB 0 (s - 1) *
          Real.sqrt (σ / M.nu) * Real.sqrt (Wg' i)
        (1 / 2 : ℝ) * modelCovarianceTrace
          (mainInverseObservable n M.nu σ)
          (pureFluxMainCubeQ3Directions n b L) x ≥
          ∑ i : Fin 2, (-2 * Kf' i - (Kz' i) ^ 2) := by
  have hresponse := main_actual_q3_centered_two_load_row_ae_of_native_state
    M h hM hg n s hs t ht hpast
  filter_upwards [hresponse] with ω hω
  rcases hω with ⟨r', u', w', hrow⟩
  let Q := originCube 2 n
  let σ := (Annealed.sigmaBar M n : ℝ)
  let x := modelInsertedScalar (closure (cubeSet Q)) (n + (s : ℤ) - 1) t ω
  let b := q3ModelAmplitude M h (n + (s : ℤ))
  let L := q3ModelLength (n + (s : ℤ))
  let P : Fin 2 → BlockVec 2 := fun i => (0, Pi.single i 1)
  let Wv' (i : Fin 2) := lemmaVTiledWeakEnergy Q (pureFluxBankSourceDepth s)
    (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (P i).1
      (r' i)).grad
  let Wg' (i : Fin 2) := lemmaVTiledWeakEnergy Q (pureFluxBankSourceDepth s)
    ((1 / 2 : ℝ) • ((w' i).toH1 - (u' i).toH1)).grad
  let B := (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
    (bankPartialInsertionWeights n s t) ω).toReal
  let Kf' (i : Fin 2) := (63 / 50 : ℝ) * B * (abs σ⁻¹ * abs b) ^ 2 *
    pureFluxCovarianceA 0 (s - 1) * pureFluxCovarianceB 0 (s - 1) *
    Real.sqrt (Wv' i) * Real.sqrt (Wg' i)
  let Kz' (i : Fin 2) := abs σ⁻¹ * abs b * pureFluxCovarianceB 0 (s - 1) *
    Real.sqrt (σ / M.nu) * Real.sqrt (Wg' i)
  let Krow := ∑ i : Fin 2, (-2 * Kf' i - (Kz' i) ^ 2)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hcenter := main_actual_q3_centered_inverse_trace_lower_of_response_row
    n M.nu σ b Krow M.nu_pos hσ L x hrow
  have huncentered :=
    (mainInverseObservable_covarianceTrace_mainCubeQ3_centered_eq_twoPureFluxHessians
      n M.nu σ b M.nu_pos hσ L x).1
  have hrow' : (1 / 2 : ℝ) * modelCovarianceTrace
      (mainInverseObservable n M.nu σ) (pureFluxMainCubeQ3Directions n b L) x ≥ Krow := by
    rw [← huncentered]
    exact hcenter
  exact ⟨r', u', w', hrow'⟩

end ASDExplicitGamma.Main

end
