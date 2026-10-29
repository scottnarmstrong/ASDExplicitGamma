module

public import ASDExplicitGamma.Main.PathwiseHessianParentCovariance
public import ASDExplicitGamma.Main.InverseLowerCenteredEnergy
public import ASDExplicitGamma.Main.InverseObservable
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLoads

/-! The signed q3 covariance budget in terms of actual response energy. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

/-- The fixed-frame inverse observable is the squared norm of the selected
minimum-energy response carrier. -/
theorem main_response_energy_minimizer_norm_sq
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2) :
    ‖responseFrameEnergyBaseMinimizer
      (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P‖ ^ 2 =
      responseFrameEnergyObservable
        (measurableSet_openCubeSet (originCube 2 n))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
        ν σ hν hσ P k := by
  let hU := measurableSet_openCubeSet (originCube 2 n)
  let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
  let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
  let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k P
  let hNil := responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ k
  let : NormedAddCommGroup (EnergyCarrier D) := instNormedAddCommGroupEnergyCarrier D
  let : InnerProductSpace ℝ (EnergyCarrier D) := instInnerProductSpaceEnergyCarrier D
  have hOrth : ∀ Y : V.toSubmodule, inner ℝ S Y = 0 := by
    let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
    change ∀ Y : (responseEnergyCorrectionSpace M D).toSubmodule,
      inner ℝ (responseEnergyUp D (M.minimizerMap P)) Y = 0
    intro Y
    exact responseEnergyMinimizer_orthogonal M P Y
  calc
    ‖S‖ ^ 2 = linearShearMinimum V C S 0 hNil :=
      (linearShearMinimum_zero_eq_norm_sq V C S hNil hOrth).symm
    _ = responseFrameEnergy hU hvol ν σ hν hσ k P 0 :=
      (responseFrameEnergy_eq_linearShearMinimum hU hvol ν σ hν hσ k P 0).symm
    _ = responseFrameEnergyObservable hU hvol ν σ hν hσ P k := by
      change 2 *
          (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (k + 0)).toMuHilbertRealization.muCandidate P =
        2 *
          (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (0 + k)).toMuHilbertRealization.muCandidate P
      rw [add_zero, zero_add]

/-- The actual q3 signed covariance of any finite family of affine response
minimizers is bounded by the corresponding inverse-observable energies.
The affine zero-trace correctors and the primal/adjoint minimizer witnesses
are selected from the source variational problem. -/
theorem main_diag_q3_signed_covariance_integral_affine_minimizer_family_le
    {ι : Type*} (s : Finset ι) (n : ℤ) (mesh : ℕ) (ν σ b : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (L : {l : ℝ // 0 < l})
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (P : ι → BlockVec 2) :
    ∃ (r : ι → H10Function (openCubeSet (originCube 2 n)))
      (u : ι → AHarmonicFunction
        (responseFramePlanarCoefficientField ν σ k) (openCubeSet (originCube 2 n)))
      (w : ι → AHarmonicFunction
        (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
          (openCubeSet (originCube 2 n))),
      (∀ i, hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap (P i)) =ᵐ[
            volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) (u i) (w i)).eval x)) ∧
      (∀ i, (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) (P i).1 (r i)).grad =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) (u i) (w i)).potential) ∧
      |∑ i ∈ s, ∑' j : ℕ,
        ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L (originCube 2 n) mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n))
            (P i).1 (r i)) j x ∂(normalizedCubeMeasure (originCube 2 n))| ≤
        b ^ 2 * (σ / ν) * ∑ i ∈ s,
          responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
            (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
            ν σ hν hσ (P i) k := by
  classical
  let Q := originCube 2 n
  let hU := measurableSet_openCubeSet Q
  let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let a := responseFramePlanarCoefficientField ν σ k
  have hEll := responseFramePlanarCoefficientField_isElliptic hU ν σ hν hσ k
  have hmins (i : ι) := lemmaV_minimizer_pair n hEll (P i)
  choose r u w hrep hgrad hEv hEu using hmins
  rw [lemmaV_responseSystem_eq_canonical hU hvol ν σ hν hσ k] at hrep hEv hEu
  have hrep' (i : ι) :
      hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.minimizerMap
          (P i)) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        (fun x => (blockResponsePairHalfState a (u i) (w i)).eval x) := by
    simpa only [a, hU, hvol] using hrep i
  have hgrad' (i : ι) :
      (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (P i).1
        (r i)).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
        (blockResponsePairHalfState a (u i) (w i)).potential := by
    simpa only [a, hU, hvol] using hgrad i
  have hrow (i : ι) :
      |∑' j : ℕ,
        ∫ x, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q)
            (P i).1 (r i)) j x ∂(normalizedCubeMeasure Q)| ≤
        b ^ 2 * lemmaVTiledWeakEnergy Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q)
            (P i).1 (r i)).grad := by
    exact main_diag_q3_signed_covariance_integral_affine_corrector_source_le
      b L Q mesh (P i).1 (r i)
  have hbudget (i : ι) :
      (ν / σ) *
        (lemmaVTiledWeakEnergy Q mesh
            (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q)
              (P i).1 (r i)).grad +
          lemmaVTiledWeakEnergy Q mesh
            ((1 / 2 : ℝ) • ((w i).toH1 - (u i).toH1)).grad) ≤
        ‖responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k (P i)‖ ^ 2 := by
    simpa only [Q, a, hU, hvol] using
      main_response_pair_tiled_weighted_energy_le n mesh ν σ hν hσ k (P i)
        (r i) (u i) (w i) (hrep' i) (hgrad' i)
  have hnorm (i : ι) :
      ‖responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k (P i)‖ ^ 2 =
        responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := by
    let D := responseFrameEnergyData hU hvol ν σ hν hσ k
    let V := responseFrameEnergyVariationSpace hU hvol ν σ hν hσ k
    let C := responseFrameEnergyShearFamily hU hvol ν σ hν hσ k
    let S := responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k (P i)
    let hNil := responseFrameEnergyShearFamily_pairwise_nilpotent hU hvol ν σ hν hσ k
    let : NormedAddCommGroup (EnergyCarrier D) := instNormedAddCommGroupEnergyCarrier D
    let : InnerProductSpace ℝ (EnergyCarrier D) := instInnerProductSpaceEnergyCarrier D
    have hOrth : ∀ Y : V.toSubmodule, inner ℝ S Y = 0 := by
      let M := (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization
      change ∀ Y : (responseEnergyCorrectionSpace M D).toSubmodule,
        inner ℝ (responseEnergyUp D (M.minimizerMap (P i))) Y = 0
      intro Y
      exact responseEnergyMinimizer_orthogonal M (P i) Y
    calc
      ‖S‖ ^ 2 = linearShearMinimum V C S 0 hNil :=
        (linearShearMinimum_zero_eq_norm_sq V C S hNil hOrth).symm
      _ = responseFrameEnergy hU hvol ν σ hν hσ k (P i) 0 :=
        (responseFrameEnergy_eq_linearShearMinimum hU hvol ν σ hν hσ k (P i) 0).symm
      _ = responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := by
        change 2 *
            (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (k + 0)).toMuHilbertRealization.muCandidate
              (P i) =
          2 *
            (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ (0 + k)).toMuHilbertRealization.muCandidate
              (P i)
        rw [add_zero, zero_add]
  have hweak (i : ι) :
      lemmaVTiledWeakEnergy Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q)
            (P i).1 (r i)).grad ≤
        (σ / ν) * responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := by
    let Wv := lemmaVTiledWeakEnergy Q mesh
      (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (P i).1 (r i)).grad
    let Wg := lemmaVTiledWeakEnergy Q mesh
      ((1 / 2 : ℝ) • ((w i).toH1 - (u i).toH1)).grad
    have hWg : 0 ≤ Wg := by
      dsimp [Wg]
      exact lemmaVTiledWeakEnergy_nonneg Q mesh _
    have htotal : (ν / σ) * (Wv + Wg) ≤
        ‖responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k (P i)‖ ^ 2 := by
      simpa only [Wv, Wg] using hbudget i
    have hsum : Wv ≤ Wv + Wg := le_add_of_nonneg_right hWg
    have hscaled := mul_le_mul_of_nonneg_left hsum (div_nonneg hν.le hσ.le)
    have hcombined : (ν / σ) * Wv ≤
        responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := by
      calc
        (ν / σ) * Wv ≤ (ν / σ) * (Wv + Wg) := hscaled
        _ ≤ ‖responseFrameEnergyBaseMinimizer hU hvol ν σ hν hσ k (P i)‖ ^ 2 := htotal
        _ = responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := hnorm i
    have hratio : (σ / ν) * (ν / σ) = 1 := by field_simp
    calc
      Wv = (σ / ν) * ((ν / σ) * Wv) := by rw [← mul_assoc, hratio, one_mul]
      _ ≤ (σ / ν) * responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k :=
        mul_le_mul_of_nonneg_left hcombined (div_nonneg hσ.le hν.le)
  have hfinite := main_diag_q3_signed_covariance_integral_affine_corrector_finite_source_le
    s b L Q mesh (fun i => (P i).1) r
  refine ⟨r, u, w, hrep', hgrad', ?_⟩
  calc
    _ ≤ b ^ 2 * ∑ i ∈ s,
        lemmaVTiledWeakEnergy Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q)
            (P i).1 (r i)).grad := by
      simpa only [Q] using hfinite
    _ ≤ b ^ 2 * ∑ i ∈ s,
        (σ / ν) * responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
      exact Finset.sum_le_sum fun i hi => hweak i
    _ = b ^ 2 * (σ / ν) * ∑ i ∈ s,
        responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := by
      calc
        _ = ∑ i ∈ s, b ^ 2 * ((σ / ν) *
            responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k) := by
          rw [Finset.mul_sum]
        _ = ∑ i ∈ s, (b ^ 2 * (σ / ν)) *
            responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (b ^ 2 * (σ / ν)) * ∑ i ∈ s,
            responseFrameEnergyObservable hU hvol ν σ hν hσ (P i) k := by
          rw [← Finset.mul_sum]
        _ = _ := by ring

/-- For the two canonical inverse-trace loads, the signed q3 DIAG covariance
is controlled directly by the actual fixed-frame inverse observable. This is
the form of the covariance-to-response-energy adapter. -/
theorem main_diag_q3_signed_covariance_integral_actual_inverse_trace_le
    (n : ℤ) (mesh : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    ∃ (r : Fin 2 → H10Function (openCubeSet (originCube 2 n)))
      (u : Fin 2 → AHarmonicFunction
        (responseFramePlanarCoefficientField ν σ
          (pureFluxOpenResponseRestriction n x)) (openCubeSet (originCube 2 n)))
      (w : Fin 2 → AHarmonicFunction
        (adjointCoeffField (responseFramePlanarCoefficientField ν σ
          (pureFluxOpenResponseRestriction n x))) (openCubeSet (originCube 2 n))),
      (∀ i, hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ (pureFluxOpenResponseRestriction n x)).toMuHilbertRealization.minimizerMap
            (0, Pi.single i 1)) =ᵐ[
              volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun y => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ
            (pureFluxOpenResponseRestriction n x)) (u i) (w i)).eval y)) ∧
      (∀ i, (lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) (0 : Vec 2) (r i)).grad
          =ᵐ[volumeMeasureOn (openCubeSet (originCube 2 n))]
        (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ
            (pureFluxOpenResponseRestriction n x)) (u i) (w i)).potential) ∧
      |∑ i : Fin 2, ∑' j : ℕ,
        ∫ y, mainDiagQ3SignedLocalizedGradientTerm b L (originCube 2 n) mesh
          (lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) (0 : Vec 2) (r i)) j y
          ∂(normalizedCubeMeasure (originCube 2 n))| ≤
        b ^ 2 * (σ / ν) * mainInverseObservable n ν σ x := by
  let Q := originCube 2 n
  let U := openCubeSet Q
  let hU := measurableSet_openCubeSet Q
  let hvol := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let P : Fin 2 → BlockVec 2 := fun i => (0, Pi.single i 1)
  let k := pureFluxOpenResponseRestriction n x
  let E (i : Fin 2) := responseFrameEnergyObservable hU hvol ν σ hν hσ (P i)
  have hE (i : Fin 2) : E i k = σ *
      (coarseBlockMatrix (cubeSet Q)
        (responsePlanarCoefficientField ν
          (ContinuousMap.linearIsometryBoundedOfCompact
            (closure (cubeSet Q)) ℝ ℝ x))).lowerRight i i := by
    simpa only [E, hU, hvol, P, Q, k, pureFluxBankLoadEnergy] using
      pureFlux_bank_load_energy_eq n ν σ hν hσ x i
  have hsum : (∑ i : Fin 2, E i k) = mainInverseObservable n ν σ x := by
    calc
      (∑ i : Fin 2, E i k) =
          ∑ i : Fin 2, σ * (coarseBlockMatrix (cubeSet Q)
            (responsePlanarCoefficientField ν
              (ContinuousMap.linearIsometryBoundedOfCompact
                (closure (cubeSet Q)) ℝ ℝ x))).lowerRight i i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hE i
      _ = σ * Matrix.trace (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField ν
            (ContinuousMap.linearIsometryBoundedOfCompact
              (closure (cubeSet Q)) ℝ ℝ x))).lowerRight := by
        rw [← Finset.mul_sum]
        rfl
      _ = mainInverseObservable n ν σ x := by rfl
  obtain ⟨r, u, w, hrep, hgrad, hcov⟩ :=
    main_diag_q3_signed_covariance_integral_affine_minimizer_family_le
      (ι := Fin 2) Finset.univ n mesh ν σ b hν hσ L k P
  refine ⟨r, u, w, hrep, hgrad, ?_⟩
  calc
    |∑ i : Fin 2, ∑' j : ℕ,
        ∫ y, mainDiagQ3SignedLocalizedGradientTerm b L Q mesh
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q)
            (P i).1 (r i)) j y ∂(normalizedCubeMeasure Q)| ≤
        b ^ 2 * (σ / ν) * ∑ i : Fin 2, E i k := by
      simpa only [Q, U, hU, hvol, P, k, E, Finset.sum_const_zero, Finset.sum_attach] using hcov
    _ = b ^ 2 * (σ / ν) * mainInverseObservable n ν σ x := by rw [hsum]

end ASDExplicitGamma.Main
