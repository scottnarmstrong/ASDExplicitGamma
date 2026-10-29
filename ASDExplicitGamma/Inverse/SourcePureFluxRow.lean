module

public import ASDExplicitGamma.Inverse.RawShellPureFluxRows

/-! The exact four-load source remainder, before weakening its pure-source constants. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

theorem source_model_q3_remainder_covariance_row
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let L := q3ModelLength (n+(s:ℤ))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let R := fun j => centeringMap center (H j)
    let k := pureFluxOpenResponseRestriction n x
    let B := pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable n ν σ) R x ≤
      b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
          (pureFluxCovarianceB 0 (s-1))*B^2*
        (modelTraceObservable n ν σ x + 4) := by
  classical
  intro Q L center H R k B
  let P : Fin 2 × Bool → BlockVec 2 := fun p =>
    orthonormalFrameLoad p.1 (lemmaVLoadSign p.2)
  let E : (Fin 2 × Bool) → ResponseCoefficient (openCubeSet Q) → ℝ :=
    lemmaVLoadEnergy n ν σ hν hσ
  have hH0 : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ) inferInstance
      (mainCubeH3InnerProductSpace n b L).toNormedSpace inferInstance inferInstance
      (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
      (mainCubeH3Value n b L)
  have hH : Summable (fun j => ‖R j‖ ^ 2) := by
    exact summable_sq_bounded_image H hH0 (centeringMap center)
  have hcenter (j : ℕ) : R j = pureFluxCoefficientCentering center (H j) := by
    ext y
    simp [R, centeringMap, pureFluxCoefficientCentering, smul_eq_mul]
  have hrestrict (j : ℕ) : pureFluxOpenResponseRestriction n (R j) =
      pureFluxMainCubeQ3CenteredResponseCoefficient n b L j := by
    rw [hcenter]
    exact (pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction n b L j).symm
  have hload (p : Fin 2 × Bool) :
      modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    exact responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k
  have htrace := modelTrace_covarianceTrace_eq_open_four_load_hessians
    n ν σ hν hσ R hH x
  have hload00 : modelCovarianceTrace (E (0, true))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 0 1) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (0, true)
  have hload01 : modelCovarianceTrace (E (0, false))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 0 (-1)) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (0, false)
  have hload10 : modelCovarianceTrace (E (1, true))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 1 1) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (1, true)
  have hload11 : modelCovarianceTrace (E (1, false))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 1 (-1)) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (1, false)
  have hcov : modelCovarianceTrace (modelTraceObservable n ν σ) R x =
      ∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)),
        modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k := by
    have htrace' := htrace
    simp_rw [hrestrict] at htrace'
    rw [← hload00, ← hload01, ← hload10, ← hload11] at htrace'
    rw [htrace']
    simp [E, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have henergy :
      (∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)), E p k) =
        modelTraceObservable n ν σ x + 4 := by
    have hsum := lemmaVTrace_eq_load_sum n ν σ hν hσ k
    have htraceOpen := modelTraceObservable_eq_lemmaVTrace_openRestriction
      n ν σ hν hσ x
    have hsum' :
        (∑ p : Fin 2 × Bool, lemmaVLoadEnergy n ν σ hν hσ p k) =
          lemmaVTrace n ν σ k + 4 := by linarith [hsum]
    simpa [E] using
      hsum'.trans (congrArg (fun z : ℝ => z + 4) htraceOpen.symm)
  have hbound := pureFlux_shell_finite_affine_load_generator
    n s hs ν σ b hν hσ k Finset.univ P
  dsimp only at hbound
  have hbound' :
      (1/2:ℝ)*(∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)),
        modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k) ≤
        b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
          (pureFluxCovarianceB 0 (s-1))*B^2*
          (∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)), E p k) := by
    simpa [E, P, lemmaVLoadEnergy, lemmaVLoadSign] using hbound
  rw [← hcov, henergy] at hbound'
  simpa [Q, L, center, H, R, k, B] using hbound'

end
end ASDExplicitGamma.Inverse
