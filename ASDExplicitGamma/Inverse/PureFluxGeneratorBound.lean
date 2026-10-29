module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorFeedback
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredYTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorMinimizerEnergy
public import ASDExplicitGamma.Inverse.PureFluxGeneratorDirectionBridge
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTraceLimit
public import ASDExplicitGamma.Inverse.PureFluxGeneratorHistory
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankScales

/-! The actual centered covariance generator bound for every affine load. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Variational ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped BigOperators
noncomputable section

local instance pureFluxBoundFiniteMeasure (n : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 n))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isFiniteMeasure_restrict_volume

theorem pureFlux_affine_load_generator_of_history_bound
    (n : ℤ) (q i m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hρ : cubeScaleFactor (originCube 2 n)/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m/L.1 = pureFluxCovarianceDelta q i)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ U ∈ descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k)
        ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    (1/2:ℝ)*modelCovarianceTrace
      (responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k ≤
      b^2/σ^2 *pureFluxCovarianceMu (pureFluxCovarianceA q i) (pureFluxCovarianceB q i)*B^2*
        responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P k := by
  let Q := originCube 2 n
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let a := responseFramePlanarCoefficientField ν σ k
  let E := responseFrameEnergyObservable (measurableSet_openCubeSet Q) hv ν σ hν hσ P
  let c := |σ⁻¹| * |b|
  let enc := @Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex)
  let H := fun l : whiteBasisIndex => pureFluxMainCubeQ3CenteredResponseCoefficient n b L (enc l)
  let Y := fun l => pureFluxResponseGeneratorY (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let Z := fun l => pureFluxResponseGeneratorZ (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  let S := responseFrameEnergyBaseMinimizer (measurableSet_openCubeSet Q) hv ν σ hν hσ k P
  let C := fun l => inner ℝ S (responseFrameEnergyShearFamily
    (measurableSet_openCubeSet Q) hv ν σ hν hσ k (H l) (Y l))
  let g := fun l => pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k (H l)
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) ν σ hν hσ k
  obtain ⟨r, u, w, hrep, hgrad, hEv, hEu⟩ := lemmaV_minimizer_pair n hEll P
  rw [lemmaV_responseSystem_eq_canonical hU.isOpen.measurableSet hv ν σ hν hσ k] at hrep hEv hEu
  have hE : E k = 2*(responseFrameMuOperatorSystemData hU.isOpen.measurableSet hv ν σ hν hσ k).toMuHilbertRealization.muCandidate P :=
    lemmaV_observable_eq_twice_muCandidate hU.isOpen.measurableSet hv ν σ hν hσ P k
  rw [← hE] at hEv hEu
  let v := lemmaVAffinePotential hU P.1 r
  let G := fun x => (1/2:ℝ) • (w.toH1.grad x-u.toH1.grad x)
  let x := Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)
  let y := Real.sqrt (lemmaVTiledWeakEnergy Q m G)
  have hx : x^2 = lemmaVTiledWeakEnergy Q m v.grad := Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m _)
  have hy : y^2 = lemmaVTiledWeakEnergy Q m G := Real.sq_sqrt (lemmaVTiledWeakEnergy_nonneg Q m _)
  have hp : x^2+y^2 ≤ B*E k := by
    rw [hx, hy]
    exact pureFlux_minimizer_pair_tiled_energy_bound n m ν σ hν hσ k P r u w hgrad hEv hEu B hhist
  have htrace := pureFluxMainQ3CenteredGeneratorY_covariance_trace_bound
    n q i m ν σ b hν hσ L k P r u w hrep hgrad hρ hδ B hB hhist
  have hfinite (s : Finset whiteBasisIndex) :
      (1/2:ℝ)*(∑ l ∈ s, g l) ≤ c^2*pureFluxCovarianceMu
        (pureFluxCovarianceA q i) (pureFluxCovarianceB q i)*B^2*E k := by
    have hidentity : (1/2:ℝ)*(∑ l ∈ s, g l) =
        (∑ l ∈ s, ‖Y l‖^2)+2*(∑ l ∈ s, C l)-(∑ l ∈ s, ‖Z l‖^2) := by
      rw [Finset.mul_sum]
      simp_rw [g, pureFluxResponseHessianDiagonal_source_identity]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    have hs : (∑ l ∈ s, ‖Y l‖^2) ≤ B*c^2*(pureFluxCovarianceA q i)^2*x^2 := by
      calc
        _ ≤ ∑' l, ‖Y l‖^2 := htrace.1.sum_le_tsum s (fun _ _ => sq_nonneg _)
        _ ≤ B*(|σ⁻¹| * |b| *pureFluxCovarianceA q i)^2*lemmaVTiledWeakEnergy Q m v.grad := htrace.2
        _ = _ := by rw [hx]; dsimp only [c]; ring
    have hc : (∑ l ∈ s, C l) ≤ (63/50:ℝ)*B*c^2*pureFluxCovarianceA q i*
        pureFluxCovarianceB q i*x*y := by
      have hc0 := pureFluxMainQ3CenteredGeneratorY_cross_feedback_finite
        n q i m ν σ b hν hσ L s k P r u w hrep hgrad hρ hδ B hB hhist
      have hGgrad : (((1/2:ℝ) • (w.toH1-u.toH1)) : H1Function (openCubeSet Q)).grad = G := by
        funext z j
        simp only [G, H1Function.smul_grad, H1Function.sub_grad, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      dsimp only at hc0
      rw [hGgrad] at hc0
      apply (le_abs_self _).trans
      exact hc0
    exact pureFlux_generator_source_feedback_bound q i c B _ _ _ _ x y (E k) hB hidentity
      (Finset.sum_nonneg fun _ _ => sq_nonneg _) hs hc hp
  have hEd : ContDiff ℝ 2 E := responseFrameEnergyObservable_contDiff _ _ ν σ hν hσ P
  have hdirs := pureFluxMainCubeQ3CenteredResponseCoefficient_summable n b L
  have hsecond (j : ℕ) : secondDirectionalDerivative E k
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) =
      pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k
        (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
    exact responseFrameEnergyObservable_hessian _ _ ν σ hν hσ P k _ _
  have hs0 := pureFlux_secondDirectionalDerivative_summable E hEd
    (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) hdirs k
  have hs1 : Summable (fun j => pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
      hv ν σ hν hσ P k (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j)) := by
    simpa only [hsecond] using hs0
  have hgs : Summable g := hs1.comp_injective
    (@Encodable.encode_injective whiteBasisIndex (Encodable.ofCountable whiteBasisIndex))
  have ht := pureFlux_tsum_half_le_of_finite_bounds g hgs _ hfinite
  have hz : pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k 0 = 0 := by
    have h0 : secondDirectionalDerivative E k 0 =
        pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k 0 := by
      unfold secondDirectionalDerivative pureFluxResponseHessianDiagonal
      exact responseFrameEnergyObservable_hessian _ _ ν σ hν hσ P k 0 0
    rw [← h0]
    simp [secondDirectionalDerivative]
  have heq : modelCovarianceTrace E (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k = ∑' l, g l := by
    rw [responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum]
    exact pureFlux_centered_directions_tsum_apply n b L
      (pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q) hv ν σ hν hσ P k) hz
  have hc2 : c^2 = b^2/σ^2 := by
    dsimp only [c]
    rw [mul_pow, sq_abs, sq_abs, inv_pow]
    ring
  rw [← heq, hc2] at ht
  exact ht

/-- The source generator bound with its actual complete source-history maximum. -/
theorem pureFlux_affine_load_generator
    (n : ℤ) (q i m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hρ : cubeScaleFactor (originCube 2 n)/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m/L.1 = pureFluxCovarianceDelta q i)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2) :
    let Q := originCube 2 n
    let B := pureFluxSourceTileHistory Q m (responseFramePlanarCoefficientField ν σ k)
    let E := responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P
    (1/2:ℝ)*modelCovarianceTrace E (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k ≤
      b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA q i) (pureFluxCovarianceB q i)*B^2*E k := by
  intro Q B E
  exact pureFlux_affine_load_generator_of_history_bound n q i m ν σ b hν hσ L hρ hδ k P B
    (pureFlux_source_tile_history_nonneg Q m _)
    (pureFlux_source_tile_history_member_le Q m _)

/-- Every physical shell and every affine load, including all four remainder loads. -/
theorem pureFlux_shell_affine_load_generator
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2) :
    let Q := originCube 2 n
    let m := pureFluxBankSourceDepth s
    let L := q3ModelLength (n+(s:ℤ))
    let B := pureFluxSourceTileHistory Q m (responseFramePlanarCoefficientField ν σ k)
    let E := responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P
    (1/2:ℝ)*modelCovarianceTrace E (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k ≤
      b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
        (pureFluxCovarianceB 0 (s-1))*B^2*E k := by
  exact pureFlux_affine_load_generator n 0 (s-1) (pureFluxBankSourceDepth s) ν σ b hν hσ
    (q3ModelLength (n+(s:ℤ))) (pureFlux_bank_source_rho n s hs) (pureFlux_bank_source_delta n s hs) k P

/-- The same physical source estimate sums over any finite affine-load family. -/
theorem pureFlux_shell_finite_affine_load_generator
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    {ι : Type*} (loads : Finset ι) (P : ι → BlockVec 2) :
    let Q := originCube 2 n
    let m := pureFluxBankSourceDepth s
    let L := q3ModelLength (n+(s:ℤ))
    let B := pureFluxSourceTileHistory Q m (responseFramePlanarCoefficientField ν σ k)
    let E := fun p => responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p)
    (1/2:ℝ)*(∑ p ∈ loads, modelCovarianceTrace (E p)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k) ≤
      b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
        (pureFluxCovarianceB 0 (s-1))*B^2*(∑ p ∈ loads, E p k) := by
  have hh := Finset.sum_le_sum (s := loads) (fun p _ =>
    pureFlux_shell_affine_load_generator n s hs ν σ b hν hσ k (P p))
  simpa only [← Finset.mul_sum] using hh

end
end ASDExplicitGamma.Inverse
