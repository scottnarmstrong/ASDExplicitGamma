module

public import ASDExplicitGamma.Scalar.OldHessianTrialSourceBank

/-! A measurable scalar majorant for the actual full mixed source and its
projection, using the original fine row and genuine coarse potentials. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The complete two-load source-square envelope before averaging. -/
def oldHessianSourceEnvelope (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (oldSignedSourceMultiplier (originCube 2 (m+129)) 134 b L*
      Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω)+
    oldHessianCoarseColumnCoefficient (originCube 2 (m+129)) 133 b L*
      Real.sqrt (inverseHistoryDiscount^2*oldHessianGroupedOldTheta M m ω))^2

/-- The actual full mixed source and its actual projected residual are
bounded simultaneously; no energy estimate is assumed. -/
theorem old_hessian_actual_source_residual_envelope
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ (b : ℝ) (L : {l : ℝ // 0<l}),
      let Q := originCube 2 (m+129)
      let k := oldHessianOldOpenCoefficient (m+129) m ω
      (∑ i : Fin 2,∑' j : whiteBasisIndex,
        oldHessianBrokenColumnEnergy Q 134 (fun _U x =>
          (oldHessianMixedBottomSource Q 133 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
            (Annealed.sigmaBar_characterization M m).1 k b L j i x).2)) ≤
          oldHessianSourceEnvelope M m b L ω ∧
      (∑ i : Fin 2,∑' j : whiteBasisIndex,
        let R := oldHessianMixedBottomResidual Q 133 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1 k b L j i
        oldSignedEnergyPairing Q M.nu (Annealed.sigmaBar M m) k R R) ≤
          oldHessianGroupedBank M m ω*oldHessianSourceEnvelope M m b L ω := by
  filter_upwards [old_hessian_actual_source_components_bank M h hM hg N hpast m hm,
    old_hessian_actual_fine_histories_le_bank M h hM hg N hpast m hm] with ω hcomp hbank
  intro b L
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let A := oldSignedSourceMultiplier Q 134 b L
  let C := oldHessianCoarseColumnCoefficient Q 133 b L
  let W := ∑ i : Fin 2,lemmaVTiledWeakEnergy Q 134
    (oldHessianMixedPotential Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k i).toH1Function.grad
  let V := ∑ i : Fin 2,oldHessianCoarseColumnBill Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k (basisVec i) b L
  let D := A*Real.sqrt W+Real.sqrt V
  let F := A*Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω)+
    C*Real.sqrt (inverseHistoryDiscount^2*oldHessianGroupedOldTheta M m ω)
  have hA : 0≤A := old_hessian_source_multiplier_nonneg Q 134 b L
  have hC : 0≤C := by
    unfold C oldHessianCoarseColumnCoefficient
    have hQ := Triadic.cubeScaleFactor_pos' Q
    have hL := L.property
    positivity
  have hD : 0≤D := add_nonneg (mul_nonneg hA (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hDF : D≤F := by
    have hv := Real.sqrt_le_sqrt (hcomp.2 b L)
    rw [Real.sqrt_mul (sq_nonneg C),Real.sqrt_sq hC] at hv
    exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcomp.1) hA) hv
  have hsq := pow_le_pow_left₀ hD hDF 2
  have hsource := old_hessian_actual_joint_source_energy (m+129) 133 M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L
  have hres := old_hessian_actual_joint_residual_energy (m+129) 133 M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L
  constructor
  · have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsource.2 2
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => tsum_nonneg (fun j =>
      old_hessian_broken_column_energy_nonneg Q 134 _)))] at hh
    exact hh.trans hsq
  · exact hres.2.trans ((mul_le_mul_of_nonneg_left hsq
      (old_hessian_fine_history_nonneg Q 134 M.nu (Annealed.sigmaBar M m) k)).trans
        (mul_le_mul_of_nonneg_right (hbank 5 (by norm_num)) (sq_nonneg F)))

end
end ASDExplicitGamma.Scalar
