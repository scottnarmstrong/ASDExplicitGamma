module

public import ASDExplicitGamma.Scalar.OldHessianTrialFlatCovarianceProfile
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedThetaMoments
public import ASDExplicitGamma.Scalar.OldHessianTrialCertifiedSource
public import ASDExplicitGamma.Scalar.OldHessianTrialSourceRoot
public import ASDExplicitGamma.Native.OldSignedSqrtExpectation

/-! The actual original flat tangent, including its negative inverse bulk. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Original two-load flat covariance tangent with the exact lambda factor. -/
def oldHessianFlatTangentTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (n : whiteBasisIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 (m+129)
  let L := q3ModelLength (m+1)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let σ := Annealed.sigmaBar M m
  (431/500:ℝ)*(2*∑ i : Fin 2,
    (-oldSignedEnergyPairing Q M.nu σ k
      (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M m).1 k (0,basisVec i))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (oldSignedFlatMinusBlock Q b L n i))+
      ∑ j : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,j) x)))

/-- Actual harmonic covariance remainder, before the deterministic Bflat
cap is inserted. The exact signed bulk is kept outside this envelope. -/
def oldHessianFlatTangentEnvelope (M : ABKModel 2) (m : ℤ) (b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (2*(431/500:ℝ)*oldHessianFlatCovarianceCap (originCube 2 (m+129)) 134 b (q3ModelLength (m+1)))*
    Real.sqrt (oldHessianGroupedOldTheta M m ω)

/-- The complete original flat tangent retains -lambda b²(tr D-2) and
pays its covariance remainder against the same paired OLD parent proxy. -/
theorem old_hessian_actual_flat_tangent
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    Integrable (oldHessianFlatTangentEnvelope M m b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (m+129)
      let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω)
      Summable (fun n => oldHessianFlatTangentTerm M m b n ω) ∧
      (∑' n,oldHessianFlatTangentTerm M m b n ω)≤
        -(431/500:ℝ)*b^2*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
          oldHessianFlatTangentEnvelope M m b ω) ∧
    (∫ ω,oldHessianFlatTangentEnvelope M m b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (2*(431/500:ℝ)*oldHessianFlatCovarianceCap (originCube 2 (m+129)) 134 b (q3ModelLength (m+1)))*
        Real.sqrt (evalReal scalarRealEnv lowerXiExpr) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q := originCube 2 (m+129)
  let L := q3ModelLength (m+1)
  let C := oldHessianFlatCovarianceCap Q 134 b L
  have hC : 0≤C := old_hessian_flat_covariance_cap_nonneg Q 134 b L
  have hθ := old_hessian_grouped_old_theta_moments M h hM hg N hpast m hm 0 (by norm_num)
  simp only [pow_zero,one_mul] at hθ
  have hr := old_signed_sqrt_expectation μ (oldHessianGroupedOldTheta M m) hθ.2.1
    (old_hessian_grouped_old_theta_nonneg M m)
  have hc : 0≤2*(431/500:ℝ)*C := mul_nonneg (by norm_num) hC
  refine ⟨hr.1.const_mul _,?_,?_⟩
  · filter_upwards [old_hessian_actual_parent_bottom_pair_le_theta M h hM hg N hpast m hm] with ω hω
    let k := oldHessianOldOpenCoefficient (m+129) m ω
    let σ := Annealed.sigmaBar M m
    have hh := old_hessian_actual_bottom_covariance_paired_bill Q 134 M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L
    dsimp only at hh
    have hs := old_hessian_flat_covariance_spatial Q 134 M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L
    rw [←old_signed_cell_average_eq_descendantsAverage Q 134 (fun U => oldHessianBottomPairedCellEnergy Q U M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k)] at hs
    have hp := hs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hω) hC)
    refine ⟨hh.1.mul_left (431/500:ℝ),?_⟩
    change (∑' n,(431/500:ℝ)*_)≤_
    rw [tsum_mul_left]
    have ht := mul_le_mul_of_nonneg_left (hh.2.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)))) (by norm_num : (0:ℝ)≤431/500)
    exact ht.trans_eq (by dsimp only [oldHessianFlatTangentEnvelope,C,Q,L]; ring)
  · change (∫ ω,(2*(431/500:ℝ)*C)*Real.sqrt (oldHessianGroupedOldTheta M m ω) ∂μ)≤_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hr.2.trans (Real.sqrt_le_sqrt (hθ.2.2.trans
      (old_hessian_weak_payment_certified M hg)))) hc

end
end ASDExplicitGamma.Scalar
