module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalRemainder
public import ASDExplicitGamma.Scalar.OldHessianTrialJointCenteredEnergy
public import ASDExplicitGamma.Scalar.OldHessianTrialSourceRoot

/-! Actual fine-scale source residual with frozen coefficient, with its coarse product retained. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Literal complete centered mixed-source energy in the actual physical
parent and the original fine interpolant. -/
def oldHessianCenteredSourceEnergy (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  let ha := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k
  ∑ i : Fin 2,∑' j,oldHessianBrokenColumnEnergy Q 134 (fun U =>
    oldHessianCenteredMixedSource Q 134 b (q3ModelLength (m+1))
      (oldSignedCanonicalFirstCorrector Q a ha (0,basisVec i))
      (oldHessianCoarsePotential Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1 k (basisVec i)) U j)

/-- Measurable scalar envelope of the centered row plus genuine product. -/
def oldHessianCenteredSourceEnvelope (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (evalReal scalarRealEnv lowerKrExpr*|b| *
      Real.sqrt (oldHessianGroupedBank M m ω*oldHessianSourceTrace M m 4 ω)+
    evalReal scalarRealEnv lowerColumnMixExpr*|b| *Real.sqrt (oldHessianGroupedOldTheta M m ω))^2

/-- The actual centered mixed-source energy is controlled by the exact
fine kr envelope; the coarse column is retained with its larger radius. -/
theorem old_hessian_actual_centered_source_envelope
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldHessianCenteredSourceEnergy M m b ω≤oldHessianCenteredSourceEnvelope M m b ω := by
  filter_upwards [old_hessian_actual_source_components_bank M h hM hg N hpast m hm] with ω hcomp
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let L := q3ModelLength (m+1)
  let C := oldHessianCoarseColumnCoefficient Q 133 b L
  have hC : 0≤C := by
    dsimp only [C,Q,L]
    rw [old_hessian_physical_coarse_column]
    positivity
  have hkr : 0≤evalReal scalarRealEnv lowerKrExpr*|b| := by
    norm_num [evalReal,lowerKrExpr,lowerS1Expr,lowerS2Expr,sc]
    positivity
  have hs := old_hessian_actual_joint_centered_energy Q 133 M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L
  have hrow := mul_le_mul (old_hessian_physical_centered_remainder m b)
    (Real.sqrt_le_sqrt hcomp.1) (Real.sqrt_nonneg _) hkr
  have hcol := Real.sqrt_le_sqrt (hcomp.2 b L)
  rw [Real.sqrt_mul (sq_nonneg C),Real.sqrt_sq hC,
    Real.sqrt_mul (sq_nonneg inverseHistoryDiscount),Real.sqrt_sq inverse_history_discount_range.1.le] at hcol
  have hcol2 := mul_le_mul_of_nonneg_right (old_hessian_coarse_column_certified m b)
    (Real.sqrt_nonneg (oldHessianGroupedOldTheta M m ω))
  have hcol3 := hcol.trans (by simpa only [mul_assoc] using hcol2)
  have hroot := hs.2.trans (add_le_add hrow hcol3)
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => tsum_nonneg (fun j =>
    old_hessian_broken_column_energy_nonneg Q 134 _)))] at hh
  simpa only [oldHessianCenteredSourceEnergy,oldHessianCenteredSourceEnvelope,Q,k,L,mul_assoc] using hh

end
end ASDExplicitGamma.Scalar
