module

public import ASDExplicitGamma.Scalar.ViscosityEnergy
public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-! Monotonicity of the actual affine minimum over its viscosity-independent admissible set. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory

/-- Ellipticity makes the genuine set of competitor energies bounded below. -/
theorem molecular_muValueSet_bddBelow {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (P : BlockVec d) :
    BddBelow (muValueSet (cubeSet Q) P a) := by
  refine ⟨0,?_⟩
  rintro z ⟨X,_,rfl⟩
  unfold volumeAverage
  apply mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
  have h := blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (X.eval x)
  exact mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) h

/-- The common affine admissible set transports a positive multiplicative integrand comparison. -/
theorem molecular_mu_comparison {d : ℕ} (Q : TriadicCube d) (a b : CoeffField d)
    {la La lb Lb : ℝ} (ha : IsEllipticFieldOn la La (cubeSet Q) a)
    (hb : IsEllipticFieldOn lb Lb (cubeSet Q) b) (r : ℝ) (hr : 0 ≤ r)
    (hc : ∀ X : BlockState d, ∀ x ∈ cubeSet Q, r*blockEnergyDensity a X x ≤ blockEnergyDensity b X x)
    (P : BlockVec d) : r*Mu (cubeSet Q) P a ≤ Mu (cubeSet Q) P b := by
  have instViscosityFiniteVolume : IsFiniteMeasure (volumeMeasureOn (cubeSet Q)) :=
    (isBounded_cubeSet Q).isBoundedDomain.isFiniteMeasure_restrict_volume
  apply le_Mu_of_forall_isBlockMuAdmissible
  intro X hX
  have hiA := (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn ha).energyIntegrable
  have hiB := (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn hb).energyIntegrable
  have hMu : Mu (cubeSet Q) P a ≤ volumeAverage (cubeSet Q) (blockEnergyDensity a X) :=
    csInf_le (molecular_muValueSet_bddBelow Q a ha P) (muValueSet_mem hX)
  calc
    _ ≤ r*volumeAverage (cubeSet Q) (blockEnergyDensity a X) := mul_le_mul_of_nonneg_left hMu hr
    _ = (volume (cubeSet Q)).toReal⁻¹ *∫ x in cubeSet Q, r*blockEnergyDensity a X x := by
      rw [integral_const_mul]
      unfold volumeAverage
      ring
    _ ≤ volumeAverage (cubeSet Q) (blockEnergyDensity b X) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
      apply integral_mono_ae (hiA.const_mul r) hiB
      filter_upwards [ae_restrict_mem (measurableSet_cubeSet Q)] with x hx
      exact hc X x hx

end ASDExplicitGamma.Scalar
