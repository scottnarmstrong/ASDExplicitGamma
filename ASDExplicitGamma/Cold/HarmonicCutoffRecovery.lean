module

public import ASDExplicitGamma.Cold.SquareOptimizerProjection
public import ASDExplicitGamma.Cold.PlateauCellOscillation

/-! # The actual cutoff-energy recovery inequality on each own cell -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Set
open ASDExplicitGamma.Triadic
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- Young's inequality for the genuine symmetric-part energy density. -/
theorem symmetric_energy_recovery_young {c lam Lam : ℝ} (hc : 0 < c)
    {A : Mat 2} (hA : IsEllipticMatrix lam Lam A) (v f : Vec 2) :
    (1-c)*vecDot f (matVecMul (symmPart A) f) -
      (1/c-1)*vecDot (v-f) (matVecMul (symmPart A) (v-f)) ≤
      vecDot v (matVecMul (symmPart A) v) := by
  have hz := (mul_nonneg hA.1.le (vecNormSq_nonneg (v-(1-c) • f))).trans
    (lowerBound_symmPart_of_isEllipticMatrix hA (v-(1-c) • f))
  have hsym := vecDot_matVecMul_symmPart_comm A v f
  change 0 ≤ vecDot (v-(1-c) • f) (matVecMul (symmPart A) (v-(1-c) • f)) at hz
  simp only [sub_eq_add_neg,matVecMul_add,matVecMul_neg,matVecMul_smul,vecDot_add_left,vecDot_add_right,
    vecDot_neg_left,vecDot_neg_right,
    vecDot_smul_left,vecDot_smul_right,hsym] at hz
  apply (mul_le_mul_iff_of_pos_left hc).mp
  simp only [sub_eq_add_neg,matVecMul_add,matVecMul_neg,vecDot_add_left,vecDot_add_right,
    vecDot_neg_left,vecDot_neg_right,hsym]
  field_simp
  nlinarith only [hz]

/-- Multiplication by the actual parent cutoff preserves integrability of every local energy. -/
theorem integrable_plateau_local_energy (Q R : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R) a)
    (v : AHarmonicFunction a (openCubeSet R)) :
    Integrable (fun x => plateauOnSquare Q x * scalarVariationEnergyIntegrand a v x)
      (volume.restrict (openCubeSet R)) := by
  have hφ : MemLp (plateauOnSquare Q) ⊤ (volume.restrict (openCubeSet R)) :=
    MemLp.of_bound (lipschitzWith_plateauOnSquare Q).continuous.aestronglyMeasurable
      (12/7) (Filter.Eventually.of_forall (norm_plateauOnSquare_le Q))
  have he := (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).energy v
  exact ((hφ.mul (r := 1) (memLp_one_iff_integrable.mpr he)).integrable (by simp))

/-- The actual parent cutoff and local harmonic energies obey the source recovery Young bound. -/
theorem harmonic_plateau_cell_recovery (Q R : TriadicCube 2) {a : CoeffField 2} {lam Lam c : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet R) a) (hc : 0 < c) (hc1 : c < 1)
    (f v : AHarmonicFunction a (openCubeSet R)) :
    (1-c)*volumeAverage (openCubeSet R) (fun x => plateauOnSquare Q x * scalarVariationEnergyIntegrand a f x) -
      (1/c-1)*(12/7)*volumeAverage (openCubeSet R)
        (scalarVariationEnergyIntegrand a (squareHarmonicDifference R hEll f v)) ≤
      volumeAverage (openCubeSet R) (fun x => plateauOnSquare Q x * scalarVariationEnergyIntegrand a v x) := by
  have hk : 0 ≤ 1/c-1 := sub_nonneg.mpr ((le_div_iff₀ hc).mpr (by linarith))
  have hInt := ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hF := integrable_plateau_local_energy Q R hEll f
  have hV := integrable_plateau_local_energy Q R hEll v
  have hD := hInt.energy (squareHarmonicDifference R hEll f v)
  have havg := (cubeVolume_pos R).le
  unfold volumeAverage
  rw [volume_openCubeSet_toReal]
  have hpoint : ∀ᵐ x ∂volume.restrict (openCubeSet R),
      (1-c)*(plateauOnSquare Q x * scalarVariationEnergyIntegrand a f x) -
        (1/c-1)*(12/7)*scalarVariationEnergyIntegrand a (squareHarmonicDifference R hEll f v) x ≤
      plateauOnSquare Q x * scalarVariationEnergyIntegrand a v x := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    have h := mul_le_mul_of_nonneg_left (symmetric_energy_recovery_young hc (hEll.2 x hx)
      (v.toH1.grad x) (f.toH1.grad x)) (plateauOnSquare_nonneg Q x)
    have hdn := scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      (openCubeSet R) a hEll (squareHarmonicDifference R hEll f v) x hx
    have hM : plateauOnSquare Q x ≤ (12/7 : ℝ) :=
      (le_abs_self _).trans (norm_plateauOnSquare_le Q x)
    have hd := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM hk) hdn
    have heq : vecDot (v.toH1.grad x-f.toH1.grad x)
        (matVecMul (symmPart (a x)) (v.toH1.grad x-f.toH1.grad x)) =
        scalarVariationEnergyIntegrand a (squareHarmonicDifference R hEll f v) x := by
      unfold squareHarmonicDifference scalarVariationEnergyIntegrand
      rw [AHarmonicFunction.grad_subOfIntegrable]
      simp only [show v.toH1.grad x-f.toH1.grad x = -(f.toH1.grad x-v.toH1.grad x) by abel,
        Pi.sub_apply,matVecMul_neg,vecDot_neg_left,vecDot_neg_right,neg_neg]
    rw [heq] at h
    change plateauOnSquare Q x * ((1-c)*scalarVariationEnergyIntegrand a f x -
      (1/c-1)*scalarVariationEnergyIntegrand a (squareHarmonicDifference R hEll f v) x) ≤
      plateauOnSquare Q x * scalarVariationEnergyIntegrand a v x at h
    linarith only [h,hd]
  have hi := integral_mono_ae ((hF.const_mul _).sub (hD.const_mul _)) hV hpoint
  change (∫ x in openCubeSet R, (1-c)*(plateauOnSquare Q x * scalarVariationEnergyIntegrand a f x) -
    (1/c-1)*(12/7)*scalarVariationEnergyIntegrand a (squareHarmonicDifference R hEll f v) x) ≤ _ at hi
  rw [integral_sub (hF.const_mul _) (hD.const_mul _), integral_const_mul, integral_const_mul] at hi
  have hm := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr havg)
  nlinarith only [hm]

end ASDExplicitGamma.Cold
