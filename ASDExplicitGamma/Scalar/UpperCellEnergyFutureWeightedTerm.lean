module

public import ASDExplicitGamma.Scalar.UpperCellEnergyFutureDepth
public import ASDExplicitGamma.Scalar.UpperCellEnergyFutureArithmetic

/-! Every positive term of the actual UPPER full-response history is
controlled by the corresponding complete-future bank term. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Native Inverse
open scoped ENNReal
noncomputable section

/-- The normalized source history discount, including its prefactor. -/
def upperCellHistoryWeight (j : ℕ) : ℝ :=
  (1-(3:ℝ)^(-(1/4:ℝ)))*((3:ℝ)^(-(1/4:ℝ)))^j

theorem upper_cell_history_weight_nonneg (j : ℕ) :
    0 ≤ upperCellHistoryWeight j := by
  have ha := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<3)
    (by norm_num : -(1/4:ℝ)<0)
  exact mul_nonneg (sub_nonneg.mpr ha.le) (pow_nonneg (Real.rpow_nonneg (by norm_num) _) _)

/-- A finite depth maximum can safely be viewed as a real variable without
losing either its value or its norm. -/
theorem upper_cell_future_depth_real_norm
    (M : ABKModel 2) (n : ℤ) (height j : ℕ) (weights : ℤ → ℝ) :
    eLpNorm (fun ω => (upperCellFutureDepthMax M n height j weights ω).toReal) 64
      (Cutoff.cutoffSampleLaw M).toMeasure =
    eLpNorm (upperCellFutureDepthMax M n height j weights) 64
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  rw [← eLpNorm_ofReal _ (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall (fun ω => ENNReal.ofReal_toReal
    (upper_cell_future_depth_max_ne_top M n height j weights ω))

/-- The actual weighted depth maximum has the exact full64 future-term cap. -/
theorem upper_cell_future_weighted_term_L64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ k < n, nativeInductionState M h k)
    (height j : ℕ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n+(height:ℤ)), 0 ≤ weights k ∧ weights k ≤ 1) :
    eLpNorm (fun ω => upperCellHistoryWeight j*
      (upperCellFutureDepthMax M n height j weights ω).toReal) 64
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (4*nativeFullResponse64FutureTerm M.gamma ((height:ℝ)+15) 15 j) := by
  change eLpNorm (upperCellHistoryWeight j •
    (fun ω => (upperCellFutureDepthMax M n height j weights ω).toReal)) 64 _ ≤ _
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal (upper_cell_history_weight_nonneg j),
    upper_cell_future_depth_real_norm]
  apply (mul_le_mul' le_rfl
    (upper_cell_future_depth_max_L64 M h hM hg n hpast height j weights hw)).trans_eq
  rw [show (9:ℝ≥0∞) = ENNReal.ofReal (9:ℝ) by norm_num,
    ← ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤9),
    ENNReal.ofReal_rpow_of_pos (pow_pos (by norm_num : (0:ℝ)<9) j),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (pow_nonneg (by norm_num) _) _),
    ← ENNReal.ofReal_mul (upper_cell_history_weight_nonneg j)]
  congr 1
  simpa only [upperCellHistoryWeight,Nat.cast_add,Nat.cast_ofNat,mul_assoc] using
    upper_cell_future_term_identity M.gamma height j

end
end ASDExplicitGamma.Scalar
