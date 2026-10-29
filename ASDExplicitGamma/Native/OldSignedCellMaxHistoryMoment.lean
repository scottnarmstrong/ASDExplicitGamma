module

public import ASDExplicitGamma.Native.OldSignedCellMaxHistory

/-! Complete max-history summation for each OLD source cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The same summable depth profile pays every source cell maximum. -/
theorem old_signed_cell_max_history_moment_of_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ k ≤ n,nativeInductionState M h k)
    (Q : TriadicCube 2) (hQ : Q.scale = n-5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (B : ℕ → ℝ) (hB : ∀ j,0≤B j)
    (hBs : Summable (fun j => coldHistoryBeta^j*B j))
    (hcap : ∀ j,lpNorm (rawDepthFourLoadTrace M n (n-((5+j:ℕ):ℤ)) t)
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ B j) :
    eLpNorm (Main.mainOrdinaryTraceMaxHistory M n Q t)
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((1-inverseHistoryDiscount)*∑' j : ℕ,coldHistoryBeta^j*B j) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun j : ℕ => fun ω => ENNReal.ofReal (inverseHistoryDiscount^j)*
    Main.mainOrdinaryTraceDepthMax M n Q t j ω
  have hm (j : ℕ) : Measurable (F j) :=
    (Main.main_ordinary_trace_depth_max_measurable M n Q t j).const_mul _
  have hb (j : ℕ) : eLpNorm (F j) 20 μ ≤ ENNReal.ofReal (coldHistoryBeta^j*B j) := by
    rw [show F j = fun ω => ENNReal.ofReal (inverseHistoryDiscount^j)*
      Main.mainOrdinaryTraceDepthMax M n Q t j ω from rfl,
      history_constant_mul_L20 μ _ _ (Main.main_ordinary_trace_depth_max_measurable M n Q t j)]
    have hd := old_signed_cell_depth_max_L20_bound M h hM hg n hpast Q hQ t ht.1 ht.2 j
    calc
      _ ≤ ENNReal.ofReal (inverseHistoryDiscount^j)*
          (((9:ℝ≥0∞)^j)^(1/20:ℝ)*ENNReal.ofReal (lpNorm
            (rawDepthFourLoadTrace M n (n-((5+j:ℕ):ℤ)) t) 20 μ)) :=
        mul_le_mul_of_nonneg_left hd (by positivity)
      _ = ENNReal.ofReal (coldHistoryBeta^j)*ENNReal.ofReal (lpNorm
          (rawDepthFourLoadTrace M n (n-((5+j:ℕ):ℤ)) t) 20 μ) := by
        rw [←mul_assoc,old_signed_max_history_population_weight]
      _ ≤ ENNReal.ofReal (coldHistoryBeta^j)*ENNReal.ofReal (B j) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (hcap j)) (by positivity)
      _ = _ := (ENNReal.ofReal_mul (pow_nonneg coldHistoryBeta_pos.le j)).symm
  have hsum : (∑' j : ℕ,eLpNorm (F j) 20 μ) ≤ ENNReal.ofReal (∑' j : ℕ,coldHistoryBeta^j*B j) :=
    (ENNReal.tsum_le_tsum hb).trans_eq (ENNReal.ofReal_tsum_of_nonneg
      (fun j => mul_nonneg (pow_nonneg coldHistoryBeta_pos.le j) (hB j)) hBs).symm
  change eLpNorm (fun ω => ENNReal.ofReal (1-inverseHistoryDiscount)*∑' j : ℕ,F j ω) 20 μ ≤ _
  rw [history_constant_mul_L20 μ _ _ (Measurable.tsum hm)]
  exact (mul_le_mul_of_nonneg_left ((history_ennreal_tsum_L20 μ F hm).trans hsum)
    (by positivity)).trans_eq (ENNReal.ofReal_mul
      (sub_nonneg.mpr inverse_history_discount_range.2.le)).symm


end
end ASDExplicitGamma.Native
