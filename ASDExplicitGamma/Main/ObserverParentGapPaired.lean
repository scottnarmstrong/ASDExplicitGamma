module

public import ASDExplicitGamma.Main.DirectionalCovarianceTrace
public import ASDExplicitGamma.Main.ObserverBankCoefficient
public import ASDExplicitGamma.Main.ObserverParentGapTheta
public import ASDExplicitGamma.Main.ELinearObsPathwise
public import ASDExplicitGamma.Main.ELinearObsBridge
public import ASDExplicitGamma.Native.OldSignedPairedWeakTrace
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeRootTheta
public import ASDExplicitGamma.Inverse.BankDepthObservers
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Cold.SquarePartitionProjection
public import Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-! Observer-root pathwise paired parent row (primal plus reciprocal). -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Native ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Cold
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Scalar
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section
/-- Primal plus reciprocal tiled parent errors at the observer root against
twice the average of the local OLD-Theta carriers. -/
theorem observer_parent_paired_le_two_avg_theta
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (m : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hobs : ℕ) (h40 : hobs ≤ 40)
    (ω : CutoffSample 2) :
    descendantsAverage (originCube 2 (m + hobs)) (5 + hobs) (fun U =>
      oldSignedPrimalErrorSize (originCube 2 (m + hobs)) U M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2 +
      oldSignedReciprocalErrorSize (originCube 2 (m + hobs)) U M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2) ≤
      2 * descendantsAverage (originCube 2 (m + hobs)) (5 + hobs)
        (fun U => mixedOldTheta M m U t ω) := by
  classical
  set Q : TriadicCube 2 := originCube 2 (m + hobs) with hQ
  set σ : ℝ := (Annealed.sigmaBar M m : ℝ) with hσdef
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  set k := mainELinearObsCoefficient Q m t ω with hk
  set a : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ k with ha
  set d : ℕ := 5 + hobs with hd
  set α := Scalar.inverseHistoryDiscount with hαdef
  set C : ℝ := 3683 / 2500 with hC
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hα1 : α < 1 := hα.2
  have hpref : 0 ≤ 1 - α ^ 2 := by nlinarith [sq_nonneg α]
  have hpref' : 0 < 1 - α ^ 2 := by nlinarith [sq_nonneg α]
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ k
  have hfieldQ : ∀ x ∈ openCubeSet Q,
      a x = σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun x := fun x hx =>
    old_signed_obs_frame_eq_scaled_partial M Q m t ω x hx
  have hfieldU : ∀ U ∈ descendantsAtDepth Q d, ∀ x ∈ openCubeSet U,
      a x = σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun x :=
    fun U hU x hx => hfieldQ x (openCubeSet_subset_of_mem_descendantsAtDepth hU hx)
  have hEllU : ∀ U ∈ descendantsAtDepth Q d,
      IsEllipticFieldOn (M.nu / σ) (((M.nu / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (M.nu / σ))
        (openCubeSet U) a := fun U hU =>
    hEll.mono (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  let coef : ℕ → ℝ := fun j => mixedOldDepthCoefficient M m t j ω
  let raw : ℕ → TriadicCube 2 → ℝ := fun j U => rawWeakTraceSequence M m U t ω j
  let f : ℕ → TriadicCube 2 → ℝ := fun j U => (α ^ (2 * j) * coef j) * raw j U
  let Tbar : ℕ → ℝ := fun j => descendantsAverage Q (d + j)
    (fun U => traceDefect (openCubeSet U) a 1)
  have hTbar (j : ℕ) : Tbar j = descendantsAverage Q d (raw j) := by
    have htower := descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q d j
      (fun U => traceDefect (openCubeSet U) a 1)
    change descendantsAverage Q (d + j) _ = _ at htower
    show descendantsAverage Q (d + j) _ = _
    rw [htower]
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    exact obs_source_trace_average_eq M m t ht ω U a (hfieldU U hU) j
  have hrawnn (j : ℕ) (U : TriadicCube 2) : 0 ≤ raw j U :=
    raw_weak_trace_sequence_nonneg M m U t ⟨ht.1, ht.2⟩ ω j
  have hcoefnn (j : ℕ) : C ≤ coef j := by
    have hform := mixed_old_depth_coefficient_formula M m t j ω
    have hR : 0 ≤ mixedOldLocalDepthRemainder M m t j ω := by
      change 0 ≤ positiveSplitRemainder _ _ _
      exact (positive_split _ _ _).1
    have hg : 0 ≤ 2 * M.gamma * (j : ℝ) := by
      have := M.shellPrefix.gamma_pos
      positivity
    have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) :=
      Real.one_le_rpow (by norm_num) hg
    show C ≤ mixedOldDepthCoefficient M m t j ω
    rw [hform]
    nlinarith [hC]
  have hsumU : ∀ U ∈ descendantsAtDepth Q d, Summable (fun j => f j U) := by
    intro U hU
    have := obs_old_theta_core_summable M m t ht ω U a (hEllU U hU)
      (fun j => obs_source_trace_average_eq M m t ht ω U a (hfieldU U hU) j) hγ
    refine this.congr (fun j => ?_)
    simp only [f, raw, coef, mul_assoc, hαdef]
  have hpart := old_signed_partition_series Q d f hsumU
  have hfavg (j : ℕ) : descendantsAverage Q d (f j) =
      α ^ (2 * j) * coef j * Tbar j := by
    rw [hTbar j]
    exact descendantsAverage_mul_left Q d (α ^ (2 * j) * coef j) (raw j)
  have hSsum : Summable (fun j => α ^ (2 * j) * coef j * Tbar j) := by
    simpa only [hfavg] using hpart.1
  have hTheta : descendantsAverage Q d (fun U => mixedOldTheta M m U t ω) =
      (1 - α ^ 2) * ∑' j, α ^ (2 * j) * coef j * Tbar j := by
    have h1 : (fun U => mixedOldTheta M m U t ω) =
        fun U => (1 - α ^ 2) * ∑' j, f j U := by
      funext U
      unfold mixedOldTheta
      rw [← tsum_mul_left]
      apply tsum_congr
      intro j
      simp only [mixedOldThetaTerm, mixedDepthTraceAverage, f, raw, coef]
      ring
    rw [h1, descendantsAverage_mul_left]
    congr 1
    simp only [← hfavg]
    exact hpart.2.symm
  have hmod1 := old_signed_tiled_parent_paired_weak_bound Q d M.nu σ M.nu_pos hσ k
  have hbcoef (j : ℕ) : lemmaVInverseDepthMax Q a (d + j) ≤ coef j := by
    have hQroot : Q ∈ descendantsAtDepth (originCube 2 (m + 40)) (40 - hobs) := by
      have hscale : Q ∈ descendantsAtScale (originCube 2 (m + 40)) ((m + hobs : ℤ)) :=
        Algsuperdiff.Section3.Provider.ErrorComparison.originCube_mem_descendantsAtScale
          (d := 2) (by omega)
      have hdist : Int.toNat ((originCube 2 (m + 40)).scale - ((m + hobs : ℤ))) =
          40 - hobs := by
        simp only [originCube]
        omega
      rw [← hdist]
      rw [← descendantsAtScale_eq_descendantsAtDepth
        (originCube 2 (m + 40)) (by simp only [originCube]; omega)]
      exact hscale
    exact observer_depth_max_le_bank_coefficient M m t ht ω Q (40 - hobs) (d + j)
      hQroot a (hEll) hfieldQ j (by omega)
  have hb0 (j : ℕ) : 0 ≤ lemmaVInverseDepthMax Q a (d + j) :=
    lemmaVInverseDepthMax_nonneg Q a _
  have hT0 (j : ℕ) : 0 ≤ Tbar j := by
    rw [hTbar j]
    unfold descendantsAverage
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun U _ => hrawnn j U))
  have hLsum : Summable (fun j => α ^ (2 * j) * lemmaVInverseDepthMax Q a (d + j) * Tbar j) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hSsum
    · exact mul_nonneg (mul_nonneg (pow_nonneg hα0 _) (hb0 j)) (hT0 j)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbcoef j) (pow_nonneg hα0 _)) (hT0 j)
  have hchain : rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (d + j)) Tbar ≤
      (1 - α ^ 2) * ∑' j, α ^ (2 * j) * coef j * Tbar j := by
    unfold rawWeakTraceProxy
    apply mul_le_mul_of_nonneg_left _ hpref
    exact hLsum.tsum_le_tsum (fun j =>
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbcoef j) (pow_nonneg hα0 _)) (hT0 j)) hSsum
  rw [hTheta]
  have := hmod1
  exact this.trans (by linarith [hchain])

end
end ASDExplicitGamma.Main
