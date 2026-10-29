module

public import ASDExplicitGamma.Main.DirectionalCovarianceTrace
public import ASDExplicitGamma.Main.ObserverBankCoefficient
public import ASDExplicitGamma.Main.ObserverParentGapPathwise
public import ASDExplicitGamma.Main.ELinearObsPathwise
public import ASDExplicitGamma.Main.ELinearObsBridge
public import ASDExplicitGamma.Native.OldSignedPairedWeakTrace
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeRootTheta
public import ASDExplicitGamma.Inverse.BankDepthObservers
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Cold.SquarePartitionProjection
public import Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-! Observer-root pathwise parent-gap row: tiled parent primal error against the
average of the local OLD-Theta carriers, with the subtracted term kept. -/

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

theorem obs_old_theta_core_summable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : CutoffSample 2) (Q : TriadicCube 2) (a : CoeffField 2)
    {lamA LamA : ℝ} (hEllA : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (htrace : ∀ j : ℕ,
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) =
        rawWeakTraceSequence M m Q t ω j)
    (hγ : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
      mixedOldDepthCoefficient M m t j ω *
        rawWeakTraceSequence M m Q t ω j) := by
  let α := Scalar.inverseHistoryDiscount
  let C : ℝ := 3683 / 2500
  let B : ℝ := mixedBridgeBstar M m t ω
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hT0 (j : ℕ) : 0 ≤ rawWeakTraceSequence M m Q t ω j :=
    raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j
  have hTsum : Summable (fun j : ℕ => α ^ j *
      rawWeakTraceSequence M m Q t ω j) := by
    have hs := old_signed_trace_depth_series_summable Q a hEllA
    apply hs.congr
    intro j
    rw [htrace j]
  have hB0 : 0 ≤ B := mixed_bridge_bstar_nonneg M m t ω
  have hR0 (j : ℕ) : 0 ≤ mixedOldLocalDepthRemainder M m t j ω := by
    change 0 ≤ positiveSplitRemainder _ _ _
    exact (positive_split _ _ _).1
  have hCformula (j : ℕ) := mixed_old_depth_coefficient_formula M m t j ω
  have hC0 (j : ℕ) : 0 ≤ mixedOldDepthCoefficient M m t j ω := by
    rw [hCformula j]
    exact add_nonneg (mul_nonneg (by norm_num [C])
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) (hR0 j)
  have hexp : -(1 / 4 : ℝ) + 2 * M.gamma < 0 := by
    dsimp [gammaZero] at hγ ⊢
    norm_num at hγ ⊢
    linarith
  have hq : α * (3 : ℝ) ^ (2 * M.gamma) < 1 := by
    have heq : α * (3 : ℝ) ^ (2 * M.gamma) =
        (3 : ℝ) ^ (-(1 / 4 : ℝ) + 2 * M.gamma) := by
      dsimp [α, Scalar.inverseHistoryDiscount]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [heq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hbaseq : α ^ 2 * (3 : ℝ) ^ (2 * M.gamma) ≤ α := by
    have hmul : α ^ 2 * (3 : ℝ) ^ (2 * M.gamma) =
        α * (α * (3 : ℝ) ^ (2 * M.gamma)) := by ring
    rw [hmul]
    calc
      α * (α * (3 : ℝ) ^ (2 * M.gamma)) ≤ α * 1 :=
        mul_le_mul_of_nonneg_left hq.le hα0
      _ = α := by ring
  have hpow (j : ℕ) :
      α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤ α ^ j := by
    have hpow3 : (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
        ((3 : ℝ) ^ (2 * M.gamma)) ^ j := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * M.gamma)) j,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      _ = (α ^ 2 * (3 : ℝ) ^ (2 * M.gamma)) ^ j := by
        rw [pow_mul, hpow3, ← mul_pow]
      _ ≤ α ^ j := pow_le_pow_left₀
        (mul_nonneg (sq_nonneg α)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) hbaseq j
  have hbaseline (j : ℕ) :
      α ^ (2 * j) * (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) ≤ C * α ^ j := by
    have hC : 0 ≤ C := by norm_num [C]
    calc
      _ = C * (α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by ring
      _ ≤ C * α ^ j := mul_le_mul_of_nonneg_left (hpow j) hC
  have hRdiscount (j : ℕ) :
      α ^ (2 * j) * mixedOldLocalDepthRemainder M m t j ω ≤ B * α ^ j := by
    have hR := mixed_old_local_depth_remainder_discount_le_global M m t ht j ω
    calc
      _ = α ^ j * (α ^ j * mixedOldLocalDepthRemainder M m t j ω) := by
        rw [show 2 * j = j + j by omega, pow_add]
        ring
      _ ≤ α ^ j * B := mul_le_mul_of_nonneg_left hR (pow_nonneg hα0 j)
      _ = B * α ^ j := by ring
  have hmajorant : Summable (fun j : ℕ => (C + B) *
      (α ^ j * rawWeakTraceSequence M m Q t ω j)) := hTsum.mul_left (C + B)
  apply Summable.of_nonneg_of_le
  · intro j
    exact mul_nonneg (mul_nonneg (pow_nonneg hα0 _) (hC0 j)) (hT0 j)
  · intro j
    have hcoef : α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω ≤
        (C + B) * α ^ j := by
      rw [hCformula j]
      calc
        α ^ (2 * j) *
            (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) +
              mixedOldLocalDepthRemainder M m t j ω) ≤
            C * α ^ j + B * α ^ j := by
          calc
            _ = α ^ (2 * j) *
                (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) +
                  α ^ (2 * j) * mixedOldLocalDepthRemainder M m t j ω := by ring
            _ ≤ C * α ^ j + B * α ^ j := add_le_add (hbaseline j) (hRdiscount j)
        _ = (C + B) * α ^ j := by ring
    calc
      α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω *
          rawWeakTraceSequence M m Q t ω j ≤
        ((C + B) * α ^ j) * rawWeakTraceSequence M m Q t ω j :=
          mul_le_mul_of_nonneg_right hcoef (hT0 j)
      _ = (C + B) *
          (α ^ j * rawWeakTraceSequence M m Q t ω j) := by ring
  · exact hmajorant


/-- Tiled parent primal error at the observer root `originCube 2 (m+hobs)`,
depth `5+hobs`, against the average of the local OLD-Theta carriers of the
depth-`5+hobs` cells, with the observer term kept. -/
theorem observer_parent_primal_le_avg_theta
    (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (m : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hobs : ℕ) (h40 : hobs ≤ 40)
    (ω : CutoffSample 2) :
    descendantsAverage (originCube 2 (m + hobs)) (5 + hobs) (fun U =>
      oldSignedPrimalErrorSize (originCube 2 (m + hobs)) U M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2) ≤
      descendantsAverage (originCube 2 (m + hobs)) (5 + hobs)
        (fun U => mixedOldTheta M m U t ω) -
      (3683 / 2500 : ℝ) * traceDefect (openCubeSet (originCube 2 (m + hobs)))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω)) 1 := by
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
  let A : ℝ := traceDefect (openCubeSet Q) a 1
  have hA0 : 0 ≤ A := Cold.coarse_square_traceDefect_nonneg Q hEll
  have hAle (j : ℕ) : A ≤ Tbar j :=
    old_signed_parent_trace_le_child Q (d + j) M.nu σ M.nu_pos hσ k
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
  -- sums
  have hP0 (j : ℕ) : 0 ≤ α ^ (2 * j) * coef j * A := by
    have : 0 ≤ coef j := (by norm_num : (0:ℝ) ≤ C).trans (hcoefnn j)
    positivity
  have hPle (j : ℕ) : α ^ (2 * j) * coef j * A ≤ α ^ (2 * j) * coef j * Tbar j := by
    have : 0 ≤ coef j := (by norm_num : (0:ℝ) ≤ C).trans (hcoefnn j)
    exact mul_le_mul_of_nonneg_left (hAle j) (by positivity)
  have hPsum : Summable (fun j => α ^ (2 * j) * coef j * A) :=
    Summable.of_nonneg_of_le hP0 hPle hSsum
  have hgeom : Summable (fun j : ℕ => (α ^ 2) ^ j) :=
    summable_geometric_of_lt_one (sq_nonneg α) (by nlinarith)
  have hPlow : C * A / (1 - α ^ 2) ≤ ∑' j, α ^ (2 * j) * coef j * A := by
    have hlow : ∀ j, α ^ (2 * j) * (C * A) ≤ α ^ (2 * j) * coef j * A := by
      intro j
      have := mul_le_mul_of_nonneg_right (hcoefnn j) hA0
      calc α ^ (2 * j) * (C * A) ≤ α ^ (2 * j) * (coef j * A) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hgs : Summable (fun j : ℕ => α ^ (2 * j) * (C * A)) := by
      simp only [pow_mul]
      exact hgeom.mul_right _
    have := hgs.tsum_le_tsum hlow hPsum
    have hval : ∑' j : ℕ, α ^ (2 * j) * (C * A) = C * A / (1 - α ^ 2) := by
      simp only [pow_mul]
      rw [tsum_mul_right, tsum_geometric_of_lt_one (sq_nonneg α) (by nlinarith)]
      field_simp
    rwa [hval] at this
  -- trace-proxy bound
  have hmod1 := old_signed_tiled_parent_primal_weak_anchor_bound Q d M.nu σ M.nu_pos hσ k
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
  have hTA0 (j : ℕ) : 0 ≤ Tbar j - A := sub_nonneg.mpr (hAle j)
  have hRsum : Summable (fun j => α ^ (2 * j) * coef j * (Tbar j - A)) := by
    refine (hSsum.sub hPsum).congr (fun j => ?_)
    ring
  have hLsum : Summable (fun j => α ^ (2 * j) * lemmaVInverseDepthMax Q a (d + j) *
      (Tbar j - A)) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hRsum
    · exact mul_nonneg (mul_nonneg (pow_nonneg hα0 _) (hb0 j)) (hTA0 j)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbcoef j) (pow_nonneg hα0 _)) (hTA0 j)
  have hchain : rawWeakTraceProxy (fun j => lemmaVInverseDepthMax Q a (d + j))
      (fun j => Tbar j - A) ≤ (1 - α ^ 2) * ∑' j, α ^ (2 * j) * coef j * (Tbar j - A) := by
    unfold rawWeakTraceProxy
    apply mul_le_mul_of_nonneg_left _ hpref
    exact hLsum.tsum_le_tsum (fun j =>
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbcoef j) (pow_nonneg hα0 _)) (hTA0 j)) hRsum
  have hsplit : ∑' j, α ^ (2 * j) * coef j * (Tbar j - A) =
      (∑' j, α ^ (2 * j) * coef j * Tbar j) - ∑' j, α ^ (2 * j) * coef j * A := by
    rw [← hSsum.tsum_sub hPsum]
    apply tsum_congr
    intro j
    ring
  have hfin : (1 - α ^ 2) * ∑' j, α ^ (2 * j) * coef j * (Tbar j - A) ≤
      (1 - α ^ 2) * (∑' j, α ^ (2 * j) * coef j * Tbar j) - C * A := by
    rw [hsplit, mul_sub]
    have : C * A ≤ (1 - α ^ 2) * ∑' j, α ^ (2 * j) * coef j * A := by
      have := mul_le_mul_of_nonneg_left hPlow hpref
      rwa [mul_div_cancel₀ _ hpref'.ne'] at this
    linarith
  rw [hTheta]
  exact hmod1.trans (hchain.trans hfin)

end
end ASDExplicitGamma.Main
