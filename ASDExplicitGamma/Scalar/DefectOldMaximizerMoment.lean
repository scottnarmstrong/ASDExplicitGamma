module

public import ASDExplicitGamma.Scalar.DefectOldMaximizerBank
public import ASDExplicitGamma.Scalar.DefectOldMaximizerAssembly
public import ASDExplicitGamma.Scalar.DefectOldMaximizerNumerics
public import ASDExplicitGamma.Native.OldSignedTiledParentWeak
public import ASDExplicitGamma.Scalar.SmoothFeedbackActualQuantities
public import ASDExplicitGamma.Scalar.DefectOldMaximizerTrace
public import ASDExplicitGamma.Scalar.SmoothFeedbackActualHyp
public import ASDExplicitGamma.Scalar.SmoothFeedbackActualFields
public import ASDExplicitGamma.Main.ObserverBankCoefficient
public import ASDExplicitGamma.Main.DirectionalPhysicalFlux
public import ASDExplicitGamma.Native.OldSignedHistoryBounds
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Scalar.SmoothFeedbackCellHistory
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.ObserverParentGapExpectation

/-! The correlated moment `E[B² · proxy] ≤ β² ξ` at the scalar observer. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Triadic Variational Native Inverse Gaussian
  Algsuperdiff.Section3 Numerics.Inverse ASDExplicitGamma.Main
open ASDExplicitGamma.Numerics.MainReturn
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth
noncomputable section

theorem scalar_trace_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ l ≤ m, nativeInductionState M h l)
    (Q : TriadicCube 2) (hQ : Q.scale = m + 129) (j : ℕ) :
    Integrable (fun ω => rawWeakTraceSequence M m Q 0 ω (134 + j))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, rawWeakTraceSequence M m Q 0 ω (134 + j) ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      inSourceMeanActual M m (5 + j) 0 := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hpast' : ∀ l < m + 1, nativeInductionState M h l := fun l hl => hpast l (by omega)
  have hcell (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q 134) :=
    mixed_bridge_obscell_trace_mean M h hM hγ (m + 1) hpast' m (by omega) 0
      ⟨le_rfl, zero_le_one⟩ 5 (le_refl 5) U (by
        rw [scale_eq_sub_of_mem_descendantsAtDepth hU, hQ]; push_cast; ring) j
  have hfun : (fun ω => rawWeakTraceSequence M m Q 0 ω (134 + j)) = fun ω =>
      ((descendantsAtDepth Q 134).card : ℝ)⁻¹ *
        ∑ U ∈ descendantsAtDepth Q 134, rawWeakTraceSequence M m U 0 ω j := by
    funext ω
    rw [trace_tower]
    rfl
  rw [hfun]
  have hint : ∀ U ∈ descendantsAtDepth Q 134,
      Integrable (fun ω => rawWeakTraceSequence M m U 0 ω j) μ := fun U hU => (hcell U hU).1
  refine ⟨(integrable_finsetSum _ hint).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ hint]
  have hconst : ∀ U ∈ descendantsAtDepth Q 134,
      (∫ ω, rawWeakTraceSequence M m U 0 ω j ∂μ) = inSourceMeanActual M m (5 + j) 0 :=
    fun U hU => (hcell U hU).2
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hc : ((descendantsAtDepth Q 134).card : ℝ) ≠ 0 := by
    have : (descendantsAtDepth Q 134).card ≠ 0 := by
      rw [descendantsAtDepth_card]; positivity
    exact_mod_cast this
  field_simp

theorem alpha_depth_le_B (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    Scalar.inverseHistoryDiscount ^ j * depthMax M m Q ω (134 + j) ≤
      bhist M m Q 134 ω := by
  classical
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  have hα := Scalar.inverse_history_discount_range
  have hαj : 0 < Scalar.inverseHistoryDiscount ^ j := pow_pos hα.1 j
  let phys := (Cutoff.coefficientCutoff M.nu m ω).toFun
  have hcell (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q 134) :
      Scalar.inverseHistoryDiscount ^ j * depthMax M m U ω j ≤ bhist M m Q 134 ω := by
    have hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet U) M.nu σ M.nu_pos hσ (oldCutoffSkewCoefficient m U ω)
    have h1 := actual_inverse_depth_discount_bound U _ hEll 1 zero_le_one j
    have h2 := smooth_feedback_source_history_maximum_member_le Q 134 M.nu σ
      (oldCutoffSkewCoefficient m Q ω) U hU
    rw [smooth_feedback_cell_coefficient_restrict m Q U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) ω] at h2
    unfold depthMax
    unfold bhist
    calc _ = Scalar.inverseHistoryDiscount ^ j * (1 * lemmaVInverseDepthMax U
          (responseFramePlanarCoefficientField M.nu σ (oldCutoffSkewCoefficient m U ω)) j) := by ring
      _ ≤ 1 * lemmaVInverseHistory U
          (responseFramePlanarCoefficientField M.nu σ (oldCutoffSkewCoefficient m U ω))
          ((3 : ℝ) ^ (1 / 4 : ℝ)) := h1
      _ ≤ _ := by rw [one_mul]; exact h2
  rw [depthMax_frame]
  have hD : lemmaVInverseDepthMax Q phys (134 + j) ≤
      bhist M m Q 134 ω / (Scalar.inverseHistoryDiscount ^ j * σ) := by
    unfold lemmaVInverseDepthMax
    apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q _)
    intro R hR
    have hs := descendants_split Q 134 j
    rw [hs, Finset.mem_biUnion] at hR
    obtain ⟨U, hU, hRU⟩ := hR
    have hgi := Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal
      (descendantsAtDepth U j) (fun R => Book.Ch02.matrixNorm
        (sigmaStarInvCoarse (openCubeSet R) phys)) hRU
    refine hgi.trans ?_
    rw [le_div_iff₀ (mul_pos hαj hσ)]
    have := hcell U hU
    rw [depthMax_frame] at this
    unfold lemmaVInverseDepthMax at this
    have this' : Scalar.inverseHistoryDiscount ^ j * (σ * Book.Ch02.finsetSupReal
        (descendantsAtDepth U j) (fun R => Book.Ch02.matrixNorm
          (sigmaStarInvCoarse (openCubeSet R) phys))) ≤ bhist M m Q 134 ω := this
    linarith [this']
  have := mul_le_mul_of_nonneg_left hD (mul_pos hαj hσ).le
  rw [mul_div_cancel₀ _ (mul_pos hαj hσ).ne'] at this
  calc _ = (Scalar.inverseHistoryDiscount ^ j * σ) * lemmaVInverseDepthMax Q phys (134 + j) := by
        ring
    _ ≤ _ := this

open ASDExplicitGamma.Numerics.Native in
theorem preCap_le_prefix (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) :
    mixedXiPreCap M ≤ mainSourceInversePrefix := by
  have htheta1 : theta M ≤ 1 := ASDExplicitGamma.Cold.cold_theta_le_one M hγ
  have hxi0 : 0 ≤ (inSourceXi5Pre : ℝ) := by
    norm_num [inSourceXi5Pre, ASDExplicitGamma.Numerics.Native.nativeSource5Result]
  have hxiCapQ : inSourceXi5Pre ≤ (140120486781 / 1000000000000 : ℚ) := by
    exact nativeSource5_caps.2.2.1.le
  have hxiCap : (inSourceXi5Pre : ℝ) ≤ (140120486781 / 1000000000000 : ℝ) := by
    have hxiCapR := (Rat.cast_le (K := ℝ)).2 hxiCapQ
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_one] using hxiCapR
  have hprefixQ : (140120486781 / 1000000000000 : ℚ) ≤
      observer1Panel0Data.initialInverseMean - (1 / 10 ^ 12 : ℚ) := by
    decide +kernel
  have hprefix : (140120486781 / 1000000000000 : ℝ) ≤ mainSourceInversePrefix := by
    change (140120486781 / 1000000000000 : ℝ) ≤
      (observer1Panel0Data.initialInverseMean : ℝ) - (1 / 10 ^ 12 : ℝ)
    have hprefixR := (Rat.cast_le (K := ℝ)).2 hprefixQ
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_one]
      using hprefixR
  rw [mixedXiPreCap]
  calc theta M * (inSourceXi5Pre : ℝ) ≤ 1 * (inSourceXi5Pre : ℝ) :=
        mul_le_mul_of_nonneg_right htheta1 hxi0
    _ = (inSourceXi5Pre : ℝ) := by ring
    _ ≤ (140120486781 / 1000000000000 : ℝ) := hxiCap
    _ ≤ mainSourceInversePrefix := hprefix

theorem alpha_baseline_le (M : ABKModel 2) (hγ : M.gamma ≤ gammaZero) (j : ℕ) :
    Scalar.inverseHistoryDiscount ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤ 1 := by
  have hgamma : 2 * M.gamma - 1 / 4 ≤ 0 := by
    dsimp [gammaZero] at hγ ⊢
    linarith
  have hpowEq : Scalar.inverseHistoryDiscount ^ j * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
      (3 : ℝ) ^ ((2 * M.gamma - 1 / 4) * (j : ℝ)) := by
    rw [Scalar.inverse_history_discount_power j,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [hpowEq]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 3)
    (mul_nonpos_of_nonpos_of_nonneg hgamma (Nat.cast_nonneg j))

end
end ASDExplicitGamma.Scalar
