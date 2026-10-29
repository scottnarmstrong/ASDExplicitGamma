module

public import ASDExplicitGamma.Native.HeatVHEATRefinedVector
public import ASDExplicitGamma.Native.HeatInitialRefinedGaussian
public import ASDExplicitGamma.Native.HeatInitialProduct
public import ASDExplicitGamma.Native.HeatInitialCrossRow
public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.HeatFiniteBandCenters
public import ASDExplicitGamma.Numerics.Native.HeatParametersData
public import ASDExplicitGamma.Numerics.Native.Heat009Initial
public import ASDExplicitGamma.Native.HeatInitialDescendants
public import ASDExplicitGamma.Gaussian.NormalEvenMoments
public import ASDExplicitGamma.Native.HeatInitialCrossTypeTwo
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankLocal
public import ASDExplicitGamma.Inverse.ClippedMatrixLocal
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Variational.TraceDefect
public import ASDExplicitGamma.Inverse.BankLocalRootGeometry

/-! The depth-four local-root remainder for the refined start and its rare quadratic row. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3.Provider.BadEvents Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal NNReal BigOperators Nat

set_option linter.constructorNameAsVariable false

/-- The positive-truncation remainder for a child and its depth-four local root family,
read at the cutoff `m`. -/
noncomputable def nativeHeatOldInverseRemainderDepth4 (M : ABKModel 2)
    (Q : TriadicCube 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  inverseBankPopulationRemainder .localInverse (bankLocalRoots Q 4) M m (m + 1)
    (fun _ => 0) ω

theorem nativeHeatRefined_bankLocalRoots_scale (Q U : TriadicCube 2) (rmax : ℕ)
    (hU : U ∈ bankLocalRoots Q rmax) : U.scale ≤ Q.scale ∧ Q.scale - U.scale ≤ rmax := by
  classical
  rw [bankLocalRoots] at hU
  rcases Finset.mem_insert.mp hU with rfl | hU
  · exact ⟨le_rfl, by omega⟩
  obtain ⟨r, hr', hU⟩ := Finset.mem_biUnion.mp hU
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  have hrr := Finset.mem_range.mp hr'
  omega

private theorem nativeHeatRefined_rootInverseResponse_local
    (M : ABKModel 2) (m : ℤ) (V : TriadicCube 2)
    {U : Set (Vec 2)} (hVU : cubeSet V ⊆ U) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M m U) inferInstance
      (rootInverseResponse M V m (m + 1) (fun _ => 0)) := by
  let A : Cutoff.CutoffSample 2 → FullBlockMat 2 := fun ω =>
    toFullBlockMat (coarseBlockMatrix (cubeSet V)
      (Cutoff.coefficientCutoff M.nu m ω).toFun)
  letI : MeasurableSpace (Cutoff.CutoffSample 2) :=
    Cutoff.cutoffSampleLocalSigma M m U
  have hA : Measurable A := by
    simpa [A] using clipped_coarse_local_measurable M m V hVU
  have hproj : Measurable (fun X : FullBlockMat 2 =>
      fun i j : Fin 2 => X (Sum.inr i) (Sum.inr j)) := by
    apply Measurable.of_eval_matrix
    intro i j
    exact (measurable_pi_apply (Sum.inr j)).comp
      (measurable_pi_apply (Sum.inr i))
  let L : Mat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
    { toFun := fun B => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) B
      map_add' := fun X Y => map_add (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) X Y
      map_smul' := fun c X => map_smul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) c X }
  have hnorm : Measurable (fun B : Mat 2 =>
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) B‖) :=
    L.continuous_of_finiteDimensional.norm.measurable
  have hresponse : Measurable (fun X : FullBlockMat 2 =>
      (Annealed.sigmaBar M m : ℝ) *
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          (fun i j => X (Sum.inr i) (Sum.inr j))‖) :=
    measurable_const.mul (hnorm.comp hproj)
  have hresult := hresponse.comp hA
  convert hresult using 1
  funext ω
  have hcoef : attenuatedCoefficient M m (m + 1) (fun _ => 0) ω =
      Cutoff.coefficientCutoff M.nu m ω := by
    funext x
    simp [attenuatedCoefficient]
  simp [A, rootInverseResponse, hcoef, toFullBlockMat]

/-- The local OLD inverse remainder is measurable from the cutoff past on its
cell, so it can be paired with the independent physical q3 future block. -/
theorem nativeHeatRefined_oldInverseRemainderDepth4_local (M : ABKModel 2)
    (Q : TriadicCube 2) (m : ℤ) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M m (cubeSet Q)) inferInstance
      (nativeHeatOldInverseRemainderDepth4 M Q m) := by
  classical
  let I := bankLocalRoots Q 4
  let μspace : MeasurableSpace (Cutoff.CutoffSample 2) :=
    Cutoff.cutoffSampleLocalSigma M m (cubeSet Q)
  letI : MeasurableSpace (Cutoff.CutoffSample 2) := μspace
  have hroot (V : TriadicCube 2) (hV : V ∈ I) : cubeSet V ⊆ cubeSet Q := by
    change V ∈ bankLocalRoots Q 4 at hV
    rw [bankLocalRoots, Finset.mem_insert] at hV
    rcases hV with hV | hV
    · simpa [hV]
    · rw [Finset.mem_biUnion] at hV
      obtain ⟨j, hj, hdesc⟩ := hV
      exact cubeSet_subset_of_mem_descendantsAtDepth hdesc
  have hbankHistory (V : TriadicCube 2) (hV : V ∈ I) :
      Measurable (bankRootInverseHistory V M m (m + 1) (fun _ => 0)) := by
    unfold bankRootInverseHistory
    apply Measurable.const_mul
    apply Measurable.tsum
    intro j
    apply Measurable.const_mul
    unfold bankFiniteRootResponseMax
    apply history_finite_max_measurable
    intro W
    have hW : cubeSet W.1 ⊆ cubeSet V :=
      cubeSet_subset_of_mem_descendantsAtDepth W.2
    exact (ENNReal.continuous_ofReal.measurable.comp
      (nativeHeatRefined_rootInverseResponse_local M m W.1
        (hW.trans (hroot V hV))))
  have hhistory : Measurable (bankFiniteRootHistoryMax I M m (m + 1)
      (fun _ => 0)) := by
    unfold bankFiniteRootHistoryMax
    apply history_finite_max_measurable
    intro V
    exact hbankHistory V.1 V.2
  change Measurable (fun ω => positiveSplitRemainder
    (bankFiniteRootHistoryMax I M m (m + 1) (fun _ => 0) ω).toReal
    (inverseBankA .localInverse : ℝ) (1 / 2000))
  exact measurable_const.max
    (((ENNReal.measurable_toReal.comp hhistory).sub_const
      (inverseBankA .localInverse : ℝ)).sub_const (1 / 2000))

/-- Native states at the strict past provide the actual OLD local bank for a
child at cutoff `m`. Its root trace defect has the baseline-plus-rare profile
from the local inverse row, and the remainder keeps the source L128 reserve. -/
theorem nativeHeatRefined_oldInverseTraceProfileDepth4_of_states
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m : ℤ)
    (hscale : Q.scale + 1 = m)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    Measurable (nativeHeatOldInverseRemainderDepth4 M Q m) ∧
      (∀ ω, 0 ≤ nativeHeatOldInverseRemainderDepth4 M Q m ω) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        Matrix.trace (frameMatrix (Annealed.sigmaBar M m : ℝ)
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu m ω).toFun)).lowerRight ≤
          2 * ((inverseBankCap .localInverse : ℝ) +
            nativeHeatOldInverseRemainderDepth4 M Q m ω)) ∧
      eLpNorm (nativeHeatOldInverseRemainderDepth4 M Q m) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) := by
  let s := bankLocalRoots Q 4
  let w : ℤ → ℝ := fun _ => 0
  have hgeom := bank_local_roots_geometry Q 4 (by norm_num)
  have hscaleRoots : ∀ U ∈ s, U.scale ≤ m ∧ m - U.scale ≤ 5 := by
    intro U hU
    have hU' := nativeHeatRefined_bankLocalRoots_scale Q U 4 hU
    constructor <;> omega
  have hweights : ∀ k ∈ Finset.Ioc m (m + 1), 0 ≤ w k ∧ w k ≤ 1 := by
    intro k hk
    simp [w]
  have hmeans := bank_inverse_mean_inputs_of_states M h hM hg m hpast
  have hbank : InverseBankConclusion M .localInverse s m (m + 1) w :=
    local_inverse_bank M h hM hg s m (m + 1) (by omega) w hweights
      hscaleRoots hgeom.2 hpast hmeans.2
  have hQ : Q ∈ s := by
    exact bank_local_roots_self Q 4
  have hcap : 0 ≤ (inverseBankCap .localInverse : ℝ) := by
    norm_num [inverseBankCap]
  have hCoeff (ω : Cutoff.CutoffSample 2) :
      attenuatedCoefficient M m (m + 1) w ω =
        (partialInsertedCoefficient M m 0 ω).toFun := by
    funext x
    simp [attenuatedCoefficient, w, partialInsertedCoefficient]
  have hresponse : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      rootInverseResponse M Q m (m + 1) w ω ≤
        (inverseBankCap .localInverse : ℝ) + nativeHeatOldInverseRemainderDepth4 M Q m ω := by
    filter_upwards [hbank.history_le] with ω hsplit
    obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact _
      (isBounded_cubeSet Q).isCompact_closure
    have hEllPartial : IsEllipticFieldOn M.nu
        (((2 : ℝ) * 2 * (partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
        (openCubeSet Q) (partialInsertedCoefficient M m 0 ω) :=
      partialInsertedCoefficient_isEllipticFieldOn M ell m ω
        (by norm_num) (measurableSet_openCubeSet Q)
        (fun x hx => hK (subset_closure (openCubeSet_subset_cubeSet Q hx)))
    have hEll : IsEllipticFieldOn M.nu
        (((2 : ℝ) * 2 * (partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
        (openCubeSet Q) (attenuatedCoefficient M m (m + 1) w ω) := by
      simpa only [hCoeff ω] using hEllPartial
    have hroot := bank_root_response_le_history Q M m (m + 1) w ω hEll
    have hmember := bank_member_history_le M s Q hQ m (m + 1) w ω
    have hENN : ENNReal.ofReal
        (rootInverseResponse M Q m (m + 1) w ω) ≤
          ENNReal.ofReal (inverseBankCap .localInverse : ℝ) +
            ENNReal.ofReal (nativeHeatOldInverseRemainderDepth4 M Q m ω) :=
      hroot.trans (hmember.trans (by simpa [s, w, nativeHeatOldInverseRemainderDepth4] using hsplit))
    have hrem0 : 0 ≤ nativeHeatOldInverseRemainderDepth4 M Q m ω :=
      hbank.remainder_nonneg ω
    have hupper : ENNReal.ofReal (inverseBankCap .localInverse : ℝ) +
        ENNReal.ofReal (nativeHeatOldInverseRemainderDepth4 M Q m ω) =
          ENNReal.ofReal ((inverseBankCap .localInverse : ℝ) +
            nativeHeatOldInverseRemainderDepth4 M Q m ω) :=
      (ENNReal.ofReal_add hcap hrem0).symm
    have hENN' : ENNReal.ofReal
        (rootInverseResponse M Q m (m + 1) w ω) ≤
          ENNReal.ofReal ((inverseBankCap .localInverse : ℝ) +
            nativeHeatOldInverseRemainderDepth4 M Q m ω) := hENN.trans_eq hupper
    have hreal := ENNReal.toReal_mono
      (ENNReal.ofReal_ne_top : ENNReal.ofReal
        ((inverseBankCap .localInverse : ℝ) + nativeHeatOldInverseRemainderDepth4 M Q m ω) ≠ ∞)
      hENN'
    have hresponse0 : 0 ≤ rootInverseResponse M Q m (m + 1) w ω :=
      mul_nonneg (Annealed.sigmaBar_characterization M m).1.le (norm_nonneg _)
    rw [ENNReal.toReal_ofReal hresponse0,
      ENNReal.toReal_ofReal (add_nonneg hcap hrem0)] at hreal
    exact hreal
  have htrace : ∀ ω,
      Matrix.trace (frameMatrix (Annealed.sigmaBar M m : ℝ)
        (coarseBlockMatrix (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu m ω).toFun)).lowerRight ≤
        2 * rootInverseResponse M Q m (m + 1) w ω := by
    intro ω
    let A := (coarseBlockMatrix (cubeSet Q)
      (attenuatedCoefficient M m (m + 1) w ω)).lowerRight
    have h0 := (le_abs_self (A 0 0)).trans (clipped_matrix_entry_abs_le_norm A 0 0)
    have h1 := (le_abs_self (A 1 1)).trans (clipped_matrix_entry_abs_le_norm A 1 1)
    have hσ := (Annealed.sigmaBar_characterization M m).1.le
    have hh := add_le_add
      (mul_le_mul_of_nonneg_left h0 hσ)
      (mul_le_mul_of_nonneg_left h1 hσ)
    have hpart : (partialInsertedCoefficient M m 0 ω).toFun =
        (Cutoff.coefficientCutoff M.nu m ω).toFun := by
      funext x
      simp [partialInsertedCoefficient]
    have hA : A = (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun).lowerRight := by
      change (coarseBlockMatrix (cubeSet Q)
        (attenuatedCoefficient M m (m + 1) w ω)).lowerRight = _
      rw [hCoeff ω, hpart]
    calc
      Matrix.trace (frameMatrix (Annealed.sigmaBar M m : ℝ)
          (coarseBlockMatrix (cubeSet Q)
            (Cutoff.coefficientCutoff M.nu m ω).toFun)).lowerRight
          = (Annealed.sigmaBar M m : ℝ) * A 0 0 +
              (Annealed.sigmaBar M m : ℝ) * A 1 1 := by
                simp [frameMatrix, Matrix.trace, Fin.sum_univ_two, A, hA]
      _ ≤ 2 * ((Annealed.sigmaBar M m : ℝ) *
          ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A‖) := by
            nlinarith only [hh]
      _ = 2 * rootInverseResponse M Q m (m + 1) w ω := by
            simp [rootInverseResponse, A]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Measurable
      (inverseBankPopulationRemainder .localInverse (bankLocalRoots Q 4) M m (m + 1)
        (fun _ => 0))
    exact hbank.remainder_measurable
  · intro ω
    simpa [nativeHeatOldInverseRemainderDepth4, s, w] using hbank.remainder_nonneg ω
  · filter_upwards [hresponse] with ω hω
    have hr0 : 0 ≤ nativeHeatOldInverseRemainderDepth4 M Q m ω :=
      hbank.remainder_nonneg ω
    calc
      _ ≤ 2 * rootInverseResponse M Q m (m + 1) w ω := htrace ω
      _ ≤ 2 * ((inverseBankCap .localInverse : ℝ) +
          nativeHeatOldInverseRemainderDepth4 M Q m ω) := by
            exact mul_le_mul_of_nonneg_left hω (by norm_num)
  · change eLpNorm
      (inverseBankPopulationRemainder .localInverse (bankLocalRoots Q 4) M m (m + 1)
        (fun _ => 0)) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤ _
    exact hbank.remainder_L128


private theorem nativeHeat_standardEvenMoment_le_gm (k : ℕ)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) ≤
      ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) ^ k := by
  have hdouble : Nat.factorial (2 * k) =
      (2 ^ k * Nat.factorial k) * (2 * k - 1)‼ := by
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * k - 1)
    have hidx : 2 * k - 1 + 1 = 2 * k := by omega
    rw [hidx, Nat.doubleFactorial_two_mul] at h
    exact h
  have hdoubleR : (Nat.factorial (2 * k) : ℝ) =
      (2 : ℝ) ^ k * (Nat.factorial k : ℝ) * ((2 * k - 1)‼ : ℝ) := by
    exact_mod_cast hdouble
  have hratio : ((2 * k - 1)‼ : ℝ) =
      ((Nat.factorial (2 * k) : ℝ) /
        ((2 : ℝ) ^ k * (Nat.factorial k : ℝ))) := by
    have hden : (2 : ℝ) ^ k * (Nat.factorial k : ℝ) ≠ 0 := by positivity
    rw [hdoubleR]
    field_simp
  have hstd : (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) =
      ((Nat.factorial (2 * k) : ℝ) /
        ((2 : ℝ) ^ k * (Nat.factorial k : ℝ))) := by
    rw [normal_even_moment_eq_doubleFactorial k hk1, hratio]
  have hgmQ :
      (Nat.factorial (2 * k) : ℚ) / (2 ^ k * Nat.factorial k) ≤
        (nativeHeatParametersData.gm.getD k 0) ^ k := by
    interval_cases k
    · simpa using nativeHeatGM01_powers.2
    · simpa using nativeHeatGM02_powers.2
    · simpa using nativeHeatGM03_powers.2
    · simpa using nativeHeatGM04_powers.2
    · simpa using nativeHeatGM05_powers.2
    · simpa using nativeHeatGM06_powers.2
    · simpa using nativeHeatGM07_powers.2
    · simpa using nativeHeatGM08_powers.2
    · simpa using nativeHeatGM09_powers.2
    · simpa using nativeHeatGM10_powers.2
    · simpa using nativeHeatGM11_powers.2
    · simpa using nativeHeatGM12_powers.2
    · simpa using nativeHeatGM13_powers.2
    · simpa using nativeHeatGM14_powers.2
    · simpa using nativeHeatGM15_powers.2
    · simpa using nativeHeatGM16_powers.2
    · simpa using nativeHeatGM17_powers.2
    · simpa using nativeHeatGM18_powers.2
    · simpa using nativeHeatGM19_powers.2
    · simpa using nativeHeatGM20_powers.2
  have hgmR :
      ((Nat.factorial (2 * k) : ℝ) /
        ((2 : ℝ) ^ k * (Nat.factorial k : ℝ))) ≤
        ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) ^ k := by
    have hcast :
        (((Nat.factorial (2 * k) : ℚ) / (2 ^ k * Nat.factorial k) : ℚ) : ℝ) ≤
          (((nativeHeatParametersData.gm.getD k 0) ^ k : ℚ) : ℝ) := by
      exact_mod_cast hgmQ
    simpa using hcast
  rw [hstd]
  exact hgmR

private theorem nativeHeat_gaussianEvenMoment_le_gm (v : ℝ≥0) (k : ℕ)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 v) ≤
      (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) * (v : ℝ)) ^ k := by
  rw [gaussianReal_eq_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hscale : Real.sqrt (v : ℝ) ^ (2 * k) = (v : ℝ) ^ k := by
    calc
      Real.sqrt (v : ℝ) ^ (2 * k) = (Real.sqrt (v : ℝ) ^ 2) ^ k := by rw [pow_mul]
      _ = (v : ℝ) ^ k := congrArg (fun z : ℝ => z ^ k) (Real.sq_sqrt v.property)
  rw [hscale]
  have hbound := mul_le_mul_of_nonneg_left
    (nativeHeat_standardEvenMoment_le_gm k hk1 hk20) (pow_nonneg v.property k)
  calc
    _ ≤ (v : ℝ) ^ k * (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) ^ k) := hbound
    _ = (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) ^ k) * (v : ℝ) ^ k := by ring

private theorem nativeHeat_gm_nonneg (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    0 ≤ ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) := by
  interval_cases k <;> first
    | exact_mod_cast nativeHeatGM01_powers.1
    | exact_mod_cast nativeHeatGM02_powers.1
    | exact_mod_cast nativeHeatGM03_powers.1
    | exact_mod_cast nativeHeatGM04_powers.1
    | exact_mod_cast nativeHeatGM05_powers.1
    | exact_mod_cast nativeHeatGM06_powers.1
    | exact_mod_cast nativeHeatGM07_powers.1
    | exact_mod_cast nativeHeatGM08_powers.1
    | exact_mod_cast nativeHeatGM09_powers.1
    | exact_mod_cast nativeHeatGM10_powers.1
    | exact_mod_cast nativeHeatGM11_powers.1
    | exact_mod_cast nativeHeatGM12_powers.1
    | exact_mod_cast nativeHeatGM13_powers.1
    | exact_mod_cast nativeHeatGM14_powers.1
    | exact_mod_cast nativeHeatGM15_powers.1
    | exact_mod_cast nativeHeatGM16_powers.1
    | exact_mod_cast nativeHeatGM17_powers.1
    | exact_mod_cast nativeHeatGM18_powers.1
    | exact_mod_cast nativeHeatGM19_powers.1
    | exact_mod_cast nativeHeatGM20_powers.1


/-- A degree-k moment is controlled by the L128 norm on a probability space. -/
private theorem nativeHeat_lintegral_enorm_natPow_le_eLpNorm128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (k : ℕ)
    (hk1 : 1 ≤ k) (hk128 : k ≤ 128) :
    ∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ ≤ eLpNorm f 128 μ ^ k := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk128R : (k : ℝ) ≤ 128 := by exact_mod_cast hk128
  have hmono : eLpNorm' f (k : ℝ) μ ≤ eLpNorm' f 128 μ :=
    eLpNorm'_le_eLpNorm'_of_exponent_le hkpos hk128R μ hf
  have h128 : eLpNorm f 128 μ = eLpNorm' f 128 μ := by
    simpa using (eLpNorm_eq_eLpNorm' (p := (128 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf)
  calc
    _ = eLpNorm' f (k : ℝ) μ ^ (k : ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos
    _ ≤ eLpNorm' f 128 μ ^ (k : ℝ) :=
      ENNReal.rpow_le_rpow hmono (by positivity)
    _ = eLpNorm f 128 μ ^ k := by rw [← h128, ENNReal.rpow_natCast]


/-- A finite average is a contraction on every real `Lᵖ`, `p ≥ 1`. This is
stated for an abstract finite index so consumers can use large structured
partitions without unfolding their enumeration. -/
private theorem nativeHeat_eLpNorm'_average_le
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [Nonempty ι]
    {μ : Measure α} {p cap : ℝ} (hp : 1 ≤ p) (hcap0 : 0 ≤ cap)
    (f : ι → α → ℝ) (hf : ∀ i, Measurable (f i))
    (hbound : ∀ i, eLpNorm' (f i) p μ ≤ ENNReal.ofReal cap) :
    eLpNorm' (fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ω) p μ ≤
      ENNReal.ofReal cap := by
  let N : ℝ := (Fintype.card ι : ℝ)
  let S : α → ℝ := ∑ i, f i
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  have hN0 : 0 ≤ N := hNpos.le
  have hNinv0 : 0 ≤ N⁻¹ := inv_nonneg.mpr hN0
  have hsumLp : eLpNorm' S p μ ≤ ∑ i, eLpNorm' (f i) p μ := by
    change eLpNorm' (∑ i, f i) p μ ≤ _
    exact eLpNorm'_sum_le (μ := μ) (f := f) (s := Finset.univ)
      (fun i _ => (hf i).aestronglyMeasurable) hp
  have hsumCap : ∑ i, eLpNorm' (f i) p μ ≤ ENNReal.ofReal (N * cap) := by
    calc
      _ ≤ ∑ i, ENNReal.ofReal cap := Finset.sum_le_sum fun i _ => hbound i
      _ = (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal cap := by simp
      _ = ENNReal.ofReal (N * cap) := by
        rw [ENNReal.ofReal_mul hN0]
        simp [N, ENNReal.ofReal_natCast]
  have hpoint : (fun ω => N⁻¹ * S ω) = N⁻¹ • S := by
    funext ω
    simp [smul_eq_mul]
  have hscaleLp :
      eLpNorm' (N⁻¹ • S) p μ = ENNReal.ofReal N⁻¹ * eLpNorm' S p μ :=
    by
      simpa only [Real.enorm_eq_ofReal hNinv0] using
        (eLpNorm'_const_smul N⁻¹ (by positivity : 0 < p) (f := S) (μ := μ))
  have hsumBound : eLpNorm' S p μ ≤ ENNReal.ofReal (N * cap) :=
    hsumLp.trans hsumCap
  have havgSmul : eLpNorm' (N⁻¹ • S) p μ ≤ ENNReal.ofReal cap := by
    rw [hscaleLp]
    calc
      _ ≤ ENNReal.ofReal N⁻¹ * ENNReal.ofReal (N * cap) :=
        mul_le_mul_of_nonneg_left hsumBound (by positivity)
      _ = ENNReal.ofReal cap := by
        rw [← ENNReal.ofReal_mul hNinv0]
        congr 1
        field_simp [hNpos.ne']
  have havg :
      eLpNorm' (fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ω) p μ ≤
        ENNReal.ofReal cap := by
    rw [show (fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ω) =
      (fun ω => N⁻¹ * S ω) by
        funext ω
        simp [N, S, Fintype.sum_apply]]
    rw [hpoint]
    simpa [N, S] using havgSmul
  exact havg



/-- The actual normalized fresh coordinate at a depth-ten child has the configured scalar
Gaussian moments, at the heat-inflated variance. -/
theorem nativeHeatQ3RefinedZ_moment_le_gm
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1))
    (ij : Fin (3^10) × Fin (3^10)) (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceZ M m ω (finProdFinEquiv ij)‖ₑ ^
        (2 * (k : ℝ)) ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
        (nativeHeat009Variance : ℝ)) ^ (k : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let K := nativeHeatQ3GridCenterSet 10
  let shells : Fin 9 → ℤ := fun d => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)
  let T : Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 := fun ω =>
    ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
      (Cutoff.translateCutoffSample
        (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) ω)
  let S : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    modelBand K shells ω (nativeHeatQ3GridCenterPoint 10 ij)
  let B : ℝ := Real.rpow 3 (M.gamma * ((m + 10 : ℤ) : ℝ))
  let σ : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ)
  let α : ℝ := Real.sqrt (1 + (nativeHeatTheta : ℝ)) * B / σ
  let x : Vec 2 := q3GridCenterVector 10 ij
  let cov : Fin 9 → ℝ := fun d => q3ShellCovariance M h (shells d) x x
  let vcan : ℝ≥0 := ∑ d, Real.toNNReal (cov d)
  let vscaled : ℝ≥0 := ⟨α ^ 2, sq_nonneg α⟩ * vcan
  let Z : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    nativeHeatQ3RefinedCarrierSourceZ M m ω (finProdFinEquiv ij)
  let F : ℝ → ℝ≥0∞ := fun y => ‖y‖ₑ ^ (2 * (k : ℝ))
  have hθ : 0 ≤ 1 + (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  have hshells : Function.Injective shells := by
    intro d₁ d₂ hde
    apply Fin.ext
    dsimp [shells] at hde
    omega
  have hSmeas : Measurable S := by
    dsimp [S, K]
    exact (ContinuousMap.evalCLM ℝ (nativeHeatQ3GridCenterPoint 10 ij)).continuous.measurable.comp
      (measurable_modelBand (nativeHeatQ3GridCenterSet 10) shells)
  have hcanonical : μ.map S = gaussianReal 0 vcan := by
    have h := nativeHeat_q3FiniteBand_gridCombination_law M h hM
      (b := 9) shells hshells 10 (J := Unit)
      (x := fun _ : Unit => ij) (t := fun _ : Unit => (1 : ℝ))
    simpa [μ, S, K, shells, vcan, cov, x] using h
  have hBsq : B ^ 2 = (3 : ℝ) ^ (2 * M.gamma * ((m + 10 : ℤ) : ℝ)) := by
    dsimp [B]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hZ (ω : Cutoff.CutoffSample 2) : Z ω = α * S (T ω) := by
    dsimp only [Z, α, σ, B, S, T, K, shells]
    unfold nativeHeatQ3RefinedCarrierSourceZ
    rw [nativeHeatQ3RefinedFreshRaw_eq_scaled_band M m ω ij]
    ring
  have hvcan : (vcan : ℝ) = ∑ d, cov d := by
    rw [NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact Real.coe_toNNReal _
      (q3ShellCovariance_nonnegative M h (shells d) x x)
  have hscaleCap : α ^ 2 = (1 + (nativeHeatTheta : ℝ)) *
      ((3 : ℝ) ^ (2 * M.gamma * ((m + 10 : ℤ) : ℝ)) / σ ^ 2) := by
    dsimp only [α]
    rw [div_pow, mul_pow, Real.sq_sqrt hθ, hBsq]
    ring
  let e : ℝ := (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (9 : ℝ))
  have hterm (d : Fin 9) : α ^ 2 * cov d ≤ (1 + (nativeHeatTheta : ℝ)) * e := by
    have hcov : cov d = (h * (3 : ℝ) ^ (M.gamma * (shells d : ℝ))) ^ 2 := by
      dsimp [cov, x]
      rw [q3ShellCovariance_diagonal]
      rw [nativeHeat_q3ShellAmplitude_sq]
    have hsource := nativeHeatRefined_shellCap M h (m + 1) 1 (by norm_num) d hstate
    have hlabel : (((m + 1 : ℤ) + 9 : ℤ) : ℝ) = ((m + 10 : ℤ) : ℝ) := by
      push_cast; ring
    rw [hlabel] at hsource
    rw [hscaleCap, hcov]
    have := mul_le_mul_of_nonneg_left hsource hθ
    simp only [one_mul] at this
    calc
      _ = (1 + (nativeHeatTheta : ℝ)) *
          ((3 : ℝ) ^ (2 * M.gamma * ((m + 10 : ℤ) : ℝ)) / σ ^ 2 *
            (h * (3 : ℝ) ^ (M.gamma * (shells d : ℝ))) ^ 2) := by ring
      _ ≤ _ := by simpa [σ, shells, e] using this
  have hvscaled : (vscaled : ℝ) ≤ (nativeHeat009Variance : ℝ) := by
    change α ^ 2 * (vcan : ℝ) ≤ _
    rw [hvcan]
    calc
      α ^ 2 * ∑ d, cov d = ∑ d, α ^ 2 * cov d := by rw [Finset.mul_sum]
      _ ≤ ∑ d : Fin 9, (1 + (nativeHeatTheta : ℝ)) * e :=
        Finset.sum_le_sum fun d hd => hterm d
      _ = 9 * ((1 + (nativeHeatTheta : ℝ)) * e) := by simp
      _ ≤ (nativeHeat009Variance : ℝ) := by
        simpa [e] using nativeHeat009_scaledVariance_cap M hgamma
  have hmapScaled : (μ.map S).map (fun y : ℝ => α * y) =
      μ.map (fun ω => α * S ω) := by
    rw [show (fun ω => α * S ω) = (fun y : ℝ => α * y) ∘ S by rfl]
    exact Measure.map_map (μ := μ) (g := fun y : ℝ => α * y) (f := S)
      (by fun_prop) hSmeas
  have hscaled : μ.map (fun ω => α * S ω) = gaussianReal 0 vscaled := by
    calc
      _ = (μ.map S).map (fun y : ℝ => α * y) := hmapScaled.symm
      _ = gaussianReal 0 vscaled := by
        rw [hcanonical, gaussianReal_map_const_mul]
        simp only [mul_zero]
        rfl
  have hFmeas : Measurable F := by
    dsimp [F]
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_enorm
  let G : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω => F (α * S ω)
  have hGmeas : Measurable G := hFmeas.comp (measurable_const.mul hSmeas)
  have hshift := nativeHeat_cutoff_lintegral_translate_scale_shift M
    (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) (m + 10) G hGmeas
  have hmapMoment :
      ∫⁻ ω, F (α * S ω) ∂μ = ∫⁻ y, F y ∂gaussianReal 0 vscaled := by
    rw [← hscaled]
    exact (MeasureTheory.lintegral_map hFmeas (measurable_const.mul hSmeas)).symm
  have hkpow : ENNReal.ofReal (2 * (k : ℝ)) = (2 * k : ℕ) := by
    rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring]
    simp
  have hmem : MemLp (id : ℝ → ℝ) (2 * k : ℕ) (gaussianReal 0 vscaled) := by
    rw [← hkpow]; exact memLp_id_gaussianReal' _ ENNReal.ofReal_ne_top
  have hpowNonneg (y : ℝ) : 0 ≤ y ^ (2 * k) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg y) k
  have hInt : Integrable (fun y : ℝ => y ^ (2 * k)) (gaussianReal 0 vscaled) := by
    have h := hmem.integrable_norm_pow (p := 2 * k) (by omega : 2 * k ≠ 0)
    convert h using 1
    ext y
    rw [Real.norm_eq_abs]
    calc
      y ^ (2 * k) = |y ^ (2 * k)| := (abs_of_nonneg (hpowNonneg y)).symm
      _ = |y| ^ (2 * k) := abs_pow y (2 * k)
  have hpointF (y : ℝ) : F y = ENNReal.ofReal (y ^ (2 * k)) := by
    dsimp [F]
    rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
      ENNReal.rpow_natCast]
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg y)]
    congr 1
    calc
      |y| ^ (2 * k) = |y ^ (2 * k)| := (abs_pow y (2 * k)).symm
      _ = y ^ (2 * k) := abs_of_nonneg (hpowNonneg y)
  have htoENN :
      ∫⁻ y, F y ∂gaussianReal 0 vscaled =
        ENNReal.ofReal (∫ y, y ^ (2 * k) ∂gaussianReal 0 vscaled) := by
    calc
      _ = ∫⁻ y, ENNReal.ofReal (y ^ (2 * k)) ∂gaussianReal 0 vscaled := by
        apply lintegral_congr
        intro y
        exact hpointF y
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall fun y => hpowNonneg y)).symm
  have hgm0 := nativeHeat_gm_nonneg k hk1 hk20
  have hmoment := nativeHeat_gaussianEvenMoment_le_gm vscaled k hk1 hk20
  have hvar0 : 0 ≤ (nativeHeat009Variance : ℝ) :=
    (NNReal.coe_nonneg vscaled).trans hvscaled
  have hrealCap : 0 ≤
      ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
        (nativeHeat009Variance : ℝ) := mul_nonneg hgm0 hvar0
  have hvarianceMoment := mul_le_mul_of_nonneg_left hvscaled hgm0
  have hpowerMoment :
      (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) * (vscaled : ℝ)) ^ k ≤
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (nativeHeat009Variance : ℝ)) ^ k :=
    pow_le_pow_left₀ (mul_nonneg hgm0 (NNReal.coe_nonneg vscaled)) hvarianceMoment k
  calc
    _ = ∫⁻ ω, F (Z ω) ∂μ := rfl
    _ = ∫⁻ ω, G (T ω) ∂μ := by
      apply lintegral_congr
      intro ω
      simp only [G, hZ ω]
    _ = ∫⁻ ω, G ω ∂μ := hshift
    _ = ∫⁻ y, F y ∂gaussianReal 0 vscaled := hmapMoment
    _ ≤ ENNReal.ofReal
        ((((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (nativeHeat009Variance : ℝ)) ^ k) := by
      rw [htoENN]
      exact ENNReal.ofReal_le_ofReal (hmoment.trans hpowerMoment)
    _ = ENNReal.ofReal
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (nativeHeat009Variance : ℝ)) ^ (k : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hrealCap (by positivity)]
      rw [Real.rpow_natCast]

theorem nativeHeatQ3RefinedFreshRaw_measurable (m : ℤ) :
    Measurable (nativeHeatQ3RefinedCarrierSourceFreshRaw m) := by
  unfold nativeHeatQ3RefinedCarrierSourceFreshRaw
  exact (nativeHeatQ3RefinedCarrierSourceCenterMap m).continuous.measurable.comp
    (measurable_modelBand (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShells m))

theorem nativeHeatQ3RefinedFreshRaw_shellLocal (m : ℤ) :
    @Measurable (Cutoff.CutoffSample 2) (nativeHeatQ3RefinedCarrierIndex → ℝ)
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + 10))).comap Subtype.val)
      inferInstance (nativeHeatQ3RefinedCarrierSourceFreshRaw m) := by
  classical
  let J : Set ℤ := Set.Icc (m + 2) (m + 10)
  let K := nativeHeatQ3RefinedCarrierDomain m
  letI : MeasurableSpace (Cutoff.CutoffSample 2) :=
    (Cutoff.shellIndexSigma J).comap Subtype.val
  have hlabel (d : Fin 9) : nativeHeatQ3RefinedCarrierPhysicalShells m d ∈ J :=
    nativeHeatQ3RefinedCarrierPhysicalShells_mem m d
  have hcoord (d : Fin 9) : @Measurable (Cutoff.CutoffSample 2) (ShellField 2)
      ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance
      (fun ω => ω.1 (nativeHeatQ3RefinedCarrierPhysicalShells m d)) := by
    apply measurable_iff_comap_le.mpr
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fun ξ : Cutoff.ShellSeq 2 => ξ (nativeHeatQ3RefinedCarrierPhysicalShells m d))
      (Cutoff.measurable_shellCoordinate_shellIndexSigma (hlabel d))
      (by funext ω; rfl)
  have hband : @Measurable (Cutoff.CutoffSample 2) (C(K, ℝ))
      ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance
      (fun ω => modelBand K (nativeHeatQ3RefinedCarrierPhysicalShells m) ω) := by
    unfold Gaussian.modelBand
    apply Finset.measurable_sum
    intro d hd
    exact (measurable_shellFieldScalarRestriction K).comp (hcoord d)
  unfold nativeHeatQ3RefinedCarrierSourceFreshRaw
  exact (nativeHeatQ3RefinedCarrierSourceCenterMap m).continuous.measurable.comp hband

/-- The depth-four-root rare quadratic of the refined source start. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  2 * ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      nativeHeatOldInverseRemainderDepth4 M
        (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
          (nativeHeatQ3RefinedCarrierSourceZ M m ω i) ^ 2)

theorem nativeHeatQ3RefinedZ_measurable (M : ABKModel 2) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    Measurable (fun ω => nativeHeatQ3RefinedCarrierSourceZ M m ω i) := by
  unfold nativeHeatQ3RefinedCarrierSourceZ
  exact (((measurable_pi_apply i).comp
    (nativeHeatQ3RefinedFreshRaw_measurable m)).const_mul _).div_const _

theorem nativeHeatQ3RefinedZ_shellLocal (M : ABKModel 2) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + 10))).comap Subtype.val)
      inferInstance (fun ω => nativeHeatQ3RefinedCarrierSourceZ M m ω i) := by
  letI : MeasurableSpace (Cutoff.CutoffSample 2) :=
    (Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + 10))).comap Subtype.val
  unfold nativeHeatQ3RefinedCarrierSourceZ
  exact (((measurable_pi_apply i).comp
    (nativeHeatQ3RefinedFreshRaw_shellLocal m)).const_mul _).div_const _

/-- One child: the depth-four OLD remainder times the squared normalized fresh centre. -/
theorem nativeHeatQ3RefinedRareCell_moment_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (i : nativeHeatQ3RefinedCarrierIndex) (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatOldInverseRemainderDepth4 M
        (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
          (nativeHeatQ3RefinedCarrierSourceZ M m ω i) ^ 2‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((inverseBankReserve .localInverse : ℝ) *
          (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            (nativeHeat009Variance : ℝ))) ^ (k : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let R : Cutoff.CutoffSample 2 → ℝ := nativeHeatOldInverseRemainderDepth4 M Q (m + 1)
  let Z : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    nativeHeatQ3RefinedCarrierSourceZ M m ω i
  have hchild : Q.scale + 1 = m + 1 := by
    have := nativeHeatQ3RefinedCarrierChild_scale m i
    simp only [Q]; omega
  have hprofile := nativeHeatRefined_oldInverseTraceProfileDepth4_of_states
    M h hM hgamma Q (m + 1) hchild hpast
  have hRmeas : Measurable R := by simpa [R] using hprofile.1
  have hRlocal : @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M (m + 1) Set.univ) (borel ℝ) R := by
    simpa [R] using (nativeHeatRefined_oldInverseRemainderDepth4_local M Q (m + 1)).mono
      (cutoffSampleLocalSigma_mono M le_rfl
        (Set.subset_univ (cubeSet Q))) le_rfl
  have hZmeas : Measurable Z := nativeHeatQ3RefinedZ_measurable M m i
  have hZlocal : @Measurable (Cutoff.CutoffSample 2) ℝ
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + 10))).comap Subtype.val)
      inferInstance Z := nativeHeatQ3RefinedZ_shellLocal M m i
  have hJ : Disjoint (Set.Iic (m + 1)) (Set.Icc (m + 2) (m + 10)) := by
    apply Set.disjoint_left.mpr
    intro z hz hzJ
    rcases hzJ with ⟨hzLo, hzHi⟩
    change z ≤ m + 1 at hz
    omega
  have hIndep : IndepFun R Z μ := by
    simpa [μ] using nativeHeat_cutoffLocal_freshBlock_independent M (m + 1)
      (Set.Icc (m + 2) (m + 10)) hJ R hRlocal Z hZlocal
  have hR0 : ∀ ω, 0 ≤ R ω := by simpa [R] using hprofile.2.1
  let RP : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω => ENNReal.ofReal (R ω ^ k)
  let ZP : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω => ENNReal.ofReal (Z ω ^ (2 * k))
  have hRPmeas : Measurable RP := ENNReal.measurable_ofReal.comp (hRmeas.pow_const k)
  have hZPmeas : Measurable ZP :=
    ENNReal.measurable_ofReal.comp (hZmeas.pow_const (2 * k))
  have hIndPow : IndepFun RP ZP μ := by
    change (fun ω => ENNReal.ofReal (R ω ^ k)) ⟂ᵢ[μ]
      (fun ω => ENNReal.ofReal (Z ω ^ (2 * k)))
    exact hIndep.comp
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const k))
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const (2 * k)))
  have hRmoment :
      ∫⁻ ω, ‖R ω‖ₑ ^ (k : ℝ) ∂μ ≤
        ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) ^ (k : ℝ) := by
    have h128 := nativeHeat_lintegral_enorm_natPow_le_eLpNorm128
      (μ := μ) (f := R) hRmeas.aestronglyMeasurable k hk1
      (le_trans hk20 (by norm_num))
    have hcap : eLpNorm R 128 μ ≤
        ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) := by
      simpa [R, μ] using hprofile.2.2.2
    have hpow := ENNReal.rpow_le_rpow hcap (by positivity : 0 ≤ (k : ℝ))
    have hpowNat : eLpNorm R 128 μ ^ k ≤
        ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) ^ k := by
      simpa [ENNReal.rpow_natCast] using hpow
    simpa [ENNReal.rpow_natCast] using h128.trans hpowNat
  have hZmoment :
      ∫⁻ ω, ‖Z ω‖ₑ ^ (2 * (k : ℝ)) ∂μ ≤
        ENNReal.ofReal
          ((((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            (nativeHeat009Variance : ℝ))) ^ (k : ℝ) := by
    obtain ⟨ij, hij⟩ := finProdFinEquiv.surjective i
    have := nativeHeatQ3RefinedZ_moment_le_gm M h hM hgamma m hstate ij k hk1 hk20
    rw [hij] at this
    simpa [Z, μ] using this
  have hRPpoint (ω : Cutoff.CutoffSample 2) : RP ω = ‖R ω‖ₑ ^ (k : ℝ) := by
    dsimp [RP]
    rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal (hR0 ω), ENNReal.ofReal_pow (hR0 ω)]
  have hZPpoint (ω : Cutoff.CutoffSample 2) : ZP ω = ‖Z ω‖ₑ ^ (2 * (k : ℝ)) := by
    dsimp [ZP]
    have hpowNonneg : 0 ≤ Z ω ^ (2 * k) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg (Z ω)) k
    calc
      ENNReal.ofReal (Z ω ^ (2 * k)) = ‖Z ω ^ (2 * k)‖ₑ := by
        symm
        exact Real.enorm_eq_ofReal hpowNonneg
      _ = ‖Z ω‖ₑ ^ (2 * k) := by rw [enorm_pow]
      _ = ‖Z ω‖ₑ ^ (2 * (k : ℝ)) := by
        rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
          ENNReal.rpow_natCast]
  have hRPint : ∫⁻ ω, RP ω ∂μ ≤
      ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) ^ (k : ℝ) := by
    rw [lintegral_congr hRPpoint]
    exact hRmoment
  have hZPint : ∫⁻ ω, ZP ω ∂μ ≤
      ENNReal.ofReal
        ((((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (nativeHeat009Variance : ℝ))) ^ (k : ℝ) := by
    rw [lintegral_congr hZPpoint]
    exact hZmoment
  have hProductPoint (ω : Cutoff.CutoffSample 2) :
      ‖R ω * Z ω ^ 2‖ₑ ^ (k : ℝ) = RP ω * ZP ω := by
    have hnonneg : 0 ≤ R ω * Z ω ^ 2 := mul_nonneg (hR0 ω) (sq_nonneg _)
    dsimp [RP, ZP]
    rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal hnonneg,
      ← ENNReal.ofReal_pow hnonneg, mul_pow, pow_mul,
      ENNReal.ofReal_mul (pow_nonneg (hR0 ω) k)]
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (f := RP) (g := ZP) hRPmeas hZPmeas hIndPow
  have hε0 : 0 ≤ (inverseBankReserve .localInverse : ℝ) := by
    norm_num [inverseBankReserve]
  have hgm0 := nativeHeat_gm_nonneg k hk1 hk20
  have hvariance0 : 0 ≤ (nativeHeat009Variance : ℝ) := by
    norm_num [nativeHeat009Variance]
  have hgauss0 : 0 ≤ (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
      (nativeHeat009Variance : ℝ)) := mul_nonneg hgm0 hvariance0
  calc
    _ = ∫⁻ ω, RP ω * ZP ω ∂μ := by
      apply lintegral_congr
      intro ω
      exact hProductPoint ω
    _ = (∫⁻ ω, RP ω ∂μ) * ∫⁻ ω, ZP ω ∂μ := hfactor
    _ ≤ ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) ^ (k : ℝ) *
        ENNReal.ofReal
          ((((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            (nativeHeat009Variance : ℝ))) ^ (k : ℝ) :=
          mul_le_mul hRPint hZPint (by positivity) (by positivity)
    _ = ENNReal.ofReal ((inverseBankReserve .localInverse : ℝ) *
          (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            (nativeHeat009Variance : ℝ))) ^ (k : ℝ) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (k : ℝ)),
        ← ENNReal.ofReal_mul hε0]

/-- The restated rare bound: depth-four local roots at cutoff `m+1`. -/
theorem nativeHeatQ3RefinedCarrierSourceRareQuadraticMoment_le_009_depth4
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4 M m ω‖ₑ ^
        (k : ℝ) ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          (nativeHeat009Variance : ℝ))) ^ (k : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let cap : ℝ := (inverseBankReserve .localInverse : ℝ) *
    (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
      (nativeHeat009Variance : ℝ))
  let U : nativeHeatQ3RefinedCarrierIndex → Cutoff.CutoffSample 2 → ℝ := fun i ω =>
    nativeHeatOldInverseRemainderDepth4 M
      (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
        (nativeHeatQ3RefinedCarrierSourceZ M m ω i) ^ 2
  let S : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑ i, U i ω
  let N : ℝ := (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)
  have hmeanPoint : (fun ω => N⁻¹ * S ω) = N⁻¹ • S := by
    funext ω
    simp [smul_eq_mul]
  have hcap0 : 0 ≤ cap := by
    dsimp [cap]
    exact mul_nonneg (by norm_num [inverseBankReserve])
      (mul_nonneg (nativeHeat_gm_nonneg k hk1 hk20)
        (by norm_num [nativeHeat009Variance]))
  have hcellMeas (i : nativeHeatQ3RefinedCarrierIndex) : Measurable (U i) := by
    have hchild : (nativeHeatQ3RefinedCarrierChild m i).scale + 1 = m + 1 := by
      have := nativeHeatQ3RefinedCarrierChild_scale m i
      omega
    have hprofile := nativeHeatRefined_oldInverseTraceProfileDepth4_of_states
      M h hM hgamma (nativeHeatQ3RefinedCarrierChild m i) (m + 1) hchild hpast
    exact hprofile.1.mul ((nativeHeatQ3RefinedZ_measurable M m i).pow_const 2)
  have hcellMoment (i : nativeHeatQ3RefinedCarrierIndex) :
      ∫⁻ ω, ‖U i ω‖ₑ ^ (k : ℝ) ∂μ ≤ ENNReal.ofReal cap ^ (k : ℝ) :=
    nativeHeatQ3RefinedRareCell_moment_le M h hM m hgamma hstate hpast i k hk1 hk20
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1R : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
  have hcellLp (i : nativeHeatQ3RefinedCarrierIndex) :
      eLpNorm' (U i) (k : ℝ) μ ≤ ENNReal.ofReal cap := by
    have hpow : eLpNorm' (U i) (k : ℝ) μ ^ (k : ℝ) ≤
        ENNReal.ofReal cap ^ (k : ℝ) := by
      rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos]
      exact hcellMoment i
    exact (ENNReal.rpow_le_rpow_iff hkpos).mp hpow
  haveI : Nonempty nativeHeatQ3RefinedCarrierIndex :=
    ⟨⟨0, by norm_num⟩⟩
  have hmeanLp := nativeHeat_eLpNorm'_average_le (μ := μ) hk1R hcap0
    U hcellMeas hcellLp
  have hrareFun : nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4 M m =
      fun ω => 2 * (N⁻¹ * S ω) := by
    funext ω
    rfl
  have hrareLp :
      eLpNorm' (nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4 M m) (k : ℝ) μ ≤
        ENNReal.ofReal (2 * cap) := by
    have htwoPoint : (fun ω => 2 * (N⁻¹ * S ω)) =
        (2 : ℝ) • (N⁻¹ • S) := by
      funext ω
      simp [smul_eq_mul]
    have hscaleLp : eLpNorm' (fun ω => 2 * (N⁻¹ * S ω)) (k : ℝ) μ =
        ENNReal.ofReal 2 * eLpNorm' (fun ω => N⁻¹ * S ω) (k : ℝ) μ := by
      calc
        _ = eLpNorm' ((2 : ℝ) • (N⁻¹ • S)) (k : ℝ) μ := by rw [htwoPoint]
        _ = ENNReal.ofReal 2 * eLpNorm' (N⁻¹ • S) (k : ℝ) μ := by
          simpa only [Real.enorm_eq_ofReal (by norm_num : 0 ≤ (2 : ℝ))] using
            (eLpNorm'_const_smul (2 : ℝ) hkpos (f := N⁻¹ • S) (μ := μ))
        _ = _ := by rw [← hmeanPoint]
    rw [hrareFun]
    calc
      _ = ENNReal.ofReal 2 * eLpNorm' (fun ω => N⁻¹ * S ω) (k : ℝ) μ := hscaleLp
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal cap :=
        mul_le_mul_of_nonneg_left hmeanLp (by positivity)
      _ = ENNReal.ofReal (2 * cap) := by
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
  calc
    _ = eLpNorm' (nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4 M m) (k : ℝ) μ ^
        (k : ℝ) := lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos
    _ ≤ ENNReal.ofReal (2 * cap) ^ (k : ℝ) :=
      ENNReal.rpow_le_rpow hrareLp (by positivity)
    _ = _ := by
      simp only [cap]
      congr 2
      ring

end ASDExplicitGamma.Native
