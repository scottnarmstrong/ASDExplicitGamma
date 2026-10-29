module

public import ASDExplicitGamma.Inverse.RawTraceTransport
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Inverse.RawShellBandBankInputs
public import ASDExplicitGamma.Model.CutoffAction
public import ASDExplicitGamma.Model.Translation
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm

/-! The origin profile controls the actual common descendant-cell
average by translation invariance and finite Minkowski. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 MeasureTheory
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Cold ASDExplicitGamma.Model
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

noncomputable section

private theorem raw_trace_shell_scalar_eq_helper
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (_ell : ℤ)
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 _ell))
    (x : closure (cubeSet (originCube 2 n))) :
    rawShellBandScalarFromWeights M n s weights ω x =
      attenuatedCoefficient M n (n + (s : ℤ)) weights ω x 1 0 := by
  classical
  have hold := olderField_apply_eq_coefficientCutoff
    (closure (cubeSet (originCube 2 n))) M _ell n hK ω x
  have hsum :
      (∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
        weights k • shellFieldScalarRestriction
          (closure (cubeSet (originCube 2 n))) (ω.val k)) x =
      (∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
        weights k • ShellField.forgetShell (ω.val k) x.1) 1 0 := by
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
      Matrix.sum_apply, Matrix.smul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    simp [shellFieldScalarRestriction, planarShellScalarStream,
      planarShellMatrixEntry, ShellField.forgetShell_apply]
  rw [rawShellBandScalarFromWeights, ContinuousMap.add_apply, hold, hsum]
  simp only [attenuatedCoefficient, Matrix.add_apply,
    Cutoff.coefficientCutoff_apply]

/-- The padded consumer weights are exactly the ordinary partial insertion
on their support, so the origin band trace is the actual inserted-law trace. -/
theorem raw_trace_transport_band_scalar_eq_inserted_helper
    (M : ABKModel 2) (m : ℤ) (r j : ℕ) (hr : r ≤ 5)
    (t : ℝ) (_ht : t ∈ Set.Icc (0 : ℝ) 1) (ω : Cutoff.CutoffSample 2) :
    rawShellBandScalarFromWeights M (m - (r : ℤ) - (j : ℤ)) (134 + j)
      (rawTraceTransportWeights m t) ω =
    modelInsertedScalar (closure (cubeSet
      (originCube 2 (m - (r : ℤ) - (j : ℤ))))) m t ω := by
  classical
  let n : ℤ := m - (r : ℤ) - (j : ℤ)
  let s : ℕ := r + j + 1
  let K := closure (cubeSet (originCube 2 n))
  let weights := bankPartialInsertionWeights n s t
  have hendpoint : n + (s : ℤ) = m + 1 := by
    dsimp [n, s]
    omega
  have hpad : s ≤ 134 + j := by
    dsimp [s]
    omega
  have hweights : rawTraceTransportWeights m t = weights := by
    funext k
    dsimp [rawTraceTransportWeights, weights, bankPartialInsertionWeights]
    rw [hendpoint]
    by_cases hk : k ≤ m
    · simp [hk, show k < m + 1 by omega]
    · have hk' : ¬ k < m + 1 := by omega
      simp [hk, hk']
  have hpadZ : (s : ℤ) ≤ ((134 + j : ℕ) : ℤ) := by
    exact_mod_cast hpad
  have hsubset : Finset.Ioc n (n + (s : ℤ)) ⊆
      Finset.Ioc n (n + ((134 + j : ℕ) : ℤ)) :=
    Finset.Ioc_subset_Ioc_right (add_le_add_right hpadZ n)
  have hsum :
      (∑ k ∈ Finset.Ioc n (n + ((134 + j : ℕ) : ℤ)),
        rawTraceTransportWeights m t k •
          shellFieldScalarRestriction K (ω.val k)) =
      (∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
        weights k • shellFieldScalarRestriction K (ω.val k)) := by
    symm
    rw [hweights]
    apply Finset.sum_subset hsubset
    intro k hkBig hkSmall
    have hk : n + (s : ℤ) < k := by
      simp only [Finset.mem_Ioc] at hkBig hkSmall
      omega
    have hkm : ¬ k ≤ m := by omega
    have hkeq : k ≠ m + 1 := by omega
    simp [weights, bankPartialInsertionWeights, hendpoint, hkm, hkeq]
  obtain ⟨ell, hK⟩ :=
    Gaussian.exists_originCube_containing_compact K
      (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hcoeff (x : Vec 2) :
      attenuatedCoefficient M n (n + (s : ℤ)) weights ω x =
        (Model.partialInsertedCoefficient M m t ω).toFun x := by
    rw [raw_shell_partial_coefficient_any M n s (by dsimp [s]; omega) t ω x]
    rw [show n + (s : ℤ) - 1 = m by omega, hendpoint]
    rfl
  have hsmall (x : K) :
      rawShellBandScalarFromWeights M n s weights ω x =
        modelInsertedScalar K m t ω x := by
    rw [raw_trace_shell_scalar_eq_helper M n s weights ω ell hK x]
    rw [hcoeff x.1]
    exact (modelInsertedScalar_apply K M ell m hK t ω x).symm
  apply ContinuousMap.ext
  intro x
  change olderField K n ω x +
      (∑ k ∈ Finset.Ioc n (n + ((134 + j : ℕ) : ℤ)),
        rawTraceTransportWeights m t k • shellFieldScalarRestriction K (ω.val k)) x =
    modelInsertedScalar K m t ω x
  rw [hsum]
  exact hsmall x

/-- Translating a source cell is the same as translating its cutoff sample;
the partially inserted coefficient retains the fixed true frame. -/
theorem raw_cube_four_load_trace_eq_translated_origin_helper
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    rawCubeFourLoadTrace M m Q t ω =
      rawDepthFourLoadTrace M m Q.scale t
        (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) := by
  let z := triadicCubeShift Q
  have hcoeff :
      (Model.partialInsertedCoefficient M m t
        (Cutoff.translateCutoffSample z ω)).toFun =
        translateCoeffField z (Model.partialInsertedCoefficient M m t ω).toFun := by
    ext x i k
    simp [Model.partialInsertedCoefficient, Cutoff.coefficientCutoff_translateCutoffSample,
      Cutoff.translateCutoffSample_val, ShellField.forgetShell_translate,
      translateCoeffField, translateReg]
    rw [← (show (fun a : Fin 2 => x a + z a) = x + z by ext a; rfl)]
  simp only [rawCubeFourLoadTrace, rawDepthFourLoadTrace]
  rw [cubeSet_eq_translateSet_originCube_of_triadicCube Q]
  rw [Model.traceDefect_translate, ← hcoeff]

private theorem raw_depth_four_load_trace_aestronglyMeasurable_helper
    (M : ABKModel 2) (m q : ℤ) (t : ℝ) :
    AEStronglyMeasurable (rawDepthFourLoadTrace M m q t)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let K := closure (cubeSet (originCube 2 q))
  haveI : CompactSpace K := modelHeatCubeClosureCompact q
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  have hscalar : Measurable (modelInsertedScalar K m t) := by
    change Measurable (fun ω => olderField K m ω +
      Real.sqrt t • shellFieldScalarRestriction K (ω.1 (m + 1)))
    exact (measurable_olderField K ell m hK).add
      (((measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)).const_smul
          (Real.sqrt t))
  have hobs := (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1).1.continuous.measurable.comp hscalar
  have heq : rawDepthFourLoadTrace M m q t =
      fun ω => modelTraceObservable q M.nu (Annealed.sigmaBar M m : ℝ)
        (modelInsertedScalar K m t ω) := by
    funext ω
    exact raw_depth_four_load_trace_eq_model_observable M m q t ω
  rw [heq]
  exact hobs.aestronglyMeasurable

private theorem raw_trace_transport_cell_profile_from_origin_helper
    (M : ABKModel 2) (m : ℤ) (r j : ℕ) (hr : r ≤ 5) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hprofile : eLpNorm (rawTraceTransportBandObservable M m r t j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal
        (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
          (3 : ℝ) ^ (6 * gammaZero * j))) :
    ∀ Q ∈ descendantsAtDepth (originCube 2 (m - (r : ℤ))) j,
      eLpNorm (rawCubeFourLoadTrace M m Q t) (ENNReal.ofReal 2)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j)) := by
  let P := originCube 2 (m - (r : ℤ))
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let U := theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
    (3 : ℝ) ^ (6 * gammaZero * j)
  intro Q hQ
  have hscale : Q.scale = m - (r : ℤ) - (j : ℤ) := by
    change Q ∈ descendantsAtDepth P j at hQ
    simpa only [P, originCube] using
      scale_eq_sub_of_mem_descendantsAtDepth hQ
  have hmodel : ∀ ω : Cutoff.CutoffSample 2,
      rawTraceTransportBandObservable M m r t j ω =
        rawDepthFourLoadTrace M m (m - (r : ℤ) - (j : ℤ)) t ω := by
    intro ω
    rw [rawTraceTransportBandObservable]
    rw [raw_depth_four_load_trace_eq_model_observable]
    rw [raw_trace_transport_band_scalar_eq_inserted_helper M m r j hr t
      ⟨ht.1, ht.2⟩ ω]
  have hmodelFun : rawTraceTransportBandObservable M m r t j =
      rawDepthFourLoadTrace M m (m - (r : ℤ) - (j : ℤ)) t := by
    funext ω
    exact hmodel ω
  have htrans : rawCubeFourLoadTrace M m Q t = fun ω =>
      rawDepthFourLoadTrace M m (m - (r : ℤ) - (j : ℤ)) t
        (triadicCubeShift Q +ᵥ ω) := by
    funext ω
    calc
      rawCubeFourLoadTrace M m Q t ω =
          rawDepthFourLoadTrace M m Q.scale t
            (Cutoff.translateCutoffSample (triadicCubeShift Q) ω) :=
        raw_cube_four_load_trace_eq_translated_origin_helper M m Q t ω
      _ = rawDepthFourLoadTrace M m (m - (r : ℤ) - (j : ℤ)) t
            (triadicCubeShift Q +ᵥ ω) := by
        rw [hscale]
        congr 2
  rw [htrans]
  have hmeas := raw_depth_four_load_trace_aestronglyMeasurable_helper M m
    (m - (r : ℤ) - (j : ℤ)) t
  change eLpNorm
    (rawDepthFourLoadTrace M m (m - (r : ℤ) - (j : ℤ)) t ∘
      (fun ω => triadicCubeShift Q +ᵥ ω)) (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal U
  rw [eLpNorm_comp_measurePreserving hmeas
    (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd
      (μ := μ) (triadicCubeShift Q))]
  rw [← hmodelFun]
  exact hprofile

private theorem eLpNorm_constant_average_le_helper
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hcard : 0 < Fintype.card ι)
    (hbound : ∀ i, eLpNorm (f i) (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal U) :
    eLpNorm
      (fun ω => ((Fintype.card ι : ℝ)⁻¹) * ∑ i, f i ω)
      (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal U := by
  let w : ι → ℝ := fun _ => (Fintype.card ι : ℝ)⁻¹
  have hcardR : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcard
  have hweightSum : (∑ i, w i * U) = U := by
    calc
      (∑ i, w i * U) = (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ)⁻¹ * U) := by
        simp [w, Finset.sum_const, nsmul_eq_mul]
      _ = U := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcardR)]
        simp
  have hsum := finite_density_sum_Lp μ (ENNReal.ofReal 2)
    (ENNReal.one_le_ofReal.mpr (by norm_num : (1 : ℝ) ≤ 2))
    f w (fun _ => U) (fun _ => inv_nonneg.mpr hcardR.le) (fun _ => hU) hbound
  have hmean :
      (fun ω => ((Fintype.card ι : ℝ)⁻¹) * ∑ i, f i ω) =
        fun ω => ∑ i, w i * f i ω := by
    funext ω
    simp [w, Finset.mul_sum]
  rw [hmean]
  simpa [hweightSum] using hsum

private theorem raw_weak_trace_sequence_average_bound_helper
    (M : ABKModel 2) (m : ℤ) (r j : ℕ) (t U : ℝ) (hU : 0 ≤ U)
    (hcell : ∀ Q ∈ descendantsAtDepth (originCube 2 (m - (r : ℤ))) j,
      eLpNorm (rawCubeFourLoadTrace M m Q t) (ENNReal.ofReal 2)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal U) :
    eLpNorm
      (fun ω => rawWeakTraceSequence M m (originCube 2 (m - (r : ℤ))) t ω j)
      (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal U := by
  let P := originCube 2 (m - (r : ℤ))
  let D := descendantsAtDepth P j
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hcardNat : 0 < D.card := Finset.card_pos.mpr (descendantsAtDepth_nonempty P j)
  have hcard : 0 < (D.card : ℝ) := by exact_mod_cast hcardNat
  let I := SquareCells P j
  have hmean_eq :
      (fun ω => rawWeakTraceSequence M m P t ω j) =
        fun ω => ((D.card : ℝ)⁻¹) *
          ∑ C : I, rawCubeFourLoadTrace M m C.val t ω := by
    funext ω
    rfl
  have hmeanfun :
      (fun ω => rawWeakTraceSequence M m P t ω j) =
        fun ω => ∑ C : I, (D.card : ℝ)⁻¹ * rawCubeFourLoadTrace M m C.val t ω := by
    funext ω
    simpa [Finset.mul_sum] using congrFun hmean_eq ω
  have hcardI : Fintype.card I = D.card := by simp [I, SquareCells, D]
  have hcardIr : (Fintype.card I : ℝ) = (D.card : ℝ) := by exact_mod_cast hcardI
  have hcardIpos : 0 < Fintype.card I := by rw [hcardI]; exact hcardNat
  have hmeanfun' :
      (fun ω => rawWeakTraceSequence M m P t ω j) =
        fun ω => ((Fintype.card I : ℝ)⁻¹) *
          ∑ C : I, rawCubeFourLoadTrace M m C.val t ω := by
    calc
      (fun ω => rawWeakTraceSequence M m P t ω j) =
          fun ω => ∑ C : I, (D.card : ℝ)⁻¹ * rawCubeFourLoadTrace M m C.val t ω :=
        hmeanfun
      _ = fun ω => (D.card : ℝ)⁻¹ *
          ∑ C : I, rawCubeFourLoadTrace M m C.val t ω := by
        funext ω
        rw [← Finset.mul_sum]
      _ = fun ω => ((Fintype.card I : ℝ)⁻¹) *
          ∑ C : I, rawCubeFourLoadTrace M m C.val t ω := by
        funext ω
        rw [← hcardIr]
  rw [hmeanfun']
  exact eLpNorm_constant_average_le_helper
    (Ω := Cutoff.CutoffSample 2) (ι := I) μ
    (fun C : I => rawCubeFourLoadTrace M m C.val t) U hU hcardIpos
    (fun C => hcell C.val C.property)

private theorem raw_weak_trace_sequence_profile_from_origin_profile_helper
    (M : ABKModel 2) (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hprofile : ∀ j : ℕ,
      eLpNorm (rawTraceTransportBandObservable M m r t j)
          (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j))) :
    ∀ j : ℕ,
      eLpNorm
        (fun ω => rawWeakTraceSequence M m (originCube 2 (m - (r : ℤ))) t ω j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal
        (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
          (3 : ℝ) ^ (6 * gammaZero * j)) := by
  intro j
  let U := theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
    (3 : ℝ) ^ (6 * gammaZero * j)
  have hU : 0 ≤ U := by
    have htheta : 0 ≤ theta M := by
      unfold theta
      exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
    have hMrat : 0 ≤ invTraceM := by
      rw [invTrace_coefficient.1]
      positivity
    have hM : 0 ≤ (invTraceM : ℝ) := by exact_mod_cast hMrat
    have hpoly : 0 ≤ (1 + (j : ℝ)) ^ 2 := sq_nonneg _
    have hgeom : 0 ≤ (3 : ℝ) ^ (6 * gammaZero * j) := by positivity
    change 0 ≤ theta M * (invTraceM : ℚ) *
      (1 + (j : ℝ)) ^ 2 * (3 : ℝ) ^ (6 * gammaZero * j)
    exact mul_nonneg (mul_nonneg (mul_nonneg htheta hM) hpoly) hgeom
  have hcell := raw_trace_transport_cell_profile_from_origin_helper
    M m r j hr t ht (hprofile j)
  exact raw_weak_trace_sequence_average_bound_helper M m r j t U hU hcell

/-- The p=2 source envelope holds for the actual descendant average,
uniformly in the deterministic attenuation time. -/
theorem raw_weak_trace_sequence_profile_of_shell_transport_helper
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (m : ℤ) (r : ℕ) (hr : r ≤ 5) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ j : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (j : ℤ)))
    (hShell : ∀ j : ℕ,
      eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (rawShellBandScalarFromWeights M
              (m - (r : ℤ) - (j : ℤ)) (134 + j)
              (rawTraceTransportWeights m t) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        eLpNorm
          (fun ω => modelTraceObservable (m - (r : ℤ) - (j : ℤ)) M.nu
            (Annealed.sigmaBar M (m - (r : ℤ) - (j : ℤ)) : ℝ)
            (olderField (closure (cubeSet
              (originCube 2 (m - (r : ℤ) - (j : ℤ)))))
              (m - (r : ℤ) - (j : ℤ)) ω))
          (ENNReal.ofReal 20) (Cutoff.cutoffSampleLaw M).toMeasure +
        ENNReal.ofReal (rawTraceBandShellIncrement M.gamma (134 + j))) :
    ∀ j : ℕ,
      eLpNorm
        (fun ω => rawWeakTraceSequence M m (originCube 2 (m - (r : ℤ))) t ω j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal
        (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
          (3 : ℝ) ^ (6 * gammaZero * j)) := by
  have hprofile := raw_trace_transport_origin_depth_family_helper
    M h hγ m r hr t ⟨ht.1, ht.2⟩ hstate hShell
  exact raw_weak_trace_sequence_profile_from_origin_profile_helper
    M m r hr t ht hprofile

/-- IN-RAW-TRACE-TRANSPORT. The exact shell theorem is
instantiated from the native-state family, after which the actual translated
descendant average and both rare reserves follow without a shell
premise. -/
theorem raw_trace_transport_profile_and_reserves_source
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (r : ℕ) (hr : r ≤ 5)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hstate : ∀ q : ℕ,
      nativeInductionState M h (m - (r : ℤ) - (q : ℤ))) :
    (∀ j : ℕ,
      eLpNorm
        (fun ω => rawWeakTraceSequence M m
          (originCube 2 (m - (r : ℤ))) t ω j)
        (ENNReal.ofReal 2) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (theta M * (invTraceM : ℚ) * (1 + (j : ℝ)) ^ 2 *
            (3 : ℝ) ^ (6 * gammaZero * j))) ∧
    (5400 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) * theta M ≤
        (1 / 10^12 : ℝ) * theta M ∧
    (27000 : ℝ) * (1 / 10^24 : ℝ) * (invTraceM : ℚ) * theta M ≤
        (1 / 10^12 : ℝ) * theta M := by
  have hprofile := raw_weak_trace_sequence_profile_of_shell_transport_helper
    M h hγ m r hr t ht hstate
    (raw_trace_transport_shell_family_source
      M h hM hγ m r t ht hstate)
  have htheta0 : 0 ≤ theta M := by
    unfold theta
    exact div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hreserve := raw_trace_transport_rare_reserves_helper (theta M) htheta0
  exact ⟨hprofile, hreserve.1, hreserve.2⟩


end
end ASDExplicitGamma.Inverse
