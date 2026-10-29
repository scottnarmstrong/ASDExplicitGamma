module

public import ASDExplicitGamma.Inverse.BankOnePassLocal
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.RawShellBankInputs

/-! Local and full-response bank adapters for an arbitrary finite shell band. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable def rawShellBandLocalHistory (M : ABKModel 2) (n : ℤ)
    (s : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5) M n (n + (s : ℤ))
    (bankPartialInsertionWeights n s t) ω).toReal

noncomputable def rawShellBandSourceHistory (M : ABKModel 2) (n : ℤ)
    (s : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let σ := (Annealed.sigmaBar M n : ℝ)
  let x := modelInsertedScalar (closure (cubeSet Q)) (n + (s : ℤ) - 1) t ω
  let k := pureFluxOpenResponseRestriction n x
  max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ k))
    (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ k))

noncomputable def rawShellBandScalarFromWeights (_M : ABKModel 2) (n : ℤ)
    (s : ℕ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    C(closure (cubeSet (originCube 2 n)), ℝ) :=
  olderField (closure (cubeSet (originCube 2 n))) n ω +
    ∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
      weights k • shellFieldScalarRestriction (closure (cubeSet (originCube 2 n)))
        (ω.1 k)

noncomputable def rawShellWeightedLocalHistory (M : ABKModel 2) (n J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5) M n J weights ω).toReal

noncomputable def rawShellWeightedSourceHistory (M : ABKModel 2) (n : ℤ)
    (s : ℕ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let σ := (Annealed.sigmaBar M n : ℝ)
  let f := rawShellBandScalarFromWeights M n s weights ω
  let k := pureFluxOpenResponseRestriction n f
  max (lemmaVTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ k))
    (pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField M.nu σ k))

/-- The finite attenuation weights through the actual endpoint `n+s` give
the partial physical coefficient without a 40-shell restriction. -/
theorem raw_shell_partial_coefficient_any
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    attenuatedCoefficient M n (n + (s : ℤ))
        (bankPartialInsertionWeights n s t) ω x =
      Cutoff.coefficientCutoff M.nu (n + (s : ℤ) - 1) ω x +
        Real.sqrt t • (ω.val (n + (s : ℤ))).forgetShell x := by
  classical
  have hterm (k : ℤ) : bankPartialInsertionWeights n s t k • (ω.val k).forgetShell x =
      (if k < n + (s : ℤ) then (ω.val k).forgetShell x else 0) +
        (if k = n + (s : ℤ) then Real.sqrt t • (ω.val k).forgetShell x else 0) := by
    by_cases hlt : k < n + (s : ℤ)
    · simp [bankPartialInsertionWeights, hlt, ne_of_lt hlt]
    · by_cases heq : k = n + (s : ℤ)
      · simp [bankPartialInsertionWeights, heq]
      · simp [bankPartialInsertionWeights, hlt, heq]
  have hsets : (Finset.Ioc n (n + (s : ℤ))).filter
      (fun k => k < n + (s : ℤ)) = Finset.Ioc n (n + (s : ℤ) - 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  have hfirst : (∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
      if k < n + (s : ℤ) then (ω.val k).forgetShell x else 0) =
        ∑ k ∈ Finset.Ioc n (n + (s : ℤ) - 1), (ω.val k).forgetShell x := by
    rw [← Finset.sum_filter, hsets]
  have hmem : n + (s : ℤ) ∈ Finset.Ioc n (n + (s : ℤ)) := by
    simp only [Finset.mem_Ioc]
    omega
  have hsum : (∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
      bankPartialInsertionWeights n s t k • (ω.val k).forgetShell x) =
        (∑ k ∈ Finset.Ioc n (n + (s : ℤ) - 1), (ω.val k).forgetShell x) +
          Real.sqrt t • (ω.val (n + (s : ℤ))).forgetShell x := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, hfirst]
    simp only [Finset.sum_ite_eq', hmem, ite_true]
  have hc := congrArg (fun a : RegCoeffField 2 => a x)
    (Cutoff.cutoff_add_finiteShellIncrement ω
      (show n ≤ n + (s : ℤ) - 1 by omega))
  change Cutoff.cutoff n ω x +
      Cutoff.finiteShellIncrement ω.val n (n + (s : ℤ) - 1) x =
    Cutoff.cutoff (n + (s : ℤ) - 1) ω x at hc
  rw [Cutoff.finiteShellIncrement_apply] at hc
  change Cutoff.cutoff n ω x +
      (∑ k ∈ Finset.Ioc n (n + (s : ℤ) - 1), (ω.val k).forgetShell x) =
    Cutoff.cutoff (n + (s : ℤ) - 1) ω x at hc
  unfold attenuatedCoefficient
  rw [hsum, Cutoff.coefficientCutoff_apply, Cutoff.coefficientCutoff_apply, ← hc]
  abel

private theorem raw_shell_inverseHistory_frame_eq_aux
    (Q : TriadicCube 2) (a af : CoeffField 2)
    {lam Lam laf Laf σ q : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEllFrame : IsEllipticFieldOn laf Laf (openCubeSet Q) af)
    (hσ : 0 < σ)
    (hMatrix : ∀ (R : TriadicCube 2) (d : ℕ)
      (_hR : R ∈ descendantsAtDepth Q d),
      coarseBlockMatrix (cubeSet R) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) a)) :
    lemmaVInverseHistory Q af q = σ * lemmaVInverseHistory Q a q := by
  have hdepth (d : ℕ) : lemmaVInverseDepthMax Q af d =
      σ * lemmaVInverseDepthMax Q a d := by
    rw [lemmaVInverseDepthMax,
      ← Scalar.inverse_history_framed_depth_max Q a hEll σ hσ d]
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    rw [Scalar.inverse_history_lowerRight R af
      (hEllFrame.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)), hMatrix R d hR]
    simp [frameMatrix]
  unfold lemmaVInverseHistory
  simp_rw [hdepth]
  calc
    (1 - q⁻¹) * ∑' d : ℕ, (q⁻¹)^d *
        (σ * lemmaVInverseDepthMax Q a d) =
      (1 - q⁻¹) * (σ * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by
        congr 1
        calc
          ∑' d : ℕ, (q⁻¹)^d * (σ * lemmaVInverseDepthMax Q a d) =
              ∑' d : ℕ, σ * ((q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by
                apply tsum_congr
                intro d
                ring
          _ = σ * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d := tsum_mul_left
    _ = σ * ((1 - q⁻¹) * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by ring

private theorem raw_shell_descendant_in_local_roots
    (P U : TriadicCube 2) (m : ℕ) (hm : m ≤ 5)
    (hU : U ∈ descendantsAtDepth P m) : U ∈ bankLocalRoots P 5 := by
  rw [bankLocalRoots, Finset.mem_insert]
  right
  rw [Finset.mem_biUnion]
  exact ⟨m, Finset.mem_range.mpr (by omega), hU⟩

/-- The all-band local bank cap on the source roots of a scale-`n` cell. -/
theorem raw_shell_band_local_inverse_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    InverseBankConclusion M .localInverse (bankLocalRoots (originCube 2 n) 5)
      n (n + (s : ℤ)) (bankPartialInsertionWeights n s t) := by
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2
  have hgeometry := bank_one_pass_local_geometry n
  exact local_inverse_bank M h hM hg (bankLocalRoots (originCube 2 n) 5)
    n (n + (s : ℤ)) (by omega) (bankPartialInsertionWeights n s t)
    (fun i _ => bank_partial_insertion_weights_bounds n s t ht.2 i)
    hgeometry.1 hgeometry.2 hpast hmean

/-- The all-band local history inherits the exact order-128 cap. -/
theorem raw_shell_band_local_history_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    eLpNorm (rawShellBandLocalHistory M n s t) (128 : ℝ≥0∞)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (3683 / 2500 : ℝ) := by
  let H := bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5) M n
    (n + (s : ℤ)) (bankPartialInsertionWeights n s t)
  have hbank := raw_shell_band_local_inverse_bank M h hM hg n s hs t ht hpast
  have he := eLpNorm_congr_ae (p := 128) (ofReal_toReal_ae_eq hbank.history_finite)
  have he' : eLpNorm (rawShellBandLocalHistory M n s t) 128
      (Cutoff.cutoffSampleLaw M).toMeasure =
    eLpNorm H 128 (Cutoff.cutoffSampleLaw M).toMeasure := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (rawShellBandLocalHistory M n s t ω)) 128
          (Cutoff.cutoffSampleLaw M).toMeasure :=
        (eLpNorm_ofReal _ (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
      _ = _ := he
  exact he'.trans_le (by
    simpa only [H, inverseBankCap, Rat.cast_div, Rat.cast_ofNat] using hbank.total_L128)

/-- A source-mesh inverse history is bounded by the same finite-band local
history, with the exact partial coefficient and fixed frame identified. -/
theorem raw_shell_band_source_mesh_history_le
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (hs : 1 ≤ s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) (m : ℕ) (hm : m ≤ 5)
    (hfinite : bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5)
      M n (n + (s : ℤ)) (bankPartialInsertionWeights n s t) ω ≠ ∞)
    {U : TriadicCube 2} (hU : U ∈ descendantsAtDepth (originCube 2 n) m) :
    lemmaVInverseHistory U
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M n : ℝ)
          (pureFluxOpenResponseRestriction n
            (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
              (n + (s : ℤ) - 1) t ω)))
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
      (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5)
        M n (n + (s : ℤ)) (bankPartialInsertionWeights n s t) ω).toReal := by
  let P := originCube 2 n
  let K := closure (cubeSet P)
  let f := modelInsertedScalar K (n + (s : ℤ) - 1) t ω
  let H := pureFluxOpenResponseRestriction n f
  let σ := (Annealed.sigmaBar M n : ℝ)
  let a := attenuatedCoefficient M n (n + (s : ℤ))
    (bankPartialInsertionWeights n s t) ω
  let af := responseFramePlanarCoefficientField M.nu σ H
  let q := (3 : ℝ) ^ (1 / 4 : ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet P).isCompact_closure
  let Lam : ℝ := ((2 : ℝ) * 2 * (Model.partialInsertedEntryBound M ell
    (n + (s : ℤ) - 1) ω) ^ 2 + M.nu ^ 2) / M.nu
  have hEllPartial : IsEllipticFieldOn M.nu Lam (openCubeSet P)
      (Model.partialInsertedCoefficient M (n + (s : ℤ) - 1) t ω).toFun := by
    simpa using Model.partialInsertedCoefficient_isEllipticFieldOn M ell
      (n + (s : ℤ) - 1) ω ⟨ht.1, ht.2⟩ (measurableSet_openCubeSet P)
      (fun _ hx => hK (subset_closure (openCubeSet_subset_cubeSet P hx)))
  have hcoeff := raw_shell_partial_coefficient_any M n s hs t ω
  have hCoeff : a = (Model.partialInsertedCoefficient M
      (n + (s : ℤ) - 1) t ω).toFun := by
    funext x
    simpa [a, Model.partialInsertedCoefficient,
      show n + (s : ℤ) - 1 + 1 = n + (s : ℤ) by omega] using hcoeff x
  have hEll : IsEllipticFieldOn M.nu Lam (openCubeSet P) a := by
    simpa only [a, hCoeff] using hEllPartial
  have hEllFrame := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet P) M.nu σ M.nu_pos hσ H
  have hMatrix (V : TriadicCube 2) (j : ℕ)
      (hV : V ∈ descendantsAtDepth U j) :
      coarseBlockMatrix (cubeSet V) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet V) a) := by
    have hVP : V ∈ descendantsAtDepth P (m + j) := by
      simpa [Nat.add_comm] using mem_descendantsAtDepth_add hU hV
    simpa only [af, σ, a, hCoeff] using
      (pureFlux_partialInsertion_coarseMatrix_frame n M ell hK s t ω hVP)
  have hEllU := hEll.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hEllFrameU := hEllFrame.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hFrameHistory : lemmaVInverseHistory U af q = σ * lemmaVInverseHistory U a q :=
    raw_shell_inverseHistory_frame_eq_aux U a af hEllU hEllFrameU hσ (q := q)
      (fun V j hV => hMatrix V j hV)
  have hRootHistory := bank_root_history_physical U M n (n + (s : ℤ))
    (bankPartialInsertionWeights n s t) ω a rfl hEllU
  have hHistoryEq : lemmaVInverseHistory U af q =
      (bankRootInverseHistory U M n (n + (s : ℤ))
        (bankPartialInsertionWeights n s t) ω).toReal := by
    rw [hFrameHistory, hRootHistory, ENNReal.toReal_ofReal]
    exact mul_nonneg hσ.le (lemmaVInverseHistory_nonneg U a hq)
  have hRoot : U ∈ bankLocalRoots P 5 :=
    raw_shell_descendant_in_local_roots P U m hm hU
  have hmax := bank_member_history_le M (bankLocalRoots P 5) U hRoot n
    (n + (s : ℤ)) (bankPartialInsertionWeights n s t) ω
  have hmaxReal := ENNReal.toReal_mono hfinite hmax
  change lemmaVInverseHistory U af q ≤ _
  calc
    lemmaVInverseHistory U af q =
        (bankRootInverseHistory U M n (n + (s : ℤ))
          (bankPartialInsertionWeights n s t) ω).toReal := hHistoryEq
    _ ≤ (bankFiniteRootHistoryMax (bankLocalRoots P 5) M n (n + (s : ℤ))
          (bankPartialInsertionWeights n s t) ω).toReal := hmaxReal

/-- The local inverse bank accepts an arbitrary bounded attenuation profile
on the finite band, with no restriction on its endpoint. -/
theorem raw_shell_weighted_local_inverse_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n J : ℤ) (hnJ : n ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    InverseBankConclusion M .localInverse (bankLocalRoots (originCube 2 n) 5)
      n J weights := by
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2
  have hgeometry := bank_one_pass_local_geometry n
  exact local_inverse_bank M h hM hg (bankLocalRoots (originCube 2 n) 5)
    n J hnJ weights hw hgeometry.1 hgeometry.2 hpast hmean

/-- The exact OLD order-128 local cap for an arbitrary finite weighted band. -/
theorem raw_shell_weighted_local_history_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n J : ℤ) (hnJ : n ≤ J)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    eLpNorm (rawShellWeightedLocalHistory M n J weights) (128 : ℝ≥0∞)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (3683 / 2500 : ℝ) := by
  let H := bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5) M n J weights
  have hbank := raw_shell_weighted_local_inverse_bank M h hM hg n J hnJ weights hw hpast
  have he := eLpNorm_congr_ae (p := 128) (ofReal_toReal_ae_eq hbank.history_finite)
  have he' : eLpNorm (rawShellWeightedLocalHistory M n J weights) 128
      (Cutoff.cutoffSampleLaw M).toMeasure =
    eLpNorm H 128 (Cutoff.cutoffSampleLaw M).toMeasure := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (rawShellWeightedLocalHistory M n J weights ω))
          128 (Cutoff.cutoffSampleLaw M).toMeasure :=
        (eLpNorm_ofReal _ (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
      _ = _ := he
  exact he'.trans_le (by
    simpa only [H, inverseBankCap, Rat.cast_div, Rat.cast_ofNat] using hbank.total_L128)

theorem raw_shell_weighted_local_history_measurable
    (M : ABKModel 2) (n J : ℤ) (weights : ℤ → ℝ) :
    Measurable (rawShellWeightedLocalHistory M n J weights) := by
  unfold rawShellWeightedLocalHistory
  exact ENNReal.measurable_toReal.comp
    (history_finite_max_measurable _ _ (fun Q =>
      bank_root_inverse_history_measurable Q.1 M n J weights))

private theorem raw_shell_weighted_symmPart (M : ABKModel 2) (n J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Homogenization.symmPart (attenuatedCoefficient M n J weights ω x) =
      M.nu • (1 : Mat 2) := by
  unfold attenuatedCoefficient
  have hsum : Homogenization.symmPart
      (∑ k ∈ Finset.Ioc n J, weights k • ShellField.forgetShell (ω.val k) x) = 0 := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, ShellField.forgetShell_apply]
    rw [← Finset.sum_add_distrib]
    apply (div_eq_zero_iff).mpr
    left
    apply Finset.sum_eq_zero
    intro k hk
    rw [(ω.val k).skew_entry x i j]
    ring
  have hadd (A B : Mat 2) : Homogenization.symmPart (A + B) =
      Homogenization.symmPart A + Homogenization.symmPart B := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.add_apply]
    ring
  rw [hadd, Cutoff.symmPart_coefficientCutoff, hsum]
  simp

private theorem raw_shell_weighted_entry_bound (M : ABKModel 2) (ell : ℤ)
    (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    {x : Vec 2} (hx : x ∈ openCubeSet (originCube 2 ell)) (i j : Fin 2) :
    |attenuatedCoefficient M n J weights ω x i j| ≤
      M.nu + Cutoff.cutoffLocalControl ell n ω +
        ∑ k ∈ Finset.Ioc n J,
          |weights k| * localCubeControl ell (ω.val k) := by
  classical
  have hbase := Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le ell n ω hx i j
  have hsum : |∑ k ∈ Finset.Ioc n J,
        weights k * ω.val k x i j| ≤
      ∑ k ∈ Finset.Ioc n J,
        |weights k| * localCubeControl ell (ω.val k) := by
    calc
      |∑ k ∈ Finset.Ioc n J, weights k * ω.val k x i j| ≤
          ∑ k ∈ Finset.Ioc n J, |weights k * ω.val k x i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ioc n J,
          |weights k| * localCubeControl ell (ω.val k) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_entry_le_localCubeControl ell (ω.val k) hx i j) (abs_nonneg _)
  have hsumEntry :
      (∑ k ∈ Finset.Ioc n J,
        weights k • ShellField.forgetShell (ω.val k) x) i j =
        ∑ k ∈ Finset.Ioc n J, weights k * ω.val k x i j := by
    simp [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      ShellField.forgetShell_apply]
  rw [attenuatedCoefficient, Matrix.add_apply, hsumEntry]
  calc
    |Cutoff.coefficientCutoff M.nu n ω x i j +
        ∑ k ∈ Finset.Ioc n J, weights k * ω.val k x i j| ≤
      |Cutoff.coefficientCutoff M.nu n ω x i j| +
        |∑ k ∈ Finset.Ioc n J, weights k * ω.val k x i j| := abs_add_le _ _
    _ ≤ M.nu + Cutoff.cutoffLocalControl ell n ω +
        ∑ k ∈ Finset.Ioc n J, |weights k| * localCubeControl ell (ω.val k) :=
      add_le_add hbase hsum
    _ = _ := rfl

private theorem raw_shell_weighted_coefficient_isElliptic (M : ABKModel 2)
    (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (Q : TriadicCube 2) :
    ∃ Lam : ℝ, IsEllipticFieldOn M.nu Lam (openCubeSet Q)
      (attenuatedCoefficient M n J weights ω) := by
  classical
  let K : Set (Vec 2) := closure (cubeSet Q)
  have hK : IsCompact K := (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨N, hcover⟩ := Cutoff.exists_nat_openOriginCube_of_isCompact hK
  let C : ℝ := M.nu + Cutoff.cutoffLocalControl (N : ℤ) n ω +
    ∑ k ∈ Finset.Ioc n J, |weights k| * localCubeControl (N : ℤ) (ω.val k)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg M.nu_pos.le
      (Cutoff.cutoffLocalControl_nonneg (N : ℤ) n ω))
      (Finset.sum_nonneg fun k hk => mul_nonneg (abs_nonneg _)
        (localCubeControl_nonneg (N : ℤ) (ω.val k)))
  have hcover' : ∀ x ∈ cubeSet Q,
      x ∈ openCubeSet (originCube 2 (N : ℤ)) := fun x hx => hcover (subset_closure hx)
  let Lam : ℝ := ((2 : ℝ) * 2 * C ^ 2 + M.nu ^ 2) / M.nu
  let reg : RegCoeffField 2 := Cutoff.coefficientCutoff M.nu n ω +
    ∑ k ∈ Finset.Ioc n J, weights k • ShellField.forgetShell (ω.val k)
  have hreg : ∀ x, reg.toFun x = attenuatedCoefficient M n J weights ω x := by
    intro x
    simp [reg, attenuatedCoefficient, RegCoeffField.finset_sum_apply]
  have hcubeEll : IsEllipticFieldOn M.nu Lam (cubeSet Q)
      (attenuatedCoefficient M n J weights ω) := by
    refine ⟨?_, ?_⟩
    · apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      have hm : Measurable (fun x => if x ∈ cubeSet Q then
          reg.toFun x i j else 0) :=
        (reg.entry_measurable i j).ite (measurableSet_cubeSet Q) measurable_const
      have heq : (fun x => if x ∈ cubeSet Q then
          attenuatedCoefficient M n J weights ω x i j else 0) =
        (fun x => if x ∈ cubeSet Q then reg.toFun x i j else 0) := by
        funext x
        by_cases hx : x ∈ cubeSet Q <;> simp [hx, hreg]
      rw [heq]
      exact hm
    · intro x hx
      apply Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
        (raw_shell_weighted_symmPart M n J weights ω x)
      intro i j
      have hxN : x ∈ openCubeSet (originCube 2 (N : ℤ)) := hcover' x hx
      simpa [C] using raw_shell_weighted_entry_bound M (N : ℤ) n J weights ω hxN i j
  have hopen := hcubeEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  refine ⟨Lam, ?_⟩
  simpa only [Lam] using hopen

theorem raw_shell_weighted_scalar_eq_coefficient_entry
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (ell : ℤ)
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (x : closure (cubeSet (originCube 2 n))) :
    rawShellBandScalarFromWeights M n s weights ω x =
      attenuatedCoefficient M n (n + (s : ℤ)) weights ω x.1 1 0 := by
  classical
  let J := n + (s : ℤ)
  have hold := olderField_apply_eq_coefficientCutoff
    (closure (cubeSet (originCube 2 n))) M ell n hK ω x
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
    simp [shellFieldScalarRestriction, planarShellScalarStream, planarShellMatrixEntry,
      ShellField.forgetShell_apply]
  rw [rawShellBandScalarFromWeights, ContinuousMap.add_apply, hold, hsum]
  simp only [attenuatedCoefficient, Matrix.add_apply, Cutoff.coefficientCutoff_apply]

/-- The source-mesh estimate with a frame label independent of the root scale.
The frame change contributes exactly the ratio of the two true scalars. -/
local instance rawShellClosedCubeCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

private noncomputable def rawShellClosedCubeInclusion {P V : TriadicCube 2}
    {d : ℕ} (hV : V ∈ descendantsAtDepth P d) :
    C(closure (cubeSet V), closure (cubeSet P)) :=
  ⟨fun x => ⟨x.1, closure_mono (cubeSet_subset_of_mem_descendantsAtDepth hV) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

private noncomputable def rawShellResponseCoefficientOnDescendant
    {P V : TriadicCube 2} {d : ℕ} (hV : V ∈ descendantsAtDepth P d) :
    C(closure (cubeSet P), ℝ) →L[ℝ] ResponseCoefficient (cubeSet V) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    (rawShellClosedCubeInclusion hV)).comp
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closure (cubeSet P)) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private theorem rawShellResponseCoefficientOnDescendant_extension
    {P V : TriadicCube 2} {d : ℕ}
    (hV : V ∈ descendantsAtDepth P d) (f : C(closure (cubeSet P), ℝ))
    {x : Vec 2} (hx : x ∈ cubeSet V) :
    responseCoefficientExtension (rawShellResponseCoefficientOnDescendant hV f) x =
      f ⟨x, subset_closure ((cubeSet_subset_of_mem_descendantsAtDepth hV) hx)⟩ := by
  rw [responseCoefficientExtension_eq _ hx]
  simp [rawShellResponseCoefficientOnDescendant, rawShellClosedCubeInclusion,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

theorem raw_shell_weighted_source_mesh_history_le_at_frame
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (_hs : 1 ≤ s)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (σ : ℝ) (hσ : 0 < σ)
    (m : ℕ) (hm : m ≤ 5)
    (hfinite : bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5)
      M n (n + (s : ℤ)) weights ω ≠ ∞)
    {U : TriadicCube 2} (hU : U ∈ descendantsAtDepth (originCube 2 n) m) :
    lemmaVInverseHistory U
        (responseFramePlanarCoefficientField M.nu σ
          (pureFluxOpenResponseRestriction n
            (rawShellBandScalarFromWeights M n s weights ω)))
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
      (σ / (Annealed.sigmaBar M n : ℝ)) *
        (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5)
          M n (n + (s : ℤ)) weights ω).toReal := by
  let P := originCube 2 n
  let K := closure (cubeSet P)
  let f := rawShellBandScalarFromWeights M n s weights ω
  let H := pureFluxOpenResponseRestriction n f
  let a := attenuatedCoefficient M n (n + (s : ℤ)) weights ω
  let af := responseFramePlanarCoefficientField M.nu σ H
  let q := (3 : ℝ) ^ (1 / 4 : ℝ)
  have hσn : 0 < (Annealed.sigmaBar M n : ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet P).isCompact_closure
  obtain ⟨Lam, hEll⟩ := raw_shell_weighted_coefficient_isElliptic
    M n (n + (s : ℤ)) weights ω P
  have hEllFrame := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet P) M.nu σ M.nu_pos hσ H
  have hMatrix (V : TriadicCube 2) (j : ℕ)
      (hV : V ∈ descendantsAtDepth U j) :
      coarseBlockMatrix (cubeSet V) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet V) a) := by
    have hVP : V ∈ descendantsAtDepth P (m + j) := by
      simpa [Nat.add_comm] using mem_descendantsAtDepth_add hU hV
    let HV := rawShellResponseCoefficientOnDescendant hVP f
    have hsource : responseFramePlanarCoefficientField M.nu σ H =ᵐ[
        volume.restrict (openCubeSet V)]
        responseFramePlanarCoefficientField M.nu σ HV := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet V)] with x hx
      have hxP : x ∈ openCubeSet P := openCubeSet_subset_of_mem_descendantsAtDepth hVP hx
      rw [responseFramePlanarCoefficientField_apply, responseFramePlanarCoefficientField_apply,
        pureFluxOpenResponseRestriction_value n f hxP,
        rawShellResponseCoefficientOnDescendant_extension hVP f
          (openCubeSet_subset_cubeSet V hx)]
    have hphysical (x : Vec 2) (hx : x ∈ openCubeSet V) :
        responsePlanarCoefficient M.nu (responseCoefficientExtension HV x) = a x := by
      have hscalar := raw_shell_weighted_scalar_eq_coefficient_entry M n s weights ω ell hK
        ⟨x, subset_closure (openCubeSet_subset_cubeSet P
          (openCubeSet_subset_of_mem_descendantsAtDepth hVP hx))⟩
      have hscalar' : f ⟨x, subset_closure (openCubeSet_subset_cubeSet P
          (openCubeSet_subset_of_mem_descendantsAtDepth hVP hx))⟩ = a x 1 0 := by
        simpa [a] using hscalar
      rw [rawShellResponseCoefficientOnDescendant_extension hVP f
        (openCubeSet_subset_cubeSet V hx), hscalar']
      exact planar_coefficient_eq_of_symmPart M.nu _
        (raw_shell_weighted_symmPart M n (n + (s : ℤ)) weights ω x)
    have hphysicalMatrix : coarseBlockMatrix (cubeSet V)
        (responsePlanarCoefficientField M.nu HV) = coarseBlockMatrix (cubeSet V) a := by
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V,
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V]
      apply coarseBlockMatrix_congr_of_ae_eq
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet V)] with x hx
      exact hphysical x hx
    have hfield :
        coarseBlockMatrix (cubeSet V)
          (responseFramePlanarCoefficientField M.nu σ H) =
        coarseBlockMatrix (cubeSet V)
          (responseFramePlanarCoefficientField M.nu σ HV) := by
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V,
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V]
      exact coarseBlockMatrix_congr_of_ae_eq hsource
    have hframe := response_coarseMatrix_frame_eq (Q := V)
      (measurableSet_cubeSet V) M.nu σ M.nu_pos hσ HV
    calc
      coarseBlockMatrix (cubeSet V) af =
          coarseBlockMatrix (cubeSet V)
            (responseFramePlanarCoefficientField M.nu σ HV) := hfield
      _ = frameMatrix σ (coarseBlockMatrix (cubeSet V)
            (responsePlanarCoefficientField M.nu HV)) := hframe
      _ = frameMatrix σ (coarseBlockMatrix (cubeSet V) a) := by rw [hphysicalMatrix]
  have hEllU := hEll.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hEllFrameU := hEllFrame.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hFrameHistory : lemmaVInverseHistory U af q = σ * lemmaVInverseHistory U a q :=
    raw_shell_inverseHistory_frame_eq_aux U a af hEllU hEllFrameU hσ (q := q)
      (fun V j hV => hMatrix V j hV)
  have hRootHistory := bank_root_history_physical U M n (n + (s : ℤ))
    weights ω a rfl hEllU
  have hPhysicalNonneg :
      0 ≤ lemmaVInverseHistory U a ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
    simpa [q] using lemmaVInverseHistory_nonneg U a hq
  have hHistoryEq : lemmaVInverseHistory U af q =
      (σ / (Annealed.sigmaBar M n : ℝ)) *
        (bankRootInverseHistory U M n (n + (s : ℤ)) weights ω).toReal := by
    rw [hFrameHistory, hRootHistory]
    rw [ENNReal.toReal_ofReal (mul_nonneg hσn.le hPhysicalNonneg)]
    simp only [q]
    field_simp [hσn.ne']
  have hRoot : U ∈ bankLocalRoots P 5 :=
    raw_shell_descendant_in_local_roots P U m hm hU
  have hmax := bank_member_history_le M (bankLocalRoots P 5) U hRoot n
    (n + (s : ℤ)) weights ω
  have hmaxReal := ENNReal.toReal_mono hfinite hmax
  have hratio : 0 ≤ σ / (Annealed.sigmaBar M n : ℝ) :=
    div_nonneg hσ.le hσn.le
  change lemmaVInverseHistory U af q ≤ _
  calc
    lemmaVInverseHistory U af q =
        (σ / (Annealed.sigmaBar M n : ℝ)) *
          (bankRootInverseHistory U M n (n + (s : ℤ)) weights ω).toReal := hHistoryEq
    _ ≤ (σ / (Annealed.sigmaBar M n : ℝ)) *
          (bankFiniteRootHistoryMax (bankLocalRoots P 5) M n
            (n + (s : ℤ)) weights ω).toReal :=
      mul_le_mul_of_nonneg_left hmaxReal hratio

/-- At an arbitrary true frame, the source history is controlled by the same
local bank with only the exact frame ratio added. -/
theorem raw_shell_weighted_source_history_ae_le_local_history_at_frame
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (s : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (σ : ℝ) (hσ : 0 < σ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      max (lemmaVTileHistory (originCube 2 n) (pureFluxBankSourceDepth s)
          (responseFramePlanarCoefficientField M.nu σ
            (pureFluxOpenResponseRestriction n
              (rawShellBandScalarFromWeights M n s weights ω))))
        (pureFluxSourceTileHistory (originCube 2 n) (pureFluxBankSourceDepth s)
          (responseFramePlanarCoefficientField M.nu σ
            (pureFluxOpenResponseRestriction n
              (rawShellBandScalarFromWeights M n s weights ω)))) ≤
        (σ / (Annealed.sigmaBar M n : ℝ)) *
          rawShellWeightedLocalHistory M n (n + (s : ℤ)) weights ω := by
  let Q := originCube 2 n
  let R := σ / (Annealed.sigmaBar M n : ℝ)
  have hσn : 0 < (Annealed.sigmaBar M n : ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  have hR : 0 ≤ R := div_nonneg hσ.le hσn.le
  have hbank := raw_shell_weighted_local_inverse_bank M h hM hg n
    (n + (s : ℤ)) (by omega) weights hw hpast
  have hdepth := pureFlux_bank_source_depth_le_four s hs
  have hdepth5 : pureFluxBankSourceDepth s ≤ 5 := by omega
  filter_upwards [hbank.history_finite] with ω hfinite
  let f := rawShellBandScalarFromWeights M n s weights ω
  let k := pureFluxOpenResponseRestriction n f
  let a := responseFramePlanarCoefficientField M.nu σ k
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ k
  have hsource (U : TriadicCube 2)
      (hU : U ∈ descendantsAtDepth Q (pureFluxBankSourceDepth s)) :
      lemmaVInverseHistory U a ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
        R * rawShellWeightedLocalHistory M n (n + (s : ℤ)) weights ω := by
    have h := raw_shell_weighted_source_mesh_history_le_at_frame M n s hs weights ω
      σ hσ (pureFluxBankSourceDepth s) hdepth5 (ne_of_lt hfinite) hU
    simpa only [a, k, f, R, rawShellWeightedLocalHistory] using h
  have hrem : pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s) a ≤
      R * rawShellWeightedLocalHistory M n (n + (s : ℤ)) weights ω :=
    pureFlux_source_tile_history_le Q (pureFluxBankSourceDepth s) a _ hsource
  have hmix : lemmaVTileHistory Q (pureFluxBankSourceDepth s) a ≤
      pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s) a :=
    tile_history_le_source_history Q (pureFluxBankSourceDepth s)
      M.nu σ M.nu_pos hσ k
  exact max_le (hmix.trans hrem) hrem

/-- The source-mesh history for an arbitrary finite attenuation is bounded by
the matching weighted local-bank history in the same base frame. -/
theorem raw_shell_weighted_source_mesh_history_le
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (_hs : 1 ≤ s)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (m : ℕ) (hm : m ≤ 5)
    (hfinite : bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5)
      M n (n + (s : ℤ)) weights ω ≠ ∞)
    {U : TriadicCube 2} (hU : U ∈ descendantsAtDepth (originCube 2 n) m) :
    lemmaVInverseHistory U
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M n : ℝ)
          (pureFluxOpenResponseRestriction n
            (rawShellBandScalarFromWeights M n s weights ω)))
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
      (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 n) 5)
        M n (n + (s : ℤ)) weights ω).toReal := by
  let P := originCube 2 n
  let K := closure (cubeSet P)
  let f := rawShellBandScalarFromWeights M n s weights ω
  let H := pureFluxOpenResponseRestriction n f
  let σ := (Annealed.sigmaBar M n : ℝ)
  let a := attenuatedCoefficient M n (n + (s : ℤ)) weights ω
  let af := responseFramePlanarCoefficientField M.nu σ H
  let q := (3 : ℝ) ^ (1 / 4 : ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet P).isCompact_closure
  obtain ⟨Lam, hEll⟩ := raw_shell_weighted_coefficient_isElliptic
    M n (n + (s : ℤ)) weights ω P
  have hEllFrame := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet P) M.nu σ M.nu_pos hσ H
  have hMatrix (V : TriadicCube 2) (j : ℕ)
      (hV : V ∈ descendantsAtDepth U j) :
      coarseBlockMatrix (cubeSet V) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet V) a) := by
    have hVP : V ∈ descendantsAtDepth P (m + j) := by
      simpa [Nat.add_comm] using mem_descendantsAtDepth_add hU hV
    let HV := rawShellResponseCoefficientOnDescendant hVP f
    have hsource : responseFramePlanarCoefficientField M.nu σ H =ᵐ[
        volume.restrict (openCubeSet V)]
        responseFramePlanarCoefficientField M.nu σ HV := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet V)] with x hx
      have hxP : x ∈ openCubeSet P := openCubeSet_subset_of_mem_descendantsAtDepth hVP hx
      rw [responseFramePlanarCoefficientField_apply, responseFramePlanarCoefficientField_apply,
        pureFluxOpenResponseRestriction_value n f hxP,
        rawShellResponseCoefficientOnDescendant_extension hVP f
          (openCubeSet_subset_cubeSet V hx)]
    have hphysical (x : Vec 2) (hx : x ∈ openCubeSet V) :
        responsePlanarCoefficient M.nu (responseCoefficientExtension HV x) = a x := by
      have hscalar := raw_shell_weighted_scalar_eq_coefficient_entry M n s weights ω ell hK
        ⟨x, subset_closure (openCubeSet_subset_cubeSet P
          (openCubeSet_subset_of_mem_descendantsAtDepth hVP hx))⟩
      have hscalar' : f ⟨x, subset_closure (openCubeSet_subset_cubeSet P
          (openCubeSet_subset_of_mem_descendantsAtDepth hVP hx))⟩ = a x 1 0 := by
        simpa [a] using hscalar
      rw [rawShellResponseCoefficientOnDescendant_extension hVP f
        (openCubeSet_subset_cubeSet V hx), hscalar']
      exact planar_coefficient_eq_of_symmPart M.nu _
        (raw_shell_weighted_symmPart M n (n + (s : ℤ)) weights ω x)
    have hphysicalMatrix : coarseBlockMatrix (cubeSet V)
        (responsePlanarCoefficientField M.nu HV) = coarseBlockMatrix (cubeSet V) a := by
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V,
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V]
      apply coarseBlockMatrix_congr_of_ae_eq
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet V)] with x hx
      exact hphysical x hx
    have hfield :
        coarseBlockMatrix (cubeSet V)
          (responseFramePlanarCoefficientField M.nu σ H) =
        coarseBlockMatrix (cubeSet V)
          (responseFramePlanarCoefficientField M.nu σ HV) := by
      rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V,
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V]
      exact coarseBlockMatrix_congr_of_ae_eq hsource
    have hframe := response_coarseMatrix_frame_eq (Q := V)
      (measurableSet_cubeSet V) M.nu σ M.nu_pos hσ HV
    calc
      coarseBlockMatrix (cubeSet V) af =
          coarseBlockMatrix (cubeSet V)
            (responseFramePlanarCoefficientField M.nu σ HV) := hfield
      _ = frameMatrix σ (coarseBlockMatrix (cubeSet V)
            (responsePlanarCoefficientField M.nu HV)) := hframe
      _ = frameMatrix σ (coarseBlockMatrix (cubeSet V) a) := by rw [hphysicalMatrix]
  have hEllU := hEll.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hEllFrameU := hEllFrame.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hFrameHistory : lemmaVInverseHistory U af q = σ * lemmaVInverseHistory U a q :=
    raw_shell_inverseHistory_frame_eq_aux U a af hEllU hEllFrameU hσ (q := q)
      (fun V j hV => hMatrix V j hV)
  have hRootHistory := bank_root_history_physical U M n (n + (s : ℤ))
    weights ω a rfl hEllU
  have hHistoryEq : lemmaVInverseHistory U af q =
      (bankRootInverseHistory U M n (n + (s : ℤ)) weights ω).toReal := by
    rw [hFrameHistory, hRootHistory, ENNReal.toReal_ofReal]
    exact mul_nonneg hσ.le (lemmaVInverseHistory_nonneg U a hq)
  have hRoot : U ∈ bankLocalRoots P 5 :=
    raw_shell_descendant_in_local_roots P U m hm hU
  have hmax := bank_member_history_le M (bankLocalRoots P 5) U hRoot n
    (n + (s : ℤ)) weights ω
  have hmaxReal := ENNReal.toReal_mono hfinite hmax
  change lemmaVInverseHistory U af q ≤ _
  calc
    lemmaVInverseHistory U af q =
        (bankRootInverseHistory U M n (n + (s : ℤ)) weights ω).toReal := hHistoryEq
    _ ≤ (bankFiniteRootHistoryMax (bankLocalRoots P 5) M n
          (n + (s : ℤ)) weights ω).toReal := hmaxReal

/-- All source tiles in the actual weighted band are controlled by its exact
finite-root local bank maximum on the bank's finiteness event. -/
theorem raw_shell_weighted_source_history_ae_le_local_history
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (s : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      rawShellWeightedSourceHistory M n s weights ω ≤
        rawShellWeightedLocalHistory M n (n + (s : ℤ)) weights ω := by
  let Q := originCube 2 n
  let σ := (Annealed.sigmaBar M n : ℝ)
  let K := closure (cubeSet Q)
  have hbank := raw_shell_weighted_local_inverse_bank M h hM hg n
    (n + (s : ℤ)) (by omega) weights hw hpast
  have hdepth := pureFlux_bank_source_depth_le_four s hs
  have hdepth5 : pureFluxBankSourceDepth s ≤ 5 := by omega
  filter_upwards [hbank.history_finite] with ω hfinite
  let f := rawShellBandScalarFromWeights M n s weights ω
  let k := pureFluxOpenResponseRestriction n f
  let a := responseFramePlanarCoefficientField M.nu σ k
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 k
  have hsource (U : TriadicCube 2)
      (hU : U ∈ descendantsAtDepth Q (pureFluxBankSourceDepth s)) :
      lemmaVInverseHistory U a ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
        rawShellWeightedLocalHistory M n (n + (s : ℤ)) weights ω := by
    have h := raw_shell_weighted_source_mesh_history_le M n s hs weights ω
      (pureFluxBankSourceDepth s) hdepth5 (ne_of_lt hfinite) hU
    simpa [rawShellWeightedLocalHistory, Q, σ, f, k, a] using h
  have hrem : pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s) a ≤
      rawShellWeightedLocalHistory M n (n + (s : ℤ)) weights ω :=
    pureFlux_source_tile_history_le Q (pureFluxBankSourceDepth s) a _ hsource
  have hmix : lemmaVTileHistory Q (pureFluxBankSourceDepth s) a ≤
      pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s) a :=
    tile_history_le_source_history Q (pureFluxBankSourceDepth s)
      M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M n).1 k
  have hmax := max_le (hmix.trans hrem) hrem
  simpa [rawShellWeightedSourceHistory, Q, σ, K, f, k, a] using hmax

/-- The full-response bank gives its exact cap for any bounded
attenuation vector through an arbitrary finite endpoint. -/
theorem raw_shell_weighted_full_response_L128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (s : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ j ≤ n + (s : ℤ) - 303, nativeInductionState M h j) :
    eLpNorm (rootTraceObservable M (originCube 2 n) n (n + (s : ℤ)) n weights)
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (rawTraceFullResponseCap M.gamma s) := by
  exact full_response_attenuated_bank128 M h hM hg (originCube 2 n) s n
    (by change n - 342 ≤ n; omega)
    (by change n ≤ n + (s : ℤ); omega) hpast weights hw

end ASDExplicitGamma.Inverse
