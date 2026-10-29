module

public import ASDExplicitGamma.Inverse.RawShellBandBankInputs
public import Algsuperdiff.Section3.Cutoff.P4UpperMoments
public import ASDExplicitGamma.Gaussian.LawTransfer

/-! Actual-law prefix controls for the raw finite-shell heat transport. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Gaussian
open scoped ENNReal

namespace ASDExplicitGamma.Inverse

private theorem raw_shell_cutoffLocalControl_mono
    (ell m J : ℤ) (hmJ : m ≤ J) (ω : CutoffSample 2) :
    cutoffLocalControl ell m ω ≤ cutoffLocalControl ell J ω := by
  let d : ℕ := Int.toNat (J - m)
  have hd : (d : ℤ) = J - m := by
    dsimp [d]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hmJ)
  have hs := summable_cutoffLocalControl ell J ω
  have hidx (r : ℕ) : J - ((r + d : ℕ) : ℤ) = m - (r : ℤ) := by
    simp only [Nat.cast_add]
    rw [hd]
    omega
  have htail : (∑' r : ℕ,
      localCubeControl ell (ω.1 (J - ((r + d : ℕ) : ℤ)))) =
        cutoffLocalControl ell m ω := by
    unfold cutoffLocalControl
    exact tsum_congr fun r => by rw [hidx r]
  have hdecomp := hs.sum_add_tsum_nat_add d
  rw [htail] at hdecomp
  have hnonneg : 0 ≤ ∑ r ∈ Finset.range d,
      localCubeControl ell (ω.1 (J - (r : ℤ))) := by
    apply Finset.sum_nonneg
    intro r hr
    exact localCubeControl_nonneg _ _
  change cutoffLocalControl ell m ω ≤
    ∑' r : ℕ, localCubeControl ell (ω.1 (J - (r : ℤ)))
  rw [← hdecomp]
  exact le_add_of_nonneg_left hnonneg

/-- The actual weighted prefix is measurable as a continuous-map-valued
random variable. -/
theorem measurable_raw_shell_weighted_prefix
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (weights : ℤ → ℝ) :
    Measurable (rawShellBandScalarFromWeights M n s weights) := by
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hold : Measurable (olderField K n) := measurable_olderField K ell n hK
  have hsum : Measurable (fun ω : CutoffSample 2 =>
      ∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
        weights k • shellFieldScalarRestriction K (ω.1 k)) := by
    apply Finset.measurable_sum
    intro k hk
    exact ((measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply k).comp measurable_subtype_coe)).const_smul (weights k)
  change Measurable (fun ω => olderField K n ω +
    ∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
      weights k • shellFieldScalarRestriction K (ω.1 k))
  exact hold.add hsum

/-- A weighted finite prefix is bounded by a finite multiple of the actual
lower-tail control at its endpoint. -/
private theorem raw_shell_weighted_prefix_norm_le
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (s : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (ell : ℤ)
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (ω : CutoffSample 2) :
    ‖rawShellBandScalarFromWeights M n s weights ω‖ ≤
      (1 + ((Finset.Ioc n (n + (s : ℤ))).card : ℝ)) *
        cutoffLocalControl ell (n + (s : ℤ)) ω := by
  classical
  let Q := originCube 2 n
  let K := closure (cubeSet Q)
  let m := n + (s : ℤ)
  have hControl : 0 ≤ cutoffLocalControl ell m ω := cutoffLocalControl_nonneg ell m ω
  have hOldNormFields : Summable (fun r : ℕ =>
      ‖shellFieldScalarRestriction K (ω.1 (n - (r : ℤ)))‖) := by
    apply Summable.of_nonneg_of_le
      (fun r : ℕ => norm_nonneg
        (shellFieldScalarRestriction K (ω.1 (n - (r : ℤ)))))
      (fun r : ℕ => by
        exact (show ‖shellFieldScalarRestriction K (ω.1 (n - (r : ℤ)))‖ ≤
          localCubeControl ell (ω.1 (n - (r : ℤ))) from by
            rw [ContinuousMap.norm_le _
              (localCubeControl_nonneg ell (ω.1 (n - (r : ℤ))))]
            intro x
            rw [Real.norm_eq_abs]
            change |(ω.1 (n - (r : ℤ))).1.1 x.1 1 0| ≤ _
            exact abs_entry_le_localCubeControl ell
              (ω.1 (n - (r : ℤ))) (hK x.2) 1 0))
      (summable_cutoffLocalControl ell n ω)
  have hOld : ‖olderField K n ω‖ ≤ cutoffLocalControl ell n ω := by
    calc
      ‖olderField K n ω‖ ≤
          ∑' r : ℕ, ‖shellFieldScalarRestriction K (ω.1 (n - (r : ℤ)))‖ :=
        by rw [olderField]; exact norm_tsum_le_tsum_norm hOldNormFields
      _ ≤ ∑' r : ℕ, localCubeControl ell (ω.1 (n - (r : ℤ))) :=
        hOldNormFields.tsum_le_tsum (fun r => by
          rw [ContinuousMap.norm_le _
            (localCubeControl_nonneg ell (ω.1 (n - (r : ℤ))))]
          intro x
          rw [Real.norm_eq_abs]
          change |(ω.1 (n - (r : ℤ))).1.1 x.1 1 0| ≤ _
          exact abs_entry_le_localCubeControl ell
            (ω.1 (n - (r : ℤ))) (hK x.2) 1 0)
          (summable_cutoffLocalControl ell n ω)
      _ = cutoffLocalControl ell n ω := rfl
  have hOld' : ‖olderField K n ω‖ ≤ cutoffLocalControl ell m ω :=
    hOld.trans (raw_shell_cutoffLocalControl_mono ell n m (by dsimp [m]; omega) ω)
  have hterm (k : ℤ) (hk : k ∈ Finset.Ioc n m) :
      ‖weights k • shellFieldScalarRestriction K (ω.1 k)‖ ≤
        cutoffLocalControl ell m ω := by
    have hweight := hw k (by simpa [m] using hk)
    have hshell : ‖shellFieldScalarRestriction K (ω.1 k)‖ ≤
        localCubeControl ell (ω.1 k) := by
      rw [ContinuousMap.norm_le _ (localCubeControl_nonneg ell (ω.1 k))]
      intro x
      rw [Real.norm_eq_abs]
      change |(ω.1 k).1.1 x.1 1 0| ≤ localCubeControl ell (ω.1 k)
      exact abs_entry_le_localCubeControl ell (ω.1 k) (hK x.2) 1 0
    have hlocal : localCubeControl ell (ω.1 k) ≤ cutoffLocalControl ell m ω := by
      let r : ℕ := Int.toNat (m - k)
      have hr : (r : ℤ) = m - k := by
        dsimp [r]
        apply Int.toNat_of_nonneg
        exact sub_nonneg.mpr (Finset.mem_Ioc.mp hk).2
      have hs := summable_cutoffLocalControl ell m ω
      have hsingleton := hs.sum_le_tsum ({r} : Finset ℕ)
        (fun j hj => localCubeControl_nonneg ell (ω.1 (m - (j : ℤ))))
      have hindex : m - (r : ℤ) = k := by rw [hr]; omega
      have hsingle' : localCubeControl ell (ω.1 (m - (r : ℤ))) ≤
          ∑' j : ℕ, localCubeControl ell (ω.1 (m - (j : ℤ))) := by
        simpa only [Finset.sum_singleton] using hsingleton
      change localCubeControl ell (ω.1 k) ≤
        ∑' j : ℕ, localCubeControl ell (ω.1 (m - (j : ℤ)))
      rw [← hindex]
      exact hsingle'
    calc
      ‖weights k • shellFieldScalarRestriction K (ω.1 k)‖ =
          |weights k| * ‖shellFieldScalarRestriction K (ω.1 k)‖ := norm_smul _ _
      _ = weights k * ‖shellFieldScalarRestriction K (ω.1 k)‖ := by
        rw [abs_of_nonneg hweight.1]
      _ ≤ ‖shellFieldScalarRestriction K (ω.1 k)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hweight.2
      _ ≤ localCubeControl ell (ω.1 k) := hshell
      _ ≤ cutoffLocalControl ell m ω := hlocal
  have hsum : ‖∑ k ∈ Finset.Ioc n m,
      weights k • shellFieldScalarRestriction K (ω.1 k)‖ ≤
        ((Finset.Ioc n m).card : ℝ) * cutoffLocalControl ell m ω := by
    calc
      _ ≤ ∑ k ∈ Finset.Ioc n m,
          ‖weights k • shellFieldScalarRestriction K (ω.1 k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.Ioc n m, cutoffLocalControl ell m ω :=
          Finset.sum_le_sum (fun k hk => hterm k hk)
      _ = _ := by simp
  change ‖olderField K n ω +
    ∑ k ∈ Finset.Ioc n m, weights k • shellFieldScalarRestriction K (ω.1 k)‖ ≤ _
  calc
    _ ≤ ‖olderField K n ω‖ +
        ‖∑ k ∈ Finset.Ioc n m,
          weights k • shellFieldScalarRestriction K (ω.1 k)‖ := norm_add_le _ _
    _ ≤ cutoffLocalControl ell m ω +
        ((Finset.Ioc n m).card : ℝ) * cutoffLocalControl ell m ω :=
      add_le_add hOld' hsum
    _ = _ := by ring

/-- The law of a weighted prefix has all polynomial moments, for use as the
base distribution in the one-shell Gaussian heat identity. -/
theorem raw_shell_weighted_prefix_polynomial_moments
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (s : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1) :
    ∀ d : ℕ, Integrable (fun x : C(closure (cubeSet (originCube 2 n)), ℝ) =>
      (1 + ‖x‖) ^ d)
      ((Cutoff.cutoffSampleLaw M).toMeasure.map
        (rawShellBandScalarFromWeights M n s weights)) := by
  intro d
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := rawShellBandScalarFromWeights M n s weights
  let m := n + (s : ℤ)
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hmeas : Measurable X := measurable_raw_shell_weighted_prefix M n s weights
  have hmajor : Integrable (fun ω : CutoffSample 2 =>
      (1 + cutoffLocalControl ell m ω) ^ d) μ :=
    integrable_one_add_cutoffLocalControl_pow M ell m d
  have hcomp : Integrable (fun ω : CutoffSample 2 => (1 + ‖X ω‖) ^ d) μ := by
    let C : ℝ := 1 + ((Finset.Ioc n m).card : ℝ)
    have hC : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    have hU : ∀ ω : CutoffSample 2, 0 ≤ cutoffLocalControl ell m ω :=
      fun ω => cutoffLocalControl_nonneg ell m ω
    have hbound : ∀ ω : CutoffSample 2, (1 + ‖X ω‖) ^ d ≤
        C ^ d * (1 + cutoffLocalControl ell m ω) ^ d := by
      intro ω
      have hnorm := raw_shell_weighted_prefix_norm_le M n s weights hw ell hK ω
      have hbase : 1 + ‖X ω‖ ≤ C * (1 + cutoffLocalControl ell m ω) := by
        dsimp [C]
        nlinarith [hnorm, hU ω]
      calc
        (1 + ‖X ω‖) ^ d ≤ (C * (1 + cutoffLocalControl ell m ω)) ^ d :=
          pow_le_pow_left₀ (by positivity) hbase d
        _ = C ^ d * (1 + cutoffLocalControl ell m ω) ^ d := mul_pow C _ _
    have hscaled := hmajor.const_mul (C ^ d)
    apply hscaled.mono'
      (((measurable_const.add (continuous_norm.measurable.comp hmeas)).pow_const d).aestronglyMeasurable)
    filter_upwards with ω
    change ‖(1 + ‖X ω‖) ^ d‖ ≤ _
    have hnonneg : 0 ≤ (1 + ‖X ω‖) ^ d := by positivity
    rw [Real.norm_of_nonneg hnonneg]
    calc
      (1 + ‖X ω‖) ^ d ≤ C ^ d *
          (1 + cutoffLocalControl ell m ω) ^ d := hbound ω
      _ = C ^ d * (1 + cutoffLocalControl ell m ω) ^ d := rfl
  apply (integrable_map_measure (by fun_prop) hmeas.aemeasurable).mpr
  simpa only [μ, X, Function.comp_def] using hcomp

/-- A weighted completed prefix is independent of the next fresh shell. The
proof records its shell-index support explicitly, so deterministic attenuation
of the past coordinates does not affect independence. -/
theorem indepFun_raw_shell_weighted_prefix_fresh
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (weights : ℤ → ℝ) :
    IndepFun (rawShellBandScalarFromWeights M n s weights)
      (fun ω : CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 n))) (ω.1 (n + (s : ℤ) + 1)))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  let m := n + (s : ℤ)
  let X : Cutoff.ShellSeq 2 → C(K, ℝ) := fun ω =>
    (∑' r : ℕ, shellFieldScalarRestriction K (ω (n - (r : ℤ)))) +
      ∑ k ∈ Finset.Ioc n m, weights k • shellFieldScalarRestriction K (ω k)
  let Y : Cutoff.ShellSeq 2 → C(K, ℝ) := fun ω =>
    shellFieldScalarRestriction K (ω (m + 1))
  have hX : @Measurable _ _ (Cutoff.shellIndexSigma (Iic m)) _ X := by
    let : MeasurableSpace (Cutoff.ShellSeq 2) := Cutoff.shellIndexSigma (Iic m)
    change Measurable X
    apply (Measurable.tsum fun r : ℕ =>
      (measurable_shellFieldScalarRestriction K).comp
        (Cutoff.measurable_shellCoordinate_shellIndexSigma (by
          change n - (r : ℤ) ≤ m
          dsimp [m]
          omega))).add
    apply Finset.measurable_sum
    intro k hk
    exact ((measurable_shellFieldScalarRestriction K).comp
      (Cutoff.measurable_shellCoordinate_shellIndexSigma (show k ∈ Iic m from
        Finset.mem_Ioc.mp hk |>.2))).const_smul (weights k)
  have hY : @Measurable _ _ (Cutoff.shellIndexSigma ({m + 1} : Set ℤ)) _ Y := by
    let : MeasurableSpace (Cutoff.ShellSeq 2) :=
      Cutoff.shellIndexSigma ({m + 1} : Set ℤ)
    exact (measurable_shellFieldScalarRestriction K).comp
      (Cutoff.measurable_shellCoordinate_shellIndexSigma (by simp))
  have hXb := hX.mono (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hYb := hY.mono (Cutoff.shellIndexSigma_le_borel _) le_rfl
  have hind := Cutoff.indepFun_of_measurable_shellIndexSigma_of_disjoint M
    (Set.disjoint_left.mpr (fun k hk hk' => by
      simp only [mem_Iic, mem_singleton_iff] at hk hk'
      omega)) hX hY
  have hpair := hind.map_prod_eq_prod_map_map hXb.aemeasurable hYb.aemeasurable
  have hXactual : X ∘ Subtype.val = rawShellBandScalarFromWeights M n s weights := by
    funext ω
    change (∑' r : ℕ, shellFieldScalarRestriction K (ω.1 (n - (r : ℤ)))) +
        ∑ k ∈ Finset.Ioc n m, weights k • shellFieldScalarRestriction K (ω.1 k) = _
    simp only [rawShellBandScalarFromWeights, olderField, K, m]
  have hYactual : Y ∘ Subtype.val = fun ω : CutoffSample 2 =>
      shellFieldScalarRestriction K (ω.1 (m + 1)) := by
    funext ω
    rfl
  have hpairfun : (fun ω : CutoffSample 2 => (X ω.1, Y ω.1)) =
      (fun ω => (rawShellBandScalarFromWeights M n s weights ω,
        shellFieldScalarRestriction K (ω.1 (m + 1)))) := by
    funext ω
    exact Prod.ext (congrFun hXactual ω) (congrFun hYactual ω)
  have hXactual' : (fun ω : CutoffSample 2 => X ω.1) =
      rawShellBandScalarFromWeights M n s weights := by
    simpa only [Function.comp_def] using hXactual
  have hYactual' : (fun ω : CutoffSample 2 => Y ω.1) =
      (fun ω => shellFieldScalarRestriction K (ω.1 (m + 1))) := by
    simpa only [Function.comp_def] using hYactual
  rw [← Cutoff.map_cutoffSampleLaw_val M,
    Measure.map_map (hXb.prodMk hYb) measurable_subtype_coe,
    Measure.map_map hXb measurable_subtype_coe,
    Measure.map_map hYb measurable_subtype_coe] at hpair
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_raw_shell_weighted_prefix M n s weights).aemeasurable
    ((measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)).aemeasurable).mpr
  change Measure.map (fun ω : CutoffSample 2 => (X ω.1, Y ω.1))
      (Cutoff.cutoffSampleLaw M).toMeasure =
    (Measure.map (fun ω : CutoffSample 2 => X ω.1)
      (Cutoff.cutoffSampleLaw M).toMeasure).prod
      (Measure.map (fun ω : CutoffSample 2 => Y ω.1)
        (Cutoff.cutoffSampleLaw M).toMeasure) at hpair
  rw [hpairfun] at hpair
  rw [hXactual', hYactual'] at hpair
  simpa only [K, m, Function.comp_def] using hpair

/-- The literal one-shell heat expectation over a deterministic weighted
prefix on the actual cutoff probability space. -/
noncomputable def rawShellBandPrefixHeatAverage (M : ABKModel 2) (n : ℤ)
    (s : ℕ) (weights : ℤ → ℝ) (Φ : C(closure (cubeSet (originCube 2 n)), ℝ) → ℝ)
    (t : ℝ) : ℝ :=
  ∫ ω, Φ (rawShellBandScalarFromWeights M n s weights ω +
    Real.sqrt t • shellFieldScalarRestriction
      (closure (cubeSet (originCube 2 n))) (ω.1 (n + (s : ℤ) + 1)))
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The profile at the `i`th coordinate step: retain the prescribed weights
through `n+i`, insert the current shell with heat coefficient `sqrt t`, and
set all later coordinates to zero. -/
noncomputable def rawShellBandStepWeights (n : ℤ) (i : ℕ)
    (weights : ℤ → ℝ) (t : ℝ) : ℤ → ℝ := fun k =>
  if k = n + (i : ℤ) + 1 then Real.sqrt t * weights k
  else if k ∈ Finset.Ioc n (n + (i : ℤ)) then weights k else 0

/-- The step profile is exactly the old weighted prefix plus the current
fresh-shell insertion. -/
theorem raw_shell_band_step_scalar_eq (M : ABKModel 2) (n : ℤ) (i : ℕ)
    (weights : ℤ → ℝ) (t : ℝ) (ω : CutoffSample 2) :
    rawShellBandScalarFromWeights M n (i + 1) (rawShellBandStepWeights n i weights t) ω =
      rawShellBandScalarFromWeights M n i weights ω +
        (Real.sqrt t * weights (n + (i : ℤ) + 1)) •
        shellFieldScalarRestriction (closure (cubeSet (originCube 2 n)))
          (ω.1 (n + (i : ℤ) + 1)) := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  have hset : Finset.Ioc n (n + ((i + 1 : ℕ) : ℤ)) =
      insert (n + (i : ℤ) + 1) (Finset.Ioc n (n + (i : ℤ))) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
    omega
  have hnew : n + (i : ℤ) + 1 ∉ Finset.Ioc n (n + (i : ℤ)) := by
    simp only [Finset.mem_Ioc]
    omega
  have hsum :
      (∑ k ∈ Finset.Ioc n (n + ((i + 1 : ℕ) : ℤ)),
        rawShellBandStepWeights n i weights t k • shellFieldScalarRestriction K (ω.1 k)) =
      (∑ k ∈ Finset.Ioc n (n + (i : ℤ)),
        weights k • shellFieldScalarRestriction K (ω.1 k)) +
        (Real.sqrt t * weights (n + (i : ℤ) + 1)) •
          shellFieldScalarRestriction K (ω.1 (n + (i : ℤ) + 1)) := by
    rw [hset, Finset.sum_insert hnew]
    have htop : rawShellBandStepWeights n i weights t (n + (i : ℤ) + 1) =
        Real.sqrt t * weights (n + (i : ℤ) + 1) := by simp [rawShellBandStepWeights]
    have hrest : (∑ k ∈ Finset.Ioc n (n + (i : ℤ)),
        rawShellBandStepWeights n i weights t k • shellFieldScalarRestriction K (ω.1 k)) =
        ∑ k ∈ Finset.Ioc n (n + (i : ℤ)),
          weights k • shellFieldScalarRestriction K (ω.1 k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hne : k ≠ n + (i : ℤ) + 1 := by
        simp only [Finset.mem_Ioc] at hk
        omega
      simp [rawShellBandStepWeights, hne, hk]
    rw [htop, hrest]
    abel
  ext x
  simp only [rawShellBandScalarFromWeights, ContinuousMap.add_apply,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  have hsumx := congrArg (fun f : C(K, ℝ) => f x) hsum
  simp only [ContinuousMap.add_apply, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply] at hsumx
  rw [hsumx]
  abel

/-- The arbitrary-base heat expectation for one fresh shell is exactly the
literal actual-law expectation. The base may be any finite deterministic
weighted prefix, not only the unattenuated older field. -/
theorem raw_shell_band_prefix_heat_transfer
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (s : ℕ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (s : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (Φ : C(closure (cubeSet (originCube 2 n)), ℝ) → ℝ)
    (hΦ : Measurable Φ) (hg : HasPolynomialGrowth Φ) :
    ∃ (T : GaussianFactorL2 ℕ →L[ℝ]
          C(closure (cubeSet (originCube 2 n)), ℝ))
      (v : ℕ → GaussianFactorL2 ℕ) (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : CutoffSample 2 => shellFieldScalarRestriction
          (closure (cubeSet (originCube 2 n))) (ω.1 (n + (s : ℤ) + 1))) =
        standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) ∧
      ∀ t : ℝ,
        rawShellBandPrefixHeatAverage M n s weights Φ t =
          randomBaseHeatAverage hA T
            ((Cutoff.cutoffSampleLaw M).toMeasure.map
              (rawShellBandScalarFromWeights M n s weights)) Φ t := by
  let K := closure (cubeSet (originCube 2 n))
  let ρ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := rawShellBandScalarFromWeights M n s weights
  let Y := fun ω : CutoffSample 2 =>
    shellFieldScalarRestriction K (ω.1 (n + (s : ℤ) + 1))
  obtain ⟨T, v, hA, hlaw⟩ :=
    freshShell_map_scalarRestriction_eq_gaussianSeries M h hM
      (n + (s : ℤ)) (K := K)
  have hX : Measurable X := measurable_raw_shell_weighted_prefix M n s weights
  have hY : Measurable Y := (measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (n + (s : ℤ) + 1)).comp measurable_subtype_coe)
  have hi := indepFun_raw_shell_weighted_prefix_fresh M n s weights
  have hMom : ∀ d : ℕ, Integrable (fun x : C(K, ℝ) => (1 + ‖x‖) ^ d)
      (ρ.map X) := raw_shell_weighted_prefix_polynomial_moments M n s weights hw
  have hh := integral_independent_insertion ρ X Y hX hY hi hA T hlaw hMom Φ hΦ hg
  have hint := integrable_randomBaseHeatIntegrand hA T (ρ.map X) hMom Φ hΦ hg
  refine ⟨T, v, hA, hlaw, ?_⟩
  intro t
  have hht := hh t
  have heq := hht.2.trans (integral_prod _ (hint t))
  simpa only [K, X, Y, ρ, rawShellBandPrefixHeatAverage,
    randomBaseHeatAverage, gaussianSeriesHeatAverage, gaussianSeriesHeatArgument,
    Function.comp_def] using heq

end ASDExplicitGamma.Inverse
