module

public import ASDExplicitGamma.Gaussian.OlderField
public import ASDExplicitGamma.Model.ShellScaling
public import Algsuperdiff.Section3.Cutoff.ShellIndependence
public import Algsuperdiff.Section3.Cutoff.CutoffSampleRange
public import Algsuperdiff.Section3.Cutoff.Ellipticity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The older coefficient cutoff and a fresh shell

This module identifies Superdiffusion's literal cutoff series with the
completed older field, transfers the fresh-shell independence to the genuine
cutoff carrier, and records local ellipticity for deterministic partial
insertions.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Homogenization
open scoped ENNReal Topology

namespace ASDExplicitGamma.Model

/-- Pointwise, the frozen coefficient cutoff is exactly its deterministic
`nu I` part plus the convergent series of all shells at or below `m`. -/
theorem coefficientCutoff_eq_nu_add_cutoffValue
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Cutoff.coefficientCutoff M.nu m ω x =
      M.nu • (1 : Mat 2) + Cutoff.cutoffValue m ω x := by
  rw [Cutoff.coefficientCutoff_apply]
  rfl

/-- The coefficient identity holds as an equality of continuous fields, hence
also after restriction to every compact observation square. -/
theorem coefficientCutoff_eq_nu_add_olderField_entry
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) (i j : Fin 2) :
    Cutoff.coefficientCutoff M.nu m ω x i j =
      (M.nu • (1 : Mat 2)) i j +
        ∑' r : ℕ, ω.1 (m - (r : ℤ)) x i j := by
  rw [coefficientCutoff_eq_nu_add_cutoffValue, Matrix.add_apply,
    Cutoff.cutoffValue]

/-- The fresh shell marginal on the cutoff carrier is the canonical shell
marginal at level `m+1`. -/
theorem map_freshShell_eq_shellMarginalLaw
    (M : ABKModel 2) (m : ℤ) :
    Measure.map (fun ω : Cutoff.CutoffSample 2 => ω.1 (m + 1))
      (Cutoff.cutoffSampleLaw M).toMeasure =
      (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure := by
  calc
    Measure.map (fun ω : Cutoff.CutoffSample 2 => ω.1 (m + 1))
        (Cutoff.cutoffSampleLaw M).toMeasure =
        Measure.map (fun F : ℤ → ShellField 2 => F (m + 1))
          (Measure.map (Subtype.val : Cutoff.CutoffSample 2 → ShellSeq 2)
            (Cutoff.cutoffSampleLaw M).toMeasure) := by
      rw [Measure.map_map (measurable_pi_apply (m + 1)) measurable_subtype_coe]
      rfl
    _ = Measure.map (fun F : ℤ → ShellField 2 => F (m + 1)) M.P.toMeasure := by
      rw [Cutoff.map_cutoffSampleLaw_val]
    _ = (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure := rfl

/-- The fresh shell law is the exact triadic dilation of the zero-shell law. -/
theorem map_freshShell_eq_scaledZeroShellLaw
    (M : ABKModel 2) (m : ℤ) :
    Measure.map (fun ω : Cutoff.CutoffSample 2 => ω.1 (m + 1))
      (Cutoff.cutoffSampleLaw M).toMeasure =
      Measure.map (ShellField.triadicScale M.gamma (m + 1))
        (ShellField.zeroShellLaw M.P).toMeasure := by
  rw [map_freshShell_eq_shellMarginalLaw,
    M.shellPrefix.marginal_scaling (m + 1), ProbabilityMeasure.toMeasure_map]

private noncomputable def ballProbe (x : Vec 2) (r : ℝ) : Vec 2 → ℝ :=
  fun y => (volume.real (Metric.ball x r))⁻¹ *
    (Metric.ball x r).indicator (fun _ : Vec 2 => (1 : ℝ)) y

private theorem volume_real_ball_pos (x : Vec 2) {r : ℝ} (hr : 0 < r) :
    0 < volume.real (Metric.ball x r) := by
  have hv : volume.real (Metric.ball x r) = (2 * r) ^ 2 := by
    rw [MeasureTheory.measureReal_def, Real.volume_pi_ball x hr,
      ENNReal.toReal_ofReal (by positivity)]
    simp [Fintype.card_fin]
  rw [hv]
  positivity

private theorem ballProbe_isProbe (x : Vec 2) {r : ℝ} (hr : 0 < r) :
    IsProbeR (ballProbe x r) := by
  let V := volume.real (Metric.ball x r)
  have hV : 0 < V := volume_real_ball_pos x hr
  refine ⟨?_, ?_, ?_⟩
  · have hs : MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet
    have hm : Measurable ((Metric.ball x r).indicator (fun _ : Vec 2 => (1 : ℝ))) :=
      measurable_one.indicator hs
    change Measurable (fun y : Vec 2 =>
      (volume.real (Metric.ball x r))⁻¹ *
        (Metric.ball x r).indicator (fun _ : Vec 2 => (1 : ℝ)) y)
    exact measurable_const.mul hm
  · refine ⟨|V⁻¹|, fun y => ?_⟩
    by_cases hy : y ∈ Metric.ball x r <;> simp [ballProbe, V, hy]
  · have hsupp : Function.support (ballProbe x r) ⊆ Metric.closedBall x r := by
      intro y hy
      by_contra hclosed
      have hball : y ∉ Metric.ball x r := fun hb => hclosed (Metric.ball_subset_closedBall hb)
      exact (Function.mem_support.mp hy) (by simp [ballProbe, hball])
    have htsupp : tsupport (ballProbe x r) ⊆ Metric.closedBall x r :=
      closure_minimal hsupp Metric.isClosed_closedBall
    exact (isCompact_closedBall x r).of_isClosed_subset
      (isClosed_tsupport (ballProbe x r)) htsupp

private theorem entryTestR_ballProbe_eq_setAverage
    (a : RegCoeffField 2) (i j : Fin 2) (x : Vec 2) (r : ℝ) :
    entryTestR i j (ballProbe x r) a =
      ⨍ y in Metric.ball x r, a y i j ∂volume := by
  let V := volume.real (Metric.ball x r)
  have hfun : (fun y : Vec 2 => a y i j * ballProbe x r y) =
      (Metric.ball x r).indicator (fun y => V⁻¹ * a y i j) := by
    funext y
    by_cases hy : y ∈ Metric.ball x r
    · simp [ballProbe, V, hy, mul_comm]
    · simp [ballProbe, V, hy]
  unfold Homogenization.entryTestR
  rw [hfun, integral_indicator Metric.isOpen_ball.measurableSet]
  rw [integral_const_mul, MeasureTheory.setAverage_eq]
  simp [V, smul_eq_mul]

private theorem norm_setAverage_le_of_norm_le_const
    {s : Set (Vec 2)} {f : Vec 2 → ℝ} {C : ℝ}
    (hfinite : volume s < ∞) (hpos : 0 < volume.real s)
    (hbound : ∀ y ∈ s, ‖f y‖ ≤ C) :
    ‖⨍ y in s, f y ∂volume‖ ≤ C := by
  rw [setAverage_eq]
  have hI := norm_setIntegral_le_of_norm_le_const hfinite hbound
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
  calc
    (volume.real s)⁻¹ * ‖∫ y in s, f y ∂volume‖ ≤
        (volume.real s)⁻¹ * (C * volume.real s) :=
      mul_le_mul_of_nonneg_left hI (le_of_lt (inv_pos.mpr hpos))
    _ = C := by field_simp

private theorem tendsto_ballAverage_of_continuous
    {f : Vec 2 → ℝ} (hf : Continuous f) (x : Vec 2) :
    Tendsto (fun n : ℕ => ⨍ y in Metric.ball x (1 / ((n : ℝ) + 1)),
      f y ∂volume) atTop (𝓝 (f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hfAt : ContinuousAt f x := hf.continuousAt
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousAt_iff.mp hfAt (ε / 2) (by linarith)
  have htend := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ :=
    htend.eventually (Iio_mem_nhds hδ)
  filter_upwards [hsmall] with n hn
  let r : ℝ := 1 / ((n : ℝ) + 1)
  have hr : 0 < r := by positivity
  have hballFinite : volume (Metric.ball x r) < ∞ := by
    rw [Real.volume_pi_ball x hr]
    exact ENNReal.ofReal_lt_top
  have hballPos : 0 < volume.real (Metric.ball x r) := volume_real_ball_pos x hr
  have hfint : IntegrableOn f (Metric.ball x r) volume :=
    hf.continuousOn.integrableOn_compact (isCompact_closedBall x r) |>.mono_set
      Metric.ball_subset_closedBall
  have hcint : IntegrableOn (fun _ : Vec 2 => f x) (Metric.ball x r) volume :=
    integrableOn_const (ne_of_lt hballFinite)
  have hdiffint : IntegrableOn (fun y : Vec 2 => f y - f x)
      (Metric.ball x r) volume := hfint.sub hcint
  have hbd : ∀ y ∈ Metric.ball x r, ‖f y - f x‖ ≤ ε / 2 := by
    intro y hy
    have hdist : dist y x < δ := (Metric.mem_ball.mp hy).trans hn
    have hpoint := hcont hdist
    simpa [Real.dist_eq] using le_of_lt hpoint
  have hnorm := norm_setAverage_le_of_norm_le_const hballFinite hballPos hbd
  have hballNeZero : volume (Metric.ball x r) ≠ 0 := by
    intro hz
    apply (ne_of_gt hballPos)
    rw [MeasureTheory.measureReal_def, hz]
    simp
  have hconst : ⨍ y in Metric.ball x r, (fun _ : Vec 2 => f x) y ∂volume = f x :=
    setAverage_const hballNeZero (ne_of_lt hballFinite) (f x)
  have hEq : (⨍ y in Metric.ball x r, (fun y => f y - f x) y ∂volume) =
      (⨍ y in Metric.ball x r, f y ∂volume) - f x := by
    calc
      _ = (⨍ y in Metric.ball x r, f y ∂volume) -
          (⨍ y in Metric.ball x r, (fun _ : Vec 2 => f x) y ∂volume) :=
        setAverage_sub hfint hcint
      _ = _ := by rw [hconst]
  have hdist : dist (⨍ y in Metric.ball x r, f y ∂volume) (f x) ≤ ε / 2 := by
    rw [Real.dist_eq, ← hEq]
    simpa [Real.norm_eq_abs] using hnorm
  have hlt : dist (⨍ y in Metric.ball x r, f y ∂volume) (f x) < ε :=
    lt_of_le_of_lt hdist (by linarith)
  simpa [r] using hlt

private theorem measurable_entryTestR_local (i j : Fin 2) {φ : Vec 2 → ℝ}
    (hφ : IsProbeR φ) :
    @Measurable (RegCoeffField 2) ℝ (LocalSigmaR Set.univ) (borel ℝ)
      (entryTestR i j φ) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, j, φ, hφ, Set.subset_univ _, t, ht, rfl⟩

private theorem measurable_coefficientCutoff_entry_local
    (M : ABKModel 2) (m : ℤ) (x : Vec 2) (i j : Fin 2) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M m Set.univ) (borel ℝ)
      (fun ω => Cutoff.coefficientCutoff M.nu m ω x i j) := by
  let f : ℕ → Cutoff.CutoffSample 2 → ℝ := fun n ω =>
    entryTestR i j (ballProbe x (1 / ((n : ℝ) + 1)))
      (Cutoff.coefficientCutoff M.nu m ω)
  have hf : ∀ n, @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M m Set.univ) (borel ℝ) (f n) := by
    intro n
    exact (measurable_entryTestR_local i j (ballProbe_isProbe x (by positivity))).comp
      (Cutoff.measurable_coefficientCutoff_local M m Set.univ)
  have hlim : Tendsto f atTop
      (𝓝 (fun ω : Cutoff.CutoffSample 2 =>
        Cutoff.coefficientCutoff M.nu m ω x i j)) := by
    apply tendsto_pi_nhds.mpr
    intro ω
    have hcont : Continuous (fun y : Vec 2 =>
        Cutoff.coefficientCutoff M.nu m ω y i j) := by
      change Continuous (fun y : Vec 2 =>
        (M.nu • (1 : Mat 2)) i j + Cutoff.cutoff m ω y i j)
      exact continuous_const.add (Cutoff.continuous_cutoff_entry m ω i j)
    have havg := tendsto_ballAverage_of_continuous hcont x
    have hEq : ∀ n, f n ω =
        ⨍ y in Metric.ball x (1 / ((n : ℝ) + 1)),
          Cutoff.coefficientCutoff M.nu m ω y i j ∂volume := by
      intro n
      exact entryTestR_ballProbe_eq_setAverage
        (Cutoff.coefficientCutoff M.nu m ω) i j x (1 / ((n : ℝ) + 1))
    exact havg.congr' (Filter.Eventually.of_forall fun n => (hEq n).symm)
  exact @measurable_of_tendsto_metrizable
    (Cutoff.CutoffSample 2) ℝ (Cutoff.cutoffSampleLocalSigma M m Set.univ)
    _ _ _ _ f (fun ω => Cutoff.coefficientCutoff M.nu m ω x i j) hf hlim

/-- The coefficient cutoff is measurable from the completed older-shell local
information in the full regular-coefficient Borel structure. Point values are
recovered as limits of normalized local ball averages. -/
theorem measurable_coefficientCutoff_local_field (M : ABKModel 2) (m : ℤ) :
    @Measurable (Cutoff.CutoffSample 2) (RegCoeffField 2)
      (Cutoff.cutoffSampleLocalSigma M m Set.univ) inferInstance
      (Cutoff.coefficientCutoff M.nu m) := by
  apply @Homogenization.measurable_into_regCoeffField' 2
    (Cutoff.CutoffSample 2) (Cutoff.cutoffSampleLocalSigma M m Set.univ)
    (Cutoff.coefficientCutoff M.nu m) ?_ ?_
  · intro x i j
    exact measurable_coefficientCutoff_entry_local M m x i j
  · intro i j φ hφ
    exact (measurable_entryTestR_local i j hφ).comp
      (Cutoff.measurable_coefficientCutoff_local M m Set.univ)

private theorem ae_preimage_cutoffSampleLaw
    (M : ABKModel 2) {s t : Set (ShellSeq 2)}
    (hst : s =ᵐ[M.P.toMeasure] t) :
    (Subtype.val : Cutoff.CutoffSample 2 → ShellSeq 2) ⁻¹' s =ᵐ[
      (Cutoff.cutoffSampleLaw M).toMeasure]
      (Subtype.val : Cutoff.CutoffSample 2 → ShellSeq 2) ⁻¹' t := by
  rw [← Cutoff.map_cutoffSampleLaw_val M] at hst
  exact (Measure.tendsto_ae_map measurable_subtype_coe.aemeasurable).eventually hst

private theorem measure_preimage_cutoffSampleLaw
    (M : ABKModel 2) {s : Set (ShellSeq 2)} (hs : MeasurableSet s) :
    (Cutoff.cutoffSampleLaw M).toMeasure
      ((Subtype.val : Cutoff.CutoffSample 2 → ShellSeq 2) ⁻¹' s) =
      M.P.toMeasure s := by
  rw [← Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable hs,
    Cutoff.map_cutoffSampleLaw_val]

private theorem indep_cutoffSample_local_freshSigma
    (M : ABKModel 2) (m : ℤ) :
    Indep (Cutoff.cutoffSampleLocalSigma M m Set.univ)
      ((Cutoff.shellIndexSigma ({m + 1} : Set ℤ)).comap Subtype.val)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hindep := Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_of_disjoint
    M (Set.disjoint_left.mpr fun k hk hk' => by
      change k ≤ m at hk
      change k = m + 1 at hk'
      omega) Set.univ
  rw [Indep_iff]
  intro s t hs ht
  rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨s', hs', rfl⟩
  rcases MeasurableSpace.measurableSet_comap.mp ht with ⟨t', ht', rfl⟩
  obtain ⟨s0, hs0, hs'0⟩ := hs'
  have hs0borel : MeasurableSet s0 := Cutoff.lowerShellLocalSigma_le_borel m Set.univ s0 hs0
  have htBorel : MeasurableSet t' :=
    (Cutoff.shellIndexSigma_le_borel ({m + 1} : Set ℤ)) t' ht'
  have hsCut := ae_preimage_cutoffSampleLaw M hs'0
  have hstCut : (Subtype.val : Cutoff.CutoffSample 2 → ShellSeq 2) ⁻¹' (s' ∩ t') =ᵐ[
      (Cutoff.cutoffSampleLaw M).toMeasure]
      (Subtype.val : Cutoff.CutoffSample 2 → ShellSeq 2) ⁻¹' (s0 ∩ t') := by
    simpa only [Set.preimage_inter] using hsCut.inter Filter.EventuallyEq.rfl
  rw [← Set.preimage_inter]
  rw [measure_congr hstCut, measure_congr hsCut,
    measure_preimage_cutoffSampleLaw M (hs0borel.inter htBorel),
    measure_preimage_cutoffSampleLaw M hs0borel,
    measure_preimage_cutoffSampleLaw M htBorel]
  exact (Indep_iff _ _ M.P.toMeasure).mp hindep s0 t'
    ⟨s0, hs0, Filter.EventuallyEq.rfl⟩ ht'

/-- The completed cutoff coefficient and its next shell are independent. -/
theorem indepFun_coefficientCutoff_freshShell
    (M : ABKModel 2) (m : ℤ) :
    IndepFun (Cutoff.coefficientCutoff M.nu m)
      (fun ω : Cutoff.CutoffSample 2 => ω.1 (m + 1))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply (IndepFun_iff_Indep _ _ _).mpr
  exact ProbabilityTheory.indep_of_indep_of_le_right
    (ProbabilityTheory.indep_of_indep_of_le_left
      (indep_cutoffSample_local_freshSigma M m)
      (measurable_coefficientCutoff_local_field M m).comap_le)
    ((Cutoff.measurable_shellCoordinate_shellIndexSigma
      (I := ({m + 1} : Set ℤ)) (k := m + 1) (by simp)).comp
      (Measurable.of_comap_le le_rfl)).comap_le

/-- The old coefficient and fresh shell have the product of their marginals.
The first marginal is the law of the older coefficient cutoff, and the second
is the scaled zero-shell law at level `m + 1`. -/
theorem map_pair_coefficientCutoff_freshShell
    (M : ABKModel 2) (m : ℤ) :
    Measure.map (fun ω : Cutoff.CutoffSample 2 =>
        (Cutoff.coefficientCutoff M.nu m ω, ω.1 (m + 1)))
      (Cutoff.cutoffSampleLaw M).toMeasure =
      (Measure.map (Cutoff.coefficientCutoff M.nu m)
        (Cutoff.cutoffSampleLaw M).toMeasure).prod
        (Measure.map (ShellField.triadicScale M.gamma (m + 1))
          (ShellField.zeroShellLaw M.P).toMeasure) := by
  calc
    _ = (Measure.map (Cutoff.coefficientCutoff M.nu m)
          (Cutoff.cutoffSampleLaw M).toMeasure).prod
        (Measure.map (fun ω : Cutoff.CutoffSample 2 => ω.1 (m + 1))
          (Cutoff.cutoffSampleLaw M).toMeasure) :=
      (indepFun_coefficientCutoff_freshShell M m).map_prod_eq_prod_map_map
        (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable
        ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe).aemeasurable
    _ = _ := by rw [map_freshShell_eq_scaledZeroShellLaw]

/-- The older coefficient with one deterministically scaled fresh shell
inserted. This is only a coefficient field; it carries no law or scalar
interpretation. -/
noncomputable def partialInsertedCoefficient (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : RegCoeffField 2 :=
  Cutoff.coefficientCutoff M.nu m ω +
    Real.sqrt t • ShellField.forgetShell (ω.1 (m + 1))

/-- Entry bound for a partial fresh-shell insertion on an origin cube. -/
noncomputable def partialInsertedEntryBound (M : ABKModel 2) (ell m : ℤ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  M.nu + Cutoff.cutoffLocalControl ell m ω +
    localCubeControl ell (ω.1 (m + 1))

private theorem symmPart_add_local (A B : Mat 2) :
    Homogenization.symmPart (A + B) =
      Homogenization.symmPart A + Homogenization.symmPart B := by
  ext i j
  simp only [Homogenization.symmPart, Matrix.add_apply]
  ring

private theorem symmPart_smul_local (c : ℝ) (A : Mat 2) :
    Homogenization.symmPart (c • A) = c • Homogenization.symmPart A := by
  ext i j
  simp only [Homogenization.symmPart, Matrix.smul_apply]
  ring

private theorem symmPart_forgetShell_eq_zero (j : ShellField 2) (x : Vec 2) :
    Homogenization.symmPart (ShellField.forgetShell j x) = 0 := by
  ext i k
  change (j x i k + j x k i) / 2 = 0
  rw [j.skew_entry x i k]
  ring

private theorem symmPart_partialInsertedCoefficient
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) :
    Homogenization.symmPart (partialInsertedCoefficient M m t ω x) =
      M.nu • (1 : Mat 2) := by
  change Homogenization.symmPart
    (Cutoff.coefficientCutoff M.nu m ω x +
      Real.sqrt t • ShellField.forgetShell (ω.1 (m + 1)) x) = _
  rw [symmPart_add_local, symmPart_smul_local,
    symmPart_forgetShell_eq_zero, smul_zero, add_zero,
    Cutoff.symmPart_coefficientCutoff]

/-- For every `0 ≤ t ≤ 1`, the partial insertion is a locally bounded
elliptic coefficient on every measurable subset of a bounded origin cube.
The bound depends only on the old cutoff control and the fresh-shell local
control. -/
theorem partialInsertedCoefficient_isEllipticFieldOn
    (M : ABKModel 2) (ell m : ℤ) (ω : Cutoff.CutoffSample 2) {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ 1) {U : Set (Vec 2)} (hU : MeasurableSet U)
    (hUcube : U ⊆ openCubeSet (originCube 2 ell)) :
    IsEllipticFieldOn M.nu
      (((2 : ℝ) * (2 : ℝ) * (partialInsertedEntryBound M ell m ω) ^ 2 +
        M.nu ^ 2) / M.nu) U (partialInsertedCoefficient M m t ω) := by
  refine ⟨?_, ?_⟩
  · refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    exact ((partialInsertedCoefficient M m t ω).entry_measurable i j).ite
      hU measurable_const
  · intro x hx
    apply Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
      (symmPart_partialInsertedCoefficient M m t ω x)
    intro i j
    have hbase := Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le
      ell m ω (hUcube hx) i j
    have hfresh := abs_entry_le_localCubeControl ell (ω.1 (m + 1))
      (hUcube hx) i j
    have hroot0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    have hroot1 : Real.sqrt t ≤ 1 := by
      calc
        Real.sqrt t ≤ Real.sqrt 1 := Real.sqrt_le_sqrt ht.2
        _ = 1 := Real.sqrt_one
    have hscaled : Real.sqrt t * |ω.1 (m + 1) x i j| ≤
        localCubeControl ell (ω.1 (m + 1)) := by
      calc
        Real.sqrt t * |ω.1 (m + 1) x i j| ≤
            1 * |ω.1 (m + 1) x i j| :=
          mul_le_mul_of_nonneg_right hroot1 (abs_nonneg _)
        _ ≤ localCubeControl ell (ω.1 (m + 1)) := by simpa using hfresh
    change |Cutoff.coefficientCutoff M.nu m ω x i j +
      Real.sqrt t * ω.1 (m + 1) x i j| ≤ partialInsertedEntryBound M ell m ω
    calc
      |Cutoff.coefficientCutoff M.nu m ω x i j +
          Real.sqrt t * ω.1 (m + 1) x i j| ≤
          |Cutoff.coefficientCutoff M.nu m ω x i j| +
            |Real.sqrt t * ω.1 (m + 1) x i j| := abs_add_le _ _
      _ = |Cutoff.coefficientCutoff M.nu m ω x i j| +
          Real.sqrt t * |ω.1 (m + 1) x i j| := by
            rw [abs_mul, abs_of_nonneg hroot0]
      _ ≤ M.nu + Cutoff.cutoffLocalControl ell m ω +
          localCubeControl ell (ω.1 (m + 1)) := add_le_add hbase hscaled
      _ = partialInsertedEntryBound M ell m ω := rfl

end ASDExplicitGamma.Model

end
