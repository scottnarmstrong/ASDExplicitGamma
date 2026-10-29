module

public import ASDExplicitGamma.Gaussian.RealizationMeasurability
public import Algsuperdiff.Section3.Cutoff.HighMoments
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# The completed older shell field

On a compact set contained in a fixed origin cube, Superdiffusion's local
cutoff control dominates the sum of the scalar shell sup norms.  Its proved
Gaussian-tail moment bound therefore supplies every finite moment, and the
same summable majorant gives almost-sure and `L^p` convergence of the older
field series.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ASDExplicitGamma.Gaussian

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Homogenization

/-- The scalar restriction of the shells at and below `m`, summed by their
supremum norms on a compact set. -/
noncomputable def olderShellSupNormSum (K : Set (Vec 2)) [CompactSpace K]
    (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' r : ℕ, ‖shellFieldScalarRestriction K (ω.1 (m - (r : ℤ)))‖

/-- The finite older-shell field through distance `N-1` below `m`. -/
def olderFieldPartial (K : Set (Vec 2)) [CompactSpace K] (m : ℤ) (N : ℕ)
    (ω : Cutoff.CutoffSample 2) : C(K, ℝ) :=
  ∑ r ∈ Finset.range N, shellFieldScalarRestriction K (ω.1 (m - (r : ℤ)))

/-- The completed older scalar field on a compact set. -/
noncomputable def olderField (K : Set (Vec 2)) [CompactSpace K]
    (m : ℤ) (ω : Cutoff.CutoffSample 2) : C(K, ℝ) :=
  ∑' r : ℕ, shellFieldScalarRestriction K (ω.1 (m - (r : ℤ)))

private theorem shellRestriction_norm_le_localCubeControl
    (K : Set (Vec 2)) [CompactSpace K] (ell : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (j : ShellField 2) :
    ‖shellFieldScalarRestriction K j‖ ≤ localCubeControl ell j := by
  rw [ContinuousMap.norm_le _ (localCubeControl_nonneg ell j)]
  intro x
  rw [Real.norm_eq_abs]
  change |j.1.1 x.1 1 0| ≤ localCubeControl ell j
  exact abs_entry_le_localCubeControl ell j (hK x.2) 1 0

private theorem summable_olderShellRestrictions
    (K : Set (Vec 2)) [CompactSpace K] (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) :
    Summable (fun r : ℕ =>
      ‖shellFieldScalarRestriction K (ω.1 (m - (r : ℤ)))‖) := by
  apply Summable.of_norm_bounded (summable_cutoffLocalControl ell m ω)
  intro r
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact shellRestriction_norm_le_localCubeControl K ell hK
    (ω.1 (m - (r : ℤ)))

private theorem summable_olderShellFields
    (K : Set (Vec 2)) [CompactSpace K] (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) :
    Summable (fun r : ℕ =>
      shellFieldScalarRestriction K (ω.1 (m - (r : ℤ)))) := by
  apply Summable.of_norm_bounded (summable_cutoffLocalControl ell m ω)
  intro r
  exact shellRestriction_norm_le_localCubeControl K ell hK
    (ω.1 (m - (r : ℤ)))

private theorem olderShellSupNormSum_le_localControl
    (K : Set (Vec 2)) [CompactSpace K] (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) :
    olderShellSupNormSum K m ω ≤ cutoffLocalControl ell m ω := by
  exact (summable_olderShellRestrictions K ell m hK ω).tsum_le_tsum
    (fun r => shellRestriction_norm_le_localCubeControl K ell hK
      (ω.1 (m - (r : ℤ))))
    (summable_cutoffLocalControl ell m ω)

/-- The shell supremum majorant is measurable. -/
theorem measurable_olderShellSupNormSum
    (K : Set (Vec 2)) [CompactSpace K] (m : ℤ) :
    Measurable (olderShellSupNormSum K m) := by
  change Measurable (fun ω : Cutoff.CutoffSample 2 =>
    ∑' r : ℕ, ‖shellFieldScalarRestriction K (ω.1 (m - (r : ℤ)))‖)
  have hf : ∀ r : ℕ, Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ‖shellFieldScalarRestriction K (ω.1 (m - (r : ℤ)))‖) := by
    intro r
    have hcoord : Measurable (fun ω : Cutoff.CutoffSample 2 =>
        ω.1 (m - (r : ℤ))) :=
      (measurable_pi_apply (m - (r : ℤ))).comp measurable_subtype_coe
    exact (continuous_norm.measurable.comp
      (measurable_shellFieldScalarRestriction K)).comp hcoord
  exact Measurable.tsum hf

/-- The finite older-shell fields converge uniformly on the compact set for
every sample in the cutoff carrier. -/
theorem olderFieldPartial_tendsto
    (K : Set (Vec 2)) [CompactSpace K] (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) :
    Tendsto (fun N => olderFieldPartial K m N ω) atTop
      (𝓝 (olderField K m ω)) := by
  have hs := summable_olderShellFields K ell m hK ω
  simpa only [olderFieldPartial, olderField] using hs.hasSum.tendsto_sum_nat

/-- The finite older-shell field is measurable as a map into `C(K, ℝ)`. -/
theorem measurable_olderFieldPartial
    (K : Set (Vec 2)) [CompactSpace K] (m : ℤ) (N : ℕ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => olderFieldPartial K m N ω) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro x
  simp only [olderFieldPartial, ContinuousMap.coe_sum, Finset.sum_apply]
  apply Finset.measurable_sum
  intro r hr
  have hcoord : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ω.1 (m - (r : ℤ))) :=
    (measurable_pi_apply (m - (r : ℤ))).comp measurable_subtype_coe
  exact (ContinuousMap.measurable_eval x).comp
    ((measurable_shellFieldScalarRestriction K).comp hcoord)

/-- The completed older field is measurable, as the pointwise limit of its
measurable finite partial fields. -/
theorem measurable_olderField
    (K : Set (Vec 2)) [CompactSpace K] (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell)) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => olderField K m ω) := by
  apply measurable_of_tendsto_metrizable
    (f := fun N ω => olderFieldPartial K m N ω)
  · intro N
    exact measurable_olderFieldPartial K m N
  · exact tendsto_pi_nhds.mpr fun ω => olderFieldPartial_tendsto K ell m hK ω

/-- Every finite real moment of the total older-shell supremum is finite. -/
theorem integrable_olderShellSupNormSum_rpow
    (M : ABKModel 2) (K : Set (Vec 2)) [CompactSpace K] (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun ω => olderShellSupNormSum K m ω ^ p)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hMeas : Measurable (olderShellSupNormSum K m) :=
    measurable_olderShellSupNormSum K m
  have hGrowth := hasGammaMomentGrowthWith_cutoffLocalControl M ell m
  have hControl : Integrable (fun ω =>
      |cutoffLocalControl ell m ω| ^ p) μ := (hGrowth hp).1
  have hPowerMeas : Measurable (fun ω => olderShellSupNormSum K m ω ^ p) := by
    fun_prop
  apply hControl.mono' hPowerMeas.aestronglyMeasurable
  filter_upwards with ω
  have hsum_nonneg : 0 ≤ olderShellSupNormSum K m ω :=
    tsum_nonneg fun r => norm_nonneg _
  have hcontrol_nonneg : 0 ≤ cutoffLocalControl ell m ω :=
    cutoffLocalControl_nonneg ell m ω
  have hbound := olderShellSupNormSum_le_localControl K ell m hK ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hsum_nonneg _),
    abs_of_nonneg hcontrol_nonneg]
  exact Real.rpow_le_rpow hsum_nonneg hbound (le_trans (by norm_num) hp)

/-- The total older-shell supremum belongs to every finite `L^p`, `p ≥ 1`.-/
theorem memLp_olderShellSupNormSum
    (M : ABKModel 2) (K : Set (Vec 2)) [CompactSpace K] (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {p : ℝ} (hp : 1 ≤ p) :
    MemLp (olderShellSupNormSum K m) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hMeas : Measurable (olderShellSupNormSum K m) :=
    measurable_olderShellSupNormSum K m
  have hMom : Integrable (fun ω => olderShellSupNormSum K m ω ^ p) μ :=
    integrable_olderShellSupNormSum_rpow M K ell m hK hp
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one hp)).ne'
  have hpTop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hpNonneg : 0 ≤ p := le_trans (by norm_num) hp
  have hSumNonneg (ω : Cutoff.CutoffSample 2) :
      0 ≤ olderShellSupNormSum K m ω :=
    tsum_nonneg fun r => norm_nonneg _
  have hPowNonneg : ∀ ω, 0 ≤ olderShellSupNormSum K m ω ^ p :=
    fun ω => Real.rpow_nonneg (hSumNonneg ω) p
  have hLintegral :
      ∫⁻ ω, ENNReal.ofReal (olderShellSupNormSum K m ω ^ p) ∂μ < ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hMom
      (Filter.Eventually.of_forall hPowNonneg)]
    exact ENNReal.ofReal_lt_top
  have hRpow :
      (fun ω : Cutoff.CutoffSample 2 =>
        ‖olderShellSupNormSum K m ω‖ₑ ^ (ENNReal.ofReal p).toReal) =
      fun ω => ENNReal.ofReal (olderShellSupNormSum K m ω ^ p) := by
    funext ω
    rw [ENNReal.toReal_ofReal hpNonneg]
    rw [Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (hSumNonneg ω)]
    exact ENNReal.ofReal_rpow_of_nonneg (hSumNonneg ω) hpNonneg
  rw [memLp_iff]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hMeas.aestronglyMeasurable]
  rw [hRpow]
  rw [ENNReal.toReal_ofReal hpNonneg]
  simpa only [μ] using ENNReal.rpow_lt_top_of_nonneg
    (one_div_nonneg.mpr (le_of_lt (lt_of_lt_of_le zero_lt_one hp)))
    (ne_of_lt hLintegral)

end ASDExplicitGamma.Gaussian
end
