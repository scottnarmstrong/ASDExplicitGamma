module

public import ASDExplicitGamma.Cold.NativeLocalIntegralSigma
public import Algsuperdiff.Section3.Cutoff.ShellRange

/-! # Sharp coordinate-range independence at every actual shell level -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open scoped Pointwise
namespace ASDExplicitGamma.Cold

/-- Coordinate separation by 3^m contracts to separation by one at every shell n<=m. -/
theorem cold_scaled_coordinate_separation {m n : ℤ} (hnm : n ≤ m) {U V : Set (Vec 2)}
    (hsep : ∀ x ∈ U, ∀ y ∈ V, ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k|) :
    ∀ x ∈ ((3:ℝ)^n)⁻¹ • U, ∀ y ∈ ((3:ℝ)^n)⁻¹ • V,
      ∃ k : Fin 2, 1 ≤ |(x-y) k| := by
  rintro x ⟨x0,hx0,rfl⟩ y ⟨y0,hy0,rfl⟩
  obtain ⟨k,hk⟩ := hsep x0 hx0 y0 hy0
  have hscale : (0:ℝ) < (3:ℝ)^n := zpow_pos (by norm_num) _
  have hpow : (3:ℝ)^n ≤ (3:ℝ)^m := zpow_le_zpow_right₀ (by norm_num) hnm
  have hh := mul_le_mul_of_nonneg_left (hpow.trans hk) (inv_nonneg.mpr hscale.le)
  rw [inv_mul_cancel₀ hscale.ne'] at hh
  refine ⟨k,?_⟩
  have he : (((3:ℝ)^n)⁻¹ • x0-((3:ℝ)^n)⁻¹ • y0) k = ((3:ℝ)^n)⁻¹*(x0-y0) k := by
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,abs_mul,abs_of_nonneg (inv_nonneg.mpr hscale.le)]
  exact hh

/-- Every literal shell n<=m has sharp coordinate-local range 3^m under the frozen q3 law. -/
theorem cold_indep_shellLocal (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m n : ℤ) (hnm : n ≤ m) (U V : Set (Vec 2)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ x ∈ U, ∀ y ∈ V, ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k|) :
    Indep ((ShellField.lihLocalSigma U).comap (fun ω : ℤ → ShellField 2 => ω n))
      ((ShellField.lihLocalSigma V).comap (fun ω : ℤ → ShellField 2 => ω n)) M.P.toMeasure := by
  let r : ℝ := ((3:ℝ)^n)⁻¹
  have hr : r ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by norm_num))
  have hzero := cold_zeroShell_localSigma_pair M h hM (hU.const_smul_of_ne_zero hr)
    (hV.const_smul_of_ne_zero hr) (cold_scaled_coordinate_separation hnm hsep)
  have hcomap : Indep ((ShellField.lihLocalSigma U).comap (ShellField.triadicScale M.gamma n))
      ((ShellField.lihLocalSigma V).comap (ShellField.triadicScale M.gamma n))
      (ShellField.zeroShellLaw M.P).toMeasure :=
    indep_of_indep_of_le_right (indep_of_indep_of_le_left hzero
      (Cutoff.measurable_triadicScale_local M.gamma n U).comap_le)
      (Cutoff.measurable_triadicScale_local M.gamma n V).comap_le
  have hscaled := (Algsuperdiff.Probability.indep_comap_iff_indep_map
    (ShellField.measurable_triadicScale M.gamma n).aemeasurable
    (ShellField.lihLocalSigma_le_borel U) (ShellField.lihLocalSigma_le_borel V)).mp hcomap
  have hscale := congrArg ProbabilityMeasure.toMeasure (M.shellPrefix.marginal_scaling n)
  change (ShellField.shellMarginalLaw M.P n).toMeasure =
    Measure.map (ShellField.triadicScale M.gamma n) (ShellField.zeroShellLaw M.P).toMeasure at hscale
  rw [← hscale] at hscaled
  exact (Algsuperdiff.Probability.indep_comap_iff_indep_map (ShellField.measurable_shellCoordinate n).aemeasurable
    (ShellField.lihLocalSigma_le_borel U) (ShellField.lihLocalSigma_le_borel V)).mpr
    (by simpa [ShellField.shellMarginalLaw] using hscaled)

end ASDExplicitGamma.Cold
