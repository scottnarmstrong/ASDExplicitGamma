module

public import ASDExplicitGamma.Inverse.RestrictionReset
public import ASDExplicitGamma.Inverse.RootDefinitions
public import ASDExplicitGamma.Inverse.FullResponseTrace
public import ASDExplicitGamma.Scalar.StructuralContinuity
public import ASDExplicitGamma.Variational.TraceDefect

/-! Elementary order-band bounds used by the all-real-order assembly. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model
open ASDExplicitGamma.Variational
open scoped Matrix.Norms.Elementwise

noncomputable section

/-- The actual trace observable in the full-law reference frame. The base
cutoff is the protected old label and `N` is the terminal shell label, while
`weights` records the source's deterministic attenuation. -/
def rootTraceObservable (M : ABKModel 2) (Q : TriadicCube 2)
    (m N K₀ : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M K₀ : ℝ)
    (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m N weights ω))))

/-- The actual lower-right inverse block in the same full-law reference
frame used by `rootTraceObservable`. -/
def rootInverseObservable (M : ABKModel 2) (Q : TriadicCube 2)
    (m N K₀ : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (Annealed.sigmaBar M K₀ : ℝ) * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
    (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m N weights ω)).lowerRight‖

/-- The trace observable is four plus the actual trace defect in the same
reference frame. -/
theorem root_trace_observable_eq_trace_defect (M : ABKModel 2)
    (Q : TriadicCube 2) (m N K₀ : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    rootTraceObservable M Q m N K₀ weights ω =
      traceDefect (cubeSet Q) (attenuatedCoefficient M m N weights ω)
        (Annealed.sigmaBar M K₀ : ℝ) + 4 := by
  rw [rootTraceObservable, traceDefect_eq_full_framedTrace]
  ring

/-- Changing from the old cutoff frame to the source reference frame multiplies
the inverse observable by exactly the ratio of the two true scalars. -/
theorem root_inverse_observable_eq_reference_ratio (M : ABKModel 2)
    (Q : TriadicCube 2) (m N K₀ : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    rootInverseObservable M Q m N K₀ weights ω =
      ((Annealed.sigmaBar M K₀ : ℝ) / (Annealed.sigmaBar M m : ℝ)) *
        rootInverseResponse M Q m N weights ω := by
  have hσm : (Annealed.sigmaBar M m : ℝ) ≠ 0 :=
    (Annealed.sigmaBar_characterization M m).1.ne'
  unfold rootInverseObservable rootInverseResponse
  field_simp [hσm]

/-- True-frame structural continuity controls the ratio between any two
integer cutoff labels by their absolute label gap. -/
theorem true_frame_ratio_le (M : ABKModel 2) (n m : ℤ) :
    (Annealed.sigmaBar M n : ℝ) / (Annealed.sigmaBar M m : ℝ) ≤
      (3 : ℝ) ^ (2 * M.gamma * |((n - m : ℤ) : ℝ)|) := by
  have hσn : 0 < (Annealed.sigmaBar M n : ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  have hσm : 0 < (Annealed.sigmaBar M m : ℝ) :=
    (Annealed.sigmaBar_characterization M m).1
  by_cases hmn : m ≤ n
  · have hcont := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity
      M m (n - m) (by omega)).2
    rw [show m + (n - m) = n by omega] at hcont
    have hgap : (0 : ℝ) ≤ ((n - m : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hmn
    rw [abs_of_nonneg hgap]
    exact hcont
  · have hnm : n ≤ m := by omega
    have hcont := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity
      M n (m - n) (by omega)
    rw [show n + (m - n) = m by omega] at hcont
    have hmono : (Annealed.sigmaBar M n : ℝ) ≤ (Annealed.sigmaBar M m : ℝ) := by
      have hmul := (le_div_iff₀ hσn).mp hcont.1
      simpa only [one_mul] using hmul
    have hratio :
        (Annealed.sigmaBar M n : ℝ) / (Annealed.sigmaBar M m : ℝ) ≤ 1 :=
      (div_le_one hσm).2 hmono
    have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    have hexp : 0 ≤ 2 * M.gamma * |((n - m : ℤ) : ℝ)| :=
      mul_nonneg (mul_nonneg (by norm_num) hγ) (abs_nonneg _)
    exact hratio.trans (Real.one_le_rpow (by norm_num) hexp)

theorem order_band_scale (p : ℝ) :
    p ≤ 64 * (3 : ℝ) ^ orderBand p := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hceil :
      Real.log (max 1 (p / 64)) / Real.log 3 ≤ (orderBand p : ℝ) := by
    unfold orderBand
    exact_mod_cast (Nat.le_ceil (Real.log (max 1 (p / 64)) / Real.log 3))
  have hlog :
      Real.log (max 1 (p / 64)) ≤ (orderBand p : ℝ) * Real.log 3 := by
    exact (div_le_iff₀ hlog3).mp hceil
  have hmax :
      max 1 (p / 64) ≤ Real.exp ((orderBand p : ℝ) * Real.log 3) :=
    (Real.log_le_iff_le_exp (by positivity)).mp hlog
  have hexp :
      Real.exp ((orderBand p : ℝ) * Real.log 3) =
        (3 : ℝ) ^ orderBand p := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hpdiv : p / 64 ≤ (3 : ℝ) ^ orderBand p := by
    exact (le_max_right 1 (p / 64)).trans (hexp ▸ hmax)
  have h64 : (0 : ℝ) < 64 := by norm_num
  calc
    p ≤ (3 : ℝ) ^ orderBand p * 64 := (div_le_iff₀ h64).mp hpdiv
    _ = 64 * (3 : ℝ) ^ orderBand p := by ring

end

end ASDExplicitGamma.Inverse
