module

public import ASDExplicitGamma.Inverse.DescendantResponse

/-! A linear actual-cube cap and the sharp planar raw-history budget. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- Every actual old cube obeys the safe linear pure-flux cap in its true
completed-label frame, before any history averaging. -/
theorem old_pure_flux_linear_cap (M : ABKModel 2) (Q : TriadicCube 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) (v : Vec 2) :
    (Annealed.sigmaBar M n:ℝ)*dotProduct v ((coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu n ω).toFun).lowerRight.mulVec v) ≤
        2*(1+historyOperatorDefect M n Q ω)*dotProduct v v := by
  have hσ : 0 ≤ (Annealed.sigmaBar M n:ℝ) := (Annealed.sigmaBar_characterization M n).1.le
  have hv : 0 ≤ dotProduct v v := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
  have hn := (le_abs_self _).trans (clipped_quadratic_abs_le_norm
    (coarseBlockMatrix (cubeSet Q) (Cutoff.coefficientCutoff M.nu n ω).toFun).lowerRight v)
  have h1 := mul_le_mul_of_nonneg_left hn hσ
  have h2 := mul_le_mul_of_nonneg_right (actual_framed_lower_right_norm_le_defect M n Q ω) hv
  exact h1.trans (by simpa only [mul_assoc,Book.Ch02.matrixNorm] using h2)

/-- The good parent supplies the actual later response's safe linear cap on
every contained descendant, all in the parent's true old frame. -/
theorem good_parent_descendant_linear_cap (M : ABKModel 2)
    {Q R : TriadicCube 2} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) (r : RootRow)
    (m J : ℤ) (hn : Q.scale+40 ≤ m) (hm : m ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M (rootTau r) (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) Q)
    (v : Vec 2) :
    (Annealed.sigmaBar M (Q.scale+40):ℝ)*
      dotProduct v ((coarseBlockMatrix (cubeSet R) (attenuatedCoefficient M m J weights ω)).lowerRight.mulVec v) ≤
        rootEdelta r*(2*(1+historyOperatorDefect M (Q.scale+40) R ω)*dotProduct v v) := by
  have hh := mul_le_mul_of_nonneg_left
    (good_parent_descendant_pure_flux_response M hR r m J hn hm weights hw ω hgood v)
    (Annealed.sigmaBar_characterization M (Q.scale+40)).1.le
  have he : 0 ≤ rootEdelta r := (Real.exp_pos _).le
  have hb := mul_le_mul_of_nonneg_left (old_pure_flux_linear_cap M R (Q.scale+40) ω v) he
  exact hh.trans (by simpa only [mul_left_comm] using hb)

/-- The sharper planar raw-history factor 2 sqrt(3) leaves enough margin to
use the safe linear cube cap and still retain exactly the source g(6 tau).
All four fixed source rows have tau>=1. -/
theorem planar_linear_average_le_envelope (τ : ℝ) (hτ : 1 ≤ τ) :
    2*(1+2*Real.sqrt 3*τ) ≤ rootResponseEnvelope (6*τ) := by
  have hτ0 : 0 ≤ τ := le_trans (by norm_num) hτ
  have hs3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hs30 := Real.sqrt_nonneg (3:ℝ)
  have hs32 : Real.sqrt 3 ≤ 2 := by nlinarith only [hs3,hs30]
  have hs := Real.sq_sqrt (show 0 ≤ (6*τ)*(6*τ+2) by positivity)
  have hs0 := Real.sqrt_nonneg ((6*τ)*(6*τ+2))
  have hslo : 6*τ ≤ Real.sqrt ((6*τ)*(6*τ+2)) := by nlinarith only [hs,hτ0,hs0]
  have hh := mul_le_mul_of_nonneg_right hs32 hτ0
  unfold rootResponseEnvelope
  nlinarith only [hslo,hh,hτ]

end
end ASDExplicitGamma.Inverse
