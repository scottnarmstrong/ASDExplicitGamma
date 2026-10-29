module

public import ASDExplicitGamma.Inverse.RootMatrixSeries
public import ASDExplicitGamma.Inverse.RootDensitySeries

/-! Exact positive-series decomposition, with almost-sure convergence proved
before any response comparison. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

theorem root_density_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : 0 ≤ rootDensityTerm M Q r hk ω := by
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hS : 0 ≤ planarGradientCharge 40 := by unfold planarGradientCharge; positivity
  have hc : 0 ≤ rootEdelta r*rootResponseEnvelope (6*rootTau r) := by
    unfold rootEdelta rootResponseEnvelope
    positivity
  apply mul_nonneg hc
  apply mul_nonneg (mul_nonneg (by linarith only [hS]) (by positivity))
  exact Finset.sum_nonneg (fun e _ => reset_density_excess_nonneg M Q (rootH0 r) (rootTau r)
    (waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω)

/-- Exact extended nonnegative summand identity; no response or moment
subtraction defines the error. -/
theorem root_error_term_ofReal (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (rootMatrixTerm M Q r hk ω+rootDensityTerm M Q r hk ω) =
      ENNReal.ofReal (rootEdelta r)*
        (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)))*
          (ENNReal.ofReal (rootMatrixPositiveError M Q r hk ω)+
            ENNReal.ofReal (rootResponseEnvelope (6*rootTau r)*(planarGradientCharge 40+1))*
              ∑ e : Fin 3, ENNReal.ofReal (resetDensityExcess M Q (rootH0 r) (rootTau r)
                (waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω))) := by
  let Y := fun e : Fin 3 => resetDensityExcess M Q (rootH0 r) (rootTau r)
    (waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω
  have hY (e : Fin 3) : 0 ≤ Y e := reset_density_excess_nonneg _ _ _ _ _ _ _ _ _ _ _
  have hE : 0 ≤ rootEdelta r := by unfold rootEdelta; positivity
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hS : 0 ≤ planarGradientCharge 40 := by unfold planarGradientCharge; positivity
  have hC : 0 ≤ rootResponseEnvelope (6*rootTau r)*(planarGradientCharge 40+1) := by
    unfold rootResponseEnvelope
    positivity
  have hm : 0 ≤ rootMatrixPositiveError M Q r hk ω := le_max_left 0 _
  have he : rootMatrixTerm M Q r hk ω+rootDensityTerm M Q r hk ω =
      rootEdelta r*((3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ))*
        (rootMatrixPositiveError M Q r hk ω+
          (rootResponseEnvelope (6*rootTau r)*(planarGradientCharge 40+1))*∑ e, Y e)) := by
    unfold rootMatrixTerm rootDensityTerm resetDensityTerm2
    dsimp only [Y]
    ring
  rw [he,ENNReal.ofReal_mul hE,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add hm (mul_nonneg hC (Finset.sum_nonneg (fun e _ => hY e))),
    ENNReal.ofReal_mul hC,ENNReal.ofReal_sum_of_nonneg (fun e _ => hY e)]

/-- The literal root error equals the sum of its actual nonnegative matrix
and density series whenever those series converge. -/
theorem positive_root_error_eq_parts (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (ω : Cutoff.CutoffSample 2) (hm : Summable (fun hk => rootMatrixTerm M Q r hk ω))
    (hd : Summable (fun hk => rootDensityTerm M Q r hk ω)) :
    positiveRootError M Q r ω=ENNReal.ofReal
      ((∑' hk, rootMatrixTerm M Q r hk ω)+(∑' hk, rootDensityTerm M Q r hk ω)) := by
  rw [← hm.tsum_add hd,ENNReal.ofReal_tsum_of_nonneg
    (fun hk => add_nonneg (root_matrix_term_nonneg M Q r hk ω) (root_density_term_nonneg M Q r hk ω)) (hm.add hd)]
  simp only [root_error_term_ofReal,ENNReal.tsum_mul_left,positiveRootError]

end
end ASDExplicitGamma.Inverse
