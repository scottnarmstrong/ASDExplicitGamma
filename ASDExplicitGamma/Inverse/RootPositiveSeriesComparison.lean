module

public import ASDExplicitGamma.Inverse.LayerPositiveEnergy
public import ASDExplicitGamma.Inverse.RootLayerProfile

/-! Exact Li summation and enlargement to the complete positive source error. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The positive fixed-height layer majorant is bounded by exactly Li times
the height clock plus the complete source E_l. No finiteness or response-norm
premise is needed, and the same complete positive error serves every height. -/
theorem root_positive_layer_series_le (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (r : RootRow) (H : ℕ) (hH : rootH0 r ≤ H) (ω : Cutoff.CutoffSample 2) :
    let w := fun k : ℕ => (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) k:ℝ))
    let K := rootMeanCap r+3*(planarGradientCharge 40+1)*rootResponseEnvelope (6*rootTau r)*
      densityMomentBudget (rootQ r) 2 (rootMomentCutoff r)
    ENNReal.ofReal (rootEdelta r)*∑' k : ℕ,
      (ENNReal.ofReal (w k*K*bankLayerWeight k)+
        ENNReal.ofReal (w k)*(ENNReal.ofReal (rootMatrixPositiveError M Q r (H-rootH0 r,k) ω)+
          ENNReal.ofReal (rootResponseEnvelope (6*rootTau r)*(planarGradientCharge 40+1))*
            ∑ e : Fin 3, ENNReal.ofReal (resetDensityExcess M Q (rootH0 r) (rootTau r)
              (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r)
                2 (H-rootH0 r,k) e ω))) ≤
      ENNReal.ofReal (rootLi M.gamma r)*ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((H:ℝ)-38)))+
        positiveRootError M Q r ω := by
  let w := fun k : ℕ => (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) (H-rootH0 r) k:ℝ))
  let K := rootMeanCap r+3*(planarGradientCharge 40+1)*rootResponseEnvelope (6*rootTau r)*
    densityMomentBudget (rootQ r) 2 (rootMomentCutoff r)
  let f := fun hk : ℕ × ℕ => ENNReal.ofReal
    ((3:ℝ)^(2*M.gamma*(localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)))*
      (ENNReal.ofReal (rootMatrixPositiveError M Q r hk ω)+
        ENNReal.ofReal (rootResponseEnvelope (6*rootTau r)*(planarGradientCharge 40+1))*
          ∑ e : Fin 3, ENNReal.ofReal (resetDensityExcess M Q (rootH0 r) (rootTau r)
            (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω))
  have hpars := root_row_density_parameters r
  have hq0 : 0 ≤ rootQ r := (Real.exp_pos _).le.trans hpars.2.2.1
  have ht := density_moment_budget_nonneg _ hq0 2 _ hpars.2.2.2.1
  have hτ : 0 ≤ rootTau r := hpars.2.1.le
  have hs : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  have hg0 : 0 ≤ rootResponseEnvelope (6*rootTau r) := by unfold rootResponseEnvelope; positivity
  have hb : 0 ≤ rootMeanCap r := by cases r <;> norm_num [rootMeanCap]
  have hK : 0 ≤ K := add_nonneg hb
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) hg0) ht)
  have hE : 0 ≤ rootEdelta r := (Real.exp_pos _).le
  have hLi : 0 ≤ rootLi M.gamma r := by
    change 0 ≤ rootEdelta r*K*rootLayerSum (2*M.gamma)
    exact mul_nonneg (mul_nonneg hE hK) (tsum_nonneg (fun k => mul_nonneg (bankLayerWeight_nonneg k) (by positivity)))
  have hbase : HasSum (fun k : ℕ => rootEdelta r*(w k*K*bankLayerWeight k))
      (rootLi M.gamma r*(3:ℝ)^(2*M.gamma*((H:ℝ)-38))) := by
    have hh := (root_clocked_layer_weights_hasSum M.gamma hg r H hH).mul_left (rootEdelta r*K)
    convert hh using 1
    · funext k
      dsimp only [w]
      ring
    · unfold rootLi
      dsimp only [K]
      ring
  have hmean : ENNReal.ofReal (rootEdelta r)*(∑' k : ℕ, ENNReal.ofReal (w k*K*bankLayerWeight k))=
      ENNReal.ofReal (rootLi M.gamma r)*ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((H:ℝ)-38))) := by
    rw [← ENNReal.tsum_mul_left]
    simp_rw [← ENNReal.ofReal_mul hE]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg hE
      (mul_nonneg (mul_nonneg (by dsimp only [w]; positivity) hK) (bankLayerWeight_nonneg k))) hbase.summable,
      hbase.tsum_eq,ENNReal.ofReal_mul hLi]
  have herr : ENNReal.ofReal (rootEdelta r)*(∑' k : ℕ, f (H-rootH0 r,k)) ≤
      positiveRootError M Q r ω := by
    have hi : Function.Injective (fun k : ℕ => (H-rootH0 r,k)) := by
      intro k l he
      exact congrArg Prod.snd he
    exact mul_le_mul_right (ENNReal.tsum_comp_le_tsum_of_injective hi f) _
  dsimp only
  change ENNReal.ofReal (rootEdelta r)*(∑' k : ℕ,
    (ENNReal.ofReal (w k*K*bankLayerWeight k)+f (H-rootH0 r,k))) ≤ _
  rw [ENNReal.tsum_add,mul_add,hmean]
  exact add_le_add_right herr _

end
end ASDExplicitGamma.Inverse
