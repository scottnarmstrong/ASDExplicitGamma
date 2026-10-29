module

public import ASDExplicitGamma.Inverse.RootMatrixConcentration

/-! Source abscissa and positive directional matrix error norm (6.4). -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Exact fine-depth/buffer conversion, before taking any geometric envelope. -/
theorem root_matrix_depth_factor (H0 h k : ℕ) (hH : 38 ≤ H0) :
    (1/3:ℝ)^(k+1+whitneyProfile (H0+h) (k+1))*(3:ℝ)^40 =
      (3:ℝ)^(-((localizationResetAbscissa (H0-38) h k:ℝ)+1)) := by
  let d := k+1+whitneyProfile (H0+h) (k+1)
  let x := localizationResetAbscissa (H0-38) h k
  have hd : (d:ℤ)=(x:ℤ)+41 := by
    have hx := localization_reset_abscissa_source H0 h k hH
    dsimp only [x,d,whitneyProfile,resetDepth] at *
    push_cast at *
    omega
  have he : (1/3:ℝ)^d*(3:ℝ)^40=(3:ℝ)^(-(d:ℤ)+40) := by
    rw [zpow_add₀ (by norm_num : (3:ℝ)≠0),zpow_neg,zpow_natCast,zpow_ofNat,one_div_pow,one_div]
  change (1/3:ℝ)^d*(3:ℝ)^40=(3:ℝ)^(-((x:ℝ)+1))
  rw [he,hd]
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

/-- The source bound for the literal positive largest pure-flux deviation.
No response estimate, finite-energy premise, independence premise or
matrix-moment premise is required. All real orders p>=1 are covered. -/
theorem root_matrix_positive_error_Lp (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (Q : TriadicCube 2) (r : RootRow) (hk : ℕ × ℕ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (rootMatrixPositiveError M Q r hk) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (256*Real.sqrt p*rootResponseEnvelope (rootTau r)*Real.sqrt (bankLayerWeight hk.2)*
        (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1))) := by
  have hh := root_centered_layer_Lp_depth M h hM Q r hk p hp
  have hm := root_matrix_positive_error_measurable M Q r hk
  have hn : eLpNorm (rootMatrixPositiveError M Q r hk) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (rootCenteredLayerMatrix M Q r hk ω)‖) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply eLpNorm_mono_real hm.aestronglyMeasurable
    intro ω
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ rootMatrixPositiveError M Q r hk ω from le_max_left 0 _)]
    exact root_matrix_positive_error_le M Q r hk ω
  apply (hn.trans hh).trans
  apply ENNReal.ofReal_le_ofReal
  have hH : 38 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  have he := root_matrix_depth_factor (rootH0 r) hk.1 hk.2 hH
  have hscalar : 128*rootResponseEnvelope (rootTau r)*Real.sqrt p*Real.sqrt (bankLayerWeight hk.2)*
      (1/3:ℝ)^(hk.2+1+whitneyProfile (rootH0 r+hk.1) (hk.2+1))*(3:ℝ)^40 =
      128*Real.sqrt p*rootResponseEnvelope (rootTau r)*Real.sqrt (bankLayerWeight hk.2)*
        (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1)) := by
    calc
      _ = (128*Real.sqrt p*rootResponseEnvelope (rootTau r)*Real.sqrt (bankLayerWeight hk.2))*
          ((1/3:ℝ)^(hk.2+1+whitneyProfile (rootH0 r+hk.1) (hk.2+1))*(3:ℝ)^40) := by ring
      _ = _ := congrArg (fun a : ℝ => (128*Real.sqrt p*rootResponseEnvelope (rootTau r)*Real.sqrt (bankLayerWeight hk.2))*a) he
  rw [hscalar]
  have ht : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hG : 0 ≤ rootResponseEnvelope (rootTau r) := by unfold rootResponseEnvelope; positivity
  have hpos : 0 ≤ Real.sqrt p*rootResponseEnvelope (rootTau r)*Real.sqrt (bankLayerWeight hk.2)*
      (3:ℝ)^(-((localizationResetAbscissa (rootH0 r-38) hk.1 hk.2:ℝ)+1)) := by positivity
  nlinarith only [hpos]

end
end ASDExplicitGamma.Inverse
