module

public import ASDExplicitGamma.Inverse.ClippedMatrix
public import ASDExplicitGamma.Inverse.StoppedDensityResetPowers
public import ASDExplicitGamma.Inverse.StoppedDensityResolution

/-! The retained density powers at the endpoint of every real-order band. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The ceiling defining the source band covers every real order. -/
theorem order_le_band_majorant (p : ℝ) : p ≤ bandOrderMajorant (orderBand p) := by
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hmax : 0 < max 1 (p/64) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hceil : Real.log (max 1 (p/64))/Real.log 3 ≤ (orderBand p:ℝ) :=
    Nat.le_ceil _
  have hlog := (div_le_iff₀ hlog3).mp hceil
  have hpow : max 1 (p/64) ≤ (3:ℝ)^(orderBand p) := by
    calc
      _ = Real.exp (Real.log (max 1 (p/64))) := (Real.exp_log hmax).symm
      _ ≤ Real.exp ((orderBand p:ℝ)*Real.log 3) := Real.exp_le_exp.mpr hlog
      _ = (3:ℝ)^(orderBand p) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hp64 := (le_max_right 1 (p/64)).trans hpow
  unfold bandOrderMajorant
  linarith only [hp64]

/-- Literal coefficients of the three retained powers, including the full
localization coefficient and its five-residue allowance. -/
def bandDensityCoefficient (m k : ℕ) (i : Fin 3) : ℝ :=
  if i=0 then 4*Real.sqrt (bandOrderMajorant k*63^2*uniformDensityVariance m)
  else if i=1 then 4*bandOrderMajorant k*63^2*12^m
  else bandLocalizationCoefficient m k

theorem band_density_coefficient_nonneg (m k : ℕ) (i : Fin 3) :
    0 ≤ bandDensityCoefficient m k i := by
  unfold bandDensityCoefficient
  split
  · positivity
  · split
    · unfold bandOrderMajorant
      positivity
    · unfold bandLocalizationCoefficient bandOrderMajorant
      positivity

theorem band_density_envelope_eq (m k R : ℕ) :
    bandDensityPowerEnvelope m k R =
      ∑ i : Fin 3, bandDensityCoefficient m k i *
        (3:ℝ)^(-densityPERate m i*(R:ℝ)) := by
  norm_num [bandDensityPowerEnvelope, bandDensityCoefficient,
    densityPERate, Fin.sum_univ_succ]
  ring

/-- The exact localization remainder is bounded by the retained third power
at every source resolution in every band. -/
theorem uniform_density_envelope_le_band (m k R : ℕ)
    (hR : bandDensityEntrance k ≤ R) :
    uniformDensityPowerEnvelope m (bandOrderMajorant k) R ≤
      bandDensityPowerEnvelope m k R := by
  have hlocal := localization_error_band_power m k R hR
  have hpow : (1/9:ℝ)^R = (3:ℝ)^(-2*(R:ℝ)) := by
    rw [show (1/9:ℝ)=(3:ℝ)^(-2:ℝ) by norm_num,
      ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
  rw [hpow] at hlocal
  unfold uniformDensityPowerEnvelope bandDensityPowerEnvelope
  linarith only [hlocal]

/-- The actual density excess obeys all three source powers at the band
endpoint; the probability norm is still at the requested real order p. -/
theorem root_layer_density_band_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (H i : ℕ) (hH : heightEntrance (orderBand p) ≤ H) (hi : 1 ≤ i)
    (e : Fin 3) (m : ℕ) (hm : m=2 ∨ m=4) :
    eLpNorm (rootLayerDensityExcess M Q H i e m) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (bandDensityPowerEnvelope m (orderBand p)
        (layerDepth H i-40-e.val)) := by
  let k := orderBand p
  let P := bandOrderMajorant k
  have hpP : p ≤ P := order_le_band_majorant p
  have hP : 2 ≤ P := hp.trans hpP
  have hbound := (root_layer_density_retained_Lp M h hM hγ Q k P hP
    hpast H i hH hi e m hm).2
  have hR : bandDensityEntrance k ≤ layerDepth H i-40-e.val := by
    have he : e.val ≤ 2 := by omega
    have hmargin := layer_buffer_margin_at_order k H i e.val hH hi he
    unfold bandDensityEntrance
    omega
  have hnorm := eLpNorm_le_eLpNorm_of_exponent_le
    (f := rootLayerDensityExcess M Q H i e m)
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (ENNReal.ofReal_le_ofReal hpP)
  exact (hnorm.trans hbound).trans
    (ENNReal.ofReal_le_ofReal (uniform_density_envelope_le_band m k _ hR))

end
end ASDExplicitGamma.Inverse
