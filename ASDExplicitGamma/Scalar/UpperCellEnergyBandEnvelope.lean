module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandPair
public import ASDExplicitGamma.Scalar.UpperCellEnergyBandSupremum
public import ASDExplicitGamma.Scalar.UpperCellEnergyCompactMoment

/-! Moments of the actual correlated gradient/Hessian full-band envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Gaussian Model
open Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The two full-band tensor suprema, with deterministic physical scale weights. -/
def upperCellBandEnvelope {d : ℕ} (k : Fin d → ℤ) (w : Fin d → ℝ)
    (c : Vec 2) (s a b : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  a*‖upperCellBandSquareTensor k w Q3SpatialJet.first c s ω‖+
    b*‖upperCellBandSquareTensor k w
      (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) c s ω‖

/-- Mean bound obtained by chaining the full-band kernels. -/
def upperCellBandEnvelopeMean {d : ℕ} (M : ABKModel 2) (h : ℝ)
    (k : Fin d → ℤ) (w : Fin d → ℝ) (s a b : ℝ) : ℝ :=
  a*(Real.sqrt (waveTau1*upperCellBandVariance M h k w 1)+
    (s*Real.sqrt (upperCellBandVariance M h k w 2))*
      (Real.sqrt waveTau2/2+2*Real.sqrt (Real.log 2)*waveEll2))+
  b*(Real.sqrt (waveTau2*upperCellBandVariance M h k w 2)+
    (s*Real.sqrt (upperCellBandVariance M h k w 3))*
      (Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3))

/-- Cameron--Martin constant of the combined envelope, retaining the correlation. -/
def upperCellBandEnvelopeCM {d : ℕ} (M : ABKModel 2) (h : ℝ)
    (k : Fin d → ℤ) (w : Fin d → ℝ) (a b : ℝ) : ℝ :=
  a*Real.sqrt (waveEll1^2*upperCellBandVariance M h k w 1)+
    b*Real.sqrt (waveEll2^2*upperCellBandVariance M h k w 2)

/-- The actual envelope is nonnegative for physical weights. -/
theorem upper_cell_band_envelope_nonneg {d : ℕ}
    (k : Fin d → ℤ) (w : Fin d → ℝ) (c : Vec 2) (s a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ω : Cutoff.CutoffSample 2) :
    0 ≤ upperCellBandEnvelope k w c s a b ω :=
  add_nonneg (mul_nonneg ha (norm_nonneg _)) (mul_nonneg hb (norm_nonneg _))

/-- Integrability and the mean estimate for the actual full-band envelope. -/
theorem upper_cell_band_envelope_mean {d : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin d → ℤ) (hk : Function.Injective k) (w : Fin d → ℝ)
    (c : Vec 2) (s a b : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV2 : 0 < upperCellBandVariance M h k w 2)
    (hV3 : 0 < upperCellBandVariance M h k w 3) :
    Integrable (upperCellBandEnvelope k w c s a b) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, upperCellBandEnvelope k w c s a b ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      upperCellBandEnvelopeMean M h k w s a b := by
  have h1 := upper_cell_band_first_supremum_mean M h hM k hk w c s hs hV2
  have h2 := upper_cell_band_second_supremum_mean M h hM k hk w c s hs hV3
  refine ⟨(h1.1.const_mul a).add (h2.1.const_mul b), ?_⟩
  unfold upperCellBandEnvelope upperCellBandEnvelopeMean
  rw [integral_add (h1.1.const_mul a) (h2.1.const_mul b), integral_const_mul, integral_const_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left h1.2 ha) (mul_le_mul_of_nonneg_left h2.2 hb)

/-- Gaussian concentration of the combined envelope, with every law and variance
input instantiated on the actual cutoff sample carrier. -/
theorem upper_cell_band_envelope_mgf {d : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin d → ℤ) (hk : Function.Injective k) (w : Fin d → ℝ)
    (c : Vec 2) (s a b : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV2 : 0 < upperCellBandVariance M h k w 2)
    (hV3 : 0 < upperCellBandVariance M h k w 3) (lam : ℝ) :
    Integrable (fun ω => Real.exp (lam*(upperCellBandEnvelope k w c s a b ω-
      ∫ y, upperCellBandEnvelope k w c s a b y ∂(Cutoff.cutoffSampleLaw M).toMeasure)))
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, Real.exp (lam*(upperCellBandEnvelope k w c s a b ω-
      ∫ y, upperCellBandEnvelope k w c s a b y ∂(Cutoff.cutoffSampleLaw M).toMeasure))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      Real.exp (lam^2*(upperCellBandEnvelopeCM M h k w a b)^2/2) := by
  let squareNonempty : Nonempty (supMeanClosedSquare c s) :=
    ⟨⟨c, supMean_center_mem_closed_square c s hs.le⟩⟩
  have h1 := upper_cell_band_first_supremum_mean M h hM k hk w c s hs hV2
  have h2 := upper_cell_band_second_supremum_mean M h hM k hk w c s hs hV3
  exact upper_cell_compact_pair_mgf (Cutoff.cutoffSampleLaw M).toMeasure _ _ a b ha hb
    h1.1 h2.1 (upper_cell_band_pair_gaussian c s M h hM k hk w a b)
    _ lam (add_nonneg (mul_nonneg ha (Real.sqrt_nonneg _))
      (mul_nonneg hb (Real.sqrt_nonneg _)))
    (upper_cell_band_pair_projection_variance c s M h hM k hk w a b ha hb)

/-- All moments of the actual full-band envelope. In particular p=6 supplies
the sensitivity moment; no envelope moment or independence premise is assumed. -/
theorem upper_cell_band_envelope_moment {d : ℕ}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin d → ℤ) (hk : Function.Injective k) (w : Fin d → ℝ)
    (c : Vec 2) (s a b : ℝ) (hs : 0 < s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hV2 : 0 < upperCellBandVariance M h k w 2)
    (hV3 : 0 < upperCellBandVariance M h k w 3)
    (hL : 0 < upperCellBandEnvelopeCM M h k w a b) (p : ℝ) (hp : 1 ≤ p) :
    MemLp (upperCellBandEnvelope k w c s a b) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (eLpNorm (upperCellBandEnvelope k w c s a b) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure).toReal^2 ≤
      2*(upperCellBandEnvelopeMean M h k w s a b)^2+
        2*p*(upperCellBandEnvelopeCM M h k w a b)^2 := by
  have hm := upper_cell_band_envelope_mean M h hM k hk w c s a b hs ha hb hV2 hV3
  have hz := upper_cell_band_envelope_nonneg k w c s a b ha hb
  have hh := upper_cell_nonneg_gaussian_moment (Cutoff.cutoffSampleLaw M).toMeasure
    _ hz hm.1 _ p hL hp
    (upper_cell_band_envelope_mgf M h hM k hk w c s a b hs ha hb hV2 hV3)
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hsquare := pow_le_pow_left₀ (integral_nonneg hz) hm.2 2
  linarith only [hsquare]

end
end ASDExplicitGamma.Scalar
