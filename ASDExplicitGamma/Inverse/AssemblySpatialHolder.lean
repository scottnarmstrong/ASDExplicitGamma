module

public import ASDExplicitGamma.Inverse.FullResponseActiveSpatialDensity
public import ASDExplicitGamma.Inverse.AssemblyActiveSpatialCharge

/-! Spatial Holder for the actual wave-weighted geometric density. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- A bounded real field has a square in spatial L2 on a finite measure. -/
theorem assembly_square_memLp_two {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : MemLp f ⊤ μ) :
    MemLp (fun x => f x^2) 2 μ := by
  have h4 : MemLp f 4 μ := hf.mono_exponent (by norm_num)
  have hh := h4.norm_rpow_div (ENNReal.ofReal 2)
  have he : (4:ℝ≥0∞)/ENNReal.ofReal (2:ℝ)=2 := by
    rw [show (4:ℝ≥0∞)=ENNReal.ofReal (4:ℝ) by norm_num]
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [he,ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2)] at hh
  simpa only [Real.norm_eq_abs,Real.rpow_two,sq_abs] using hh

/-- Spatial Cauchy--Schwarz keeps the density fourth moment on the actual
layer and pays the wave fourth moment on the whole root. -/
theorem assembly_spatial_square_product_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (f g : α → ℝ)
    (hf : MemLp (fun x => f x^2) 2 μ)
    (hg : MemLp (fun x => g x^2) 2 μ) :
    (∫ x in E, f x^2*g x^2 ∂μ) ≤
      Real.sqrt (∫ x, f x^4 ∂μ)*Real.sqrt (∫ x in E, g x^4 ∂μ) := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
    (Filter.Eventually.of_forall (fun x => sq_nonneg (g x)))
    (by simpa only [ENNReal.ofReal_ofNat] using hf.restrict E)
    (by simpa only [ENNReal.ofReal_ofNat] using hg.restrict E)
  have hpow (u : α → ℝ) : (fun x => (u x^2)^(2:ℝ))=fun x => u x^4 := by
    funext x
    rw [Real.rpow_two]
    ring
  rw [hpow f,hpow g] at hh
  have hi := hf.integrable_norm_pow (p := 2) (by norm_num : 2 ≠ 0)
  have hfi : Integrable (fun x => f x^4) μ := by
    convert hi using 1
    funext x
    simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (f x))]
    ring
  have hmono : (∫ x in E, f x^4 ∂μ) ≤ ∫ x, f x^4 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun x => by positivity) hfi
  rw [show (1/(2:ℝ))=1/2 by rfl,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmono) (Real.sqrt_nonneg _))

/-- The actual later band and all three actual geometric resolutions meet
the spatial Holder hypotheses on every sample, with no regularity premise. -/
theorem assembly_actual_spatial_square_product_le
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (τ η : ℝ) (e : Fin 3) (j N : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    (∫ x in rootLayerCarrier Q (H0+hk.1) (hk.2+1),
      (laterScalarBand j N weights ω x)^2*
        (layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω x)^2
      ∂normalizedCubeMeasure Q) ≤
      Real.sqrt (cubeAverage Q (fun x => (laterScalarBand j N weights ω x)^4))*
        Real.sqrt (∫ x in rootLayerCarrier Q (H0+hk.1) (hk.2+1),
          (layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω x)^4
          ∂normalizedCubeMeasure Q) := by
  have hf : MemLp (laterScalarBand j N weights ω) ⊤ (normalizedCubeMeasure Q) := by
    rw [← later_band_w2_value Q j N weights ω]
    exact PlanarW2Infinity.value_memLp_top_normalized (laterBandW2 Q j N weights ω)
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact assembly_spatial_square_product_le _ _ _ _
    (assembly_square_memLp_two _ _ hf)
    (layer_resolution_density_square_memLp M Q Q (fun _ hx => hx) H0 hH0 hk τ η e ω)

/-- Normalizing a layer contained in the root gives its exact root-volume
fraction, including translated and negative-scale cubes. -/
theorem assembly_normalized_layer_integral (Q : TriadicCube 2)
    (E : Set (Vec 2)) (hEQ : E ⊆ cubeSet Q) (f : Vec 2 → ℝ) :
    (∫ x in E, f x ∂normalizedCubeMeasure Q) =
      (∫ x in E, f x ∂volume)/(volume (cubeSet Q)).toReal := by
  unfold normalizedCubeMeasure cubeMeasure
  rw [Measure.restrict_smul,Measure.restrict_restrict_of_subset hEQ,
    integral_smul_measure,ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_pos Q).le),
    volume_cubeSet_toReal]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- Every normalized actual density power is its rare-moment baseline plus
its own literal positive excess at the actual geometric resolution. -/
theorem assembly_normalized_density_power_le_excess
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (τ η q T : ℝ) (m : ℕ) (e : Fin 3) (ω : Cutoff.CutoffSample 2) :
    (∫ x in rootLayerCarrier Q (H0+hk.1) (hk.2+1),
      (layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω x)^m
      ∂normalizedCubeMeasure Q) ≤
      bankLayerWeight hk.2*densityMomentBudget q m T+
        resetDensityExcess M Q H0 τ η q T m hk e ω := by
  have hEQ : rootLayerCarrier Q (H0+hk.1) (hk.2+1) ⊆ cubeSet Q := by
    rw [root_layer_carrier_eq_localization]
    exact localization_whitney_layer_subset Q _ _
  rw [assembly_normalized_layer_integral Q _ hEQ,
    root_layer_carrier_eq_localization]
  simp only [layerResolutionDiameter,layer_resolution_density_label Q H0 hH0 hk e]
  change rootDiameterAverage _ Q (resetDensityDepth H0 hk e) _ m ω ≤ _
  have hh := le_max_left
    (rootDiameterAverage (q3PlanarMarks M (rootFineLabel Q (resetDensityDepth H0 hk e)) τ η)
      Q (resetDensityDepth H0 hk e) (localizationWhitneyLayer Q (H0+hk.1) hk.2) m ω-
        bankLayerWeight hk.2*densityMomentBudget q m T) 0
  change _ ≤ resetDensityExcess M Q H0 τ η q T m hk e ω at hh
  linarith only [hh]

/-- Splitting the square root preserves a separate positive fluctuation. -/
theorem assembly_sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a+b) ≤ Real.sqrt a+Real.sqrt b := by
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (add_nonneg ha hb)]
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hab := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  nlinarith only [hsa,hsb,hab]

/-- The actual wave-density product splits into the rare fourth-moment
baseline and the correlated wave times square-root excess. -/
theorem assembly_actual_wave_density_le_mean_excess
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (τ η q T : ℝ) (hB : 0 ≤ densityMomentBudget q 4 T)
    (e : Fin 3) (j N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    (∫ x in rootLayerCarrier Q (H0+hk.1) (hk.2+1),
      (laterScalarBand j N weights ω x)^2*
        (layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω x)^2
      ∂normalizedCubeMeasure Q) ≤
      Real.sqrt (cubeAverage Q (fun x => (laterScalarBand j N weights ω x)^4))*
        (Real.sqrt (bankLayerWeight hk.2)*Real.sqrt (densityMomentBudget q 4 T)+
          Real.sqrt (resetDensityExcess M Q H0 τ η q T 4 hk e ω)) := by
  have hh := assembly_actual_spatial_square_product_le M Q H0 hH0 hk τ η e j N weights ω
  have hd := assembly_normalized_density_power_le_excess M Q H0 hH0 hk τ η q T 4 e ω
  have hsplit := assembly_sqrt_add_le
    (bankLayerWeight hk.2*densityMomentBudget q 4 T)
    (resetDensityExcess M Q H0 τ η q T 4 hk e ω)
    (mul_nonneg (bankLayerWeight_nonneg _) hB) (reset_density_excess_nonneg _ _ _ _ _ _ _ _ _ _ _)
  rw [Real.sqrt_mul (bankLayerWeight_nonneg _)] at hsplit
  exact hh.trans (mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hd).trans hsplit)
    (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Inverse
