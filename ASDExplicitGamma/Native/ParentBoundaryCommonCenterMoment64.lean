module

public import ASDExplicitGamma.Native.ParentBoundaryBandCenterLaw
public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeCarrier

/-! Sharp sixty-fourth moments of the actual shared source-square center. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ProbabilityTheory Response Scalar Gaussian Inverse Main Triadic Algsuperdiff.Section3
open scoped NNReal ENNReal Nat
noncomputable section

local instance parentCommonCenterMomentCompact (P : TriadicCube 2) : CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure

/-- Exact Gaussian moments give the source constant24, rather than the
coarser general real-order bound66. Zero variance is included. -/
theorem parent_boundary_gaussian_L64_sq (v : ℝ≥0) :
    (eLpNorm (id : ℝ → ℝ) 64 (gaussianReal 0 v)).toReal^2 ≤ 24*(v:ℝ) := by
  have hm := memLp_id_gaussianReal' (μ := 0) (v := v) (ENNReal.ofReal (64:ℝ)) ENNReal.ofReal_ne_top
  have he : (∫ x : ℝ,x^64 ∂gaussianReal 0 v)=((63:ℕ)‼:ℝ)*(v:ℝ)^32 := by
    rw [gaussianReal_eq_map_sqrt v,integral_map (by fun_prop) (by fun_prop)]
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have hn : (∫ x : ℝ,x^64 ∂gaussianReal 0 1)=((63:ℕ)‼:ℝ) := by
      simpa using normal_even_moment_eq_doubleFactorial 32 (by norm_num)
    rw [hn,show Real.sqrt (v:ℝ)^64=(v:ℝ)^32 by
      calc
        Real.sqrt (v:ℝ)^64=(Real.sqrt (v:ℝ)^2)^32 := by ring
        _ = (v:ℝ)^32 := congrArg (fun z : ℝ => z^(32:ℕ)) (Real.sq_sqrt v.property)]
    exact mul_comm _ _
  have hc : ((63:ℕ)‼:ℝ)≤(24:ℝ)^32 := by norm_num [Nat.doubleFactorial]
  have hsq := rio_lpNorm_sq (p := 64) (by norm_num) hm
  norm_num only [ENNReal.ofReal_ofNat] at hsq
  rw [hsq]
  have hmoment : rioMoment (gaussianReal 0 v) 64 id=(∫ x : ℝ,x^64 ∂gaussianReal 0 v) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change |x|^(64:ℝ)=x^(64:ℕ)
      rw [Real.rpow_ofNat,show (64:ℕ)=2*32 by norm_num,pow_mul,sq_abs,pow_mul]
  rw [hmoment,he]
  calc
    _ ≤ ((24:ℝ)^32*(v:ℝ)^32)^((1:ℝ)/32) :=
      Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hc (pow_nonneg v.property _)) (by norm_num)
    _ = 24*(v:ℝ) := by
      rw [←mul_pow,←Real.rpow_natCast,←Real.rpow_mul (show (0:ℝ)≤24*(v:ℝ) from mul_nonneg (by norm_num) v.property)]
      norm_num

/-- The actual physical point of the fresh band has the source L64 square
bound with its exact finite summed variance. No spatial independence is used. -/
theorem parent_boundary_band_point_L64_sq
    {b : ℕ} (K : Set (Vec 2)) [CompactSpace K]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : Fin b → ℤ) (hk : Function.Injective k) (x : K) :
    (eLpNorm (fun ω => modelBand K k ω x) 64 (Cutoff.cutoffSampleLaw M).toMeasure).toReal^2 ≤
      24*(∑ i,(q3ModelAmplitude M h (k i))^2) := by
  have hm : Measurable (fun ω => modelBand K k ω x) :=
    (ContinuousMap.evalCLM ℝ x).continuous.measurable.comp (measurable_modelBand K k)
  have hh := eLpNorm_map_measure (p := 64) (f := fun ω => modelBand K k ω x)
    (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (by fun_prop : AEStronglyMeasurable (id : ℝ → ℝ)
      ((Cutoff.cutoffSampleLaw M).toMeasure.map (fun ω => modelBand K k ω x))) hm.aemeasurable
  rw [parent_boundary_band_point_law K M h hM k hk x] at hh
  simp only [Function.id_comp] at hh
  rw [←hh]
  have hs0 : (0:ℝ) ≤ ∑ i,(q3ModelAmplitude M h (k i))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hb := parent_boundary_gaussian_L64_sq (Real.toNNReal (∑ i,(q3ModelAmplitude M h (k i))^2))
  have he : ((Real.toNNReal (∑ i,(q3ModelAmplitude M h (k i))^2)):ℝ)=
      ∑ i,(q3ModelAmplitude M h (k i))^2 := Real.coe_toNNReal _ hs0
  rw [he] at hb
  exact hb

/-- Every finite moment of the actual normalized shared center exists,
including zero time and an empty fresh band. -/
theorem parent_boundary_common_cube_center_memLp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => parentBoundaryCommonCubeCenterValue P n height t ω/
      (Annealed.sigmaBar M n:ℝ)) p (Cutoff.cutoffSampleLaw M).toMeasure := by
  let K := closure (cubeSet P)
  let X := fun ω => modelBand K (nativeSourceBandIndex n height) ω (parentBoundaryCommonCubeCenter P)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hk : Function.Injective (nativeSourceBandIndex n height) := by
    intro i j hij
    apply Fin.ext
    dsimp [nativeSourceBandIndex] at hij
    omega
  have hm : Measurable X := (ContinuousMap.evalCLM ℝ (parentBoundaryCommonCubeCenter P)).continuous.measurable.comp
    (measurable_modelBand K (nativeSourceBandIndex n height))
  have hmap : MemLp (id : ℝ → ℝ) p (μ.map X) := by
    rw [parent_boundary_band_point_law K M h hM (nativeSourceBandIndex n height) hk]
    exact memLp_id_gaussianReal' p hp
  have hx : MemLp X p μ := hmap.comp_of_map hm.aemeasurable
  have he : (fun ω => parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ))=
      (fun ω => (Real.sqrt t/(Annealed.sigmaBar M n:ℝ))*X ω) := by
    funext ω
    dsimp only [parentBoundaryCommonCubeCenterValue,X,K]
    ring
  rw [he]
  exact hx.const_mul _

/-- Sharp actual shared-center estimate in the fixed starting true frame.
The SAME scalar center is retained for every descendant at every depth. -/
theorem parent_boundary_common_cube_center_L64_sq
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (P : TriadicCube 2) (n : ℤ) (height : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (eLpNorm (fun ω => parentBoundaryCommonCubeCenterValue P n height t ω/
      (Annealed.sigmaBar M n:ℝ)) 64 (Cutoff.cutoffSampleLaw M).toMeasure).toReal^2 ≤
      24*t*((∑ i : Fin height,(q3ModelAmplitude M h (nativeSourceBandIndex n height i))^2)/
        (Annealed.sigmaBar M n:ℝ)^2) := by
  let σ : ℝ := Annealed.sigmaBar M n
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hk : Function.Injective (nativeSourceBandIndex n height) := by
    intro i j hij
    apply Fin.ext
    dsimp [nativeSourceBandIndex] at hij
    omega
  have hh := parent_boundary_band_point_L64_sq (closure (cubeSet P)) M h hM
    (nativeSourceBandIndex n height) hk (parentBoundaryCommonCubeCenter P)
  have hc : 0 ≤ Real.sqrt t/σ := div_nonneg (Real.sqrt_nonneg _) hσ.le
  have he : (fun ω => parentBoundaryCommonCubeCenterValue P n height t ω/σ)=
      (Real.sqrt t/σ) • (fun ω => modelBand (closure (cubeSet P)) (nativeSourceBandIndex n height) ω
        (parentBoundaryCommonCubeCenter P)) := by
    funext ω
    simp only [parentBoundaryCommonCubeCenterValue,Pi.smul_apply,smul_eq_mul]
    ring
  change (eLpNorm (fun ω => parentBoundaryCommonCubeCenterValue P n height t ω/σ) 64
    (Cutoff.cutoffSampleLaw M).toMeasure).toReal^2 ≤ _
  rw [he,eLpNorm_const_smul,ENNReal.toReal_mul,Real.enorm_eq_ofReal hc,ENNReal.toReal_ofReal hc,mul_pow]
  have hs : (Real.sqrt t/σ)^2=t/σ^2 := by rw [div_pow,Real.sq_sqrt ht]
  rw [hs]
  have hb := mul_le_mul_of_nonneg_left hh (div_nonneg ht (sq_nonneg σ))
  convert hb using 1
  ring

end
end ASDExplicitGamma.Native
