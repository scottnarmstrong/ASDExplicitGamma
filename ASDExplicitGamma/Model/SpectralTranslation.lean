module

public import ASDExplicitGamma.Model.SpectralFirstChaosIsometry

@[expose] public section

open MeasureTheory Homogenization Complex

namespace ASDExplicitGamma.Model

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A measurable unit-modulus multiplier preserves square integrability. -/
theorem memLp_unit_mul {a : α → ℂ} (ham : AEStronglyMeasurable a μ)
    (ha : ∀ x, ‖a x‖ = 1) (f : Lp ℂ 2 μ) : MemLp (fun x => a x * f x) 2 μ := by
  apply (Lp.memLp f).norm.mono' (ham.mul (Lp.memLp f).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖a x * f x‖ ≤ ‖f x‖
    rw [norm_mul, ha x, one_mul]

/-- Multiplication by a unit-modulus measurable function is a linear isometry. -/
noncomputable def lpUnitMultiplier {a : α → ℂ} (ham : AEStronglyMeasurable a μ)
    (ha : ∀ x, ‖a x‖ = 1) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 μ where
  toFun f := (memLp_unit_mul ham ha f).toLp (fun x => a x * f x)
  map_add' := by
    intro f g
    apply Lp.ext
    filter_upwards [(memLp_unit_mul ham ha (f + g)).coeFn_toLp,
      (memLp_unit_mul ham ha f).coeFn_toLp, (memLp_unit_mul ham ha g).coeFn_toLp,
      Lp.coeFn_add f g,
      Lp.coeFn_add ((memLp_unit_mul ham ha f).toLp _) ((memLp_unit_mul ham ha g).toLp _)]
      with x hsum hf hg hin hout
    simp only [Pi.add_apply] at hin hout
    rw [hsum, hout, hf, hg, hin]
    exact mul_add _ _ _
  map_smul' := by
    intro c f
    apply Lp.ext
    filter_upwards [(memLp_unit_mul ham ha (c • f)).coeFn_toLp,
      (memLp_unit_mul ham ha f).coeFn_toLp, Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((memLp_unit_mul ham ha f).toLp _)] with x hcf hf hin hout
    simp only [Pi.smul_apply] at hin hout
    simp only [RingHom.id_apply]
    rw [hcf, hout, hf, hin]
    simp only [smul_eq_mul]
    ring
  norm_map' f := by
    have hc := (memLp_unit_mul ham ha f).coeFn_toLp
    apply le_antisymm
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hc] with x hx
      change ‖((memLp_unit_mul ham ha f).toLp (fun x => a x * f x)) x‖ ≤ ‖f x‖
      rw [hx, norm_mul, ha x, one_mul]
    · apply Lp.norm_le_norm_of_ae_le
      filter_upwards [hc] with x hx
      change ‖f x‖ ≤ ‖((memLp_unit_mul ham ha f).toLp (fun x => a x * f x)) x‖
      rw [hx, norm_mul, ha x, one_mul]

theorem lpUnitMultiplier_coeFn {a : α → ℂ} (ham : AEStronglyMeasurable a μ)
    (ha : ∀ x, ‖a x‖ = 1) (f : Lp ℂ 2 μ) :
    (lpUnitMultiplier ham ha f : α → ℂ) =ᵐ[μ] fun x => a x * f x :=
  (memLp_unit_mul ham ha f).coeFn_toLp

/-- The scalar character multiplier of a physical translation. -/
noncomputable def q3SpectralPhase (z : Vec 2) (ξ : Q3FrequencyPlane) : ℂ :=
  exp (((2 * Real.pi * (ξ.fst * z 0 + ξ.snd * z 1) : ℝ) : ℂ) * I)

theorem q3SpectralPhase_continuous (z : Vec 2) : Continuous (q3SpectralPhase z) := by
  unfold q3SpectralPhase
  fun_prop

theorem q3SpectralPhase_norm (z : Vec 2) (ξ : Q3FrequencyPlane) :
    ‖q3SpectralPhase z ξ‖ = 1 := norm_exp_ofReal_mul_I _

/-- Spectral translation as a bounded multiplication operator. -/
noncomputable def q3SpectralTranslation (h : ℝ) (z : Vec 2) :
    Lp ℂ 2 (q3SpectralMeasure h) →ₗᵢ[ℂ] Lp ℂ 2 (q3SpectralMeasure h) :=
  lpUnitMultiplier (q3SpectralPhase_continuous z).aestronglyMeasurable (q3SpectralPhase_norm z)

/-- Complex Koopman translations on the literal J4 probability carrier. -/
noncomputable def q3ComplexKoopman (M : Algsuperdiff.Section3.ABKModel 2) (z : Vec 2) :
    Lp ℂ 2 (planarRegLaw M) →ₗᵢ[ℂ] Lp ℂ 2 (planarRegLaw M) :=
  Lp.compMeasurePreservingₗᵢ ℂ (z +ᵥ ·)
    (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := planarRegLaw M) z)

theorem q3ComplexStream_coeFn (M : Algsuperdiff.Section3.ABKModel 2) (x : Vec 2) :
    (q3ComplexStream M x : RegCoeffField 2 → ℂ) =ᵐ[planarRegLaw M]
      fun a => (a x 1 0 : ℂ) := by
  have hc := Complex.ofRealCLM.coeFn_compLpL
    (q3StreamKoopman M x (q3StreamOriginL2 M))
  filter_upwards [hc, q3StreamKoopman_apply M x] with a hc ha
  change ((Complex.ofRealCLM.compLpL 2 (planarRegLaw M))
    (q3StreamKoopman M x (q3StreamOriginL2 M))) a = _
  rw [hc, ha, Complex.ofRealCLM_apply]

theorem q3ComplexKoopman_stream (M : Algsuperdiff.Section3.ABKModel 2) (z x : Vec 2) :
    q3ComplexKoopman M z (q3ComplexStream M x) = q3ComplexStream M (z + x) := by
  let mp := Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd
    (μ := planarRegLaw M) z
  have hc := Lp.coeFn_compMeasurePreserving (q3ComplexStream M x) mp
  have ht := mp.quasiMeasurePreserving.ae_eq_comp (q3ComplexStream_coeFn M x)
  apply Lp.ext
  filter_upwards [hc, ht, q3ComplexStream_coeFn M (z + x)] with a hc ht ha
  change (Lp.compMeasurePreserving (z +ᵥ ·) mp (q3ComplexStream M x)) a = _
  rw [hc, ha]
  have he : (z +ᵥ a : RegCoeffField 2) = translateReg z a := rfl
  simpa only [Function.comp_apply, he, translateReg_apply, add_comm] using ht

theorem q3SpectralTranslation_coeFn (h : ℝ) (z : Vec 2)
    (f : Lp ℂ 2 (q3SpectralMeasure h)) :
    (q3SpectralTranslation h z f : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h]
      fun ξ => q3SpectralPhase z ξ * f ξ :=
  lpUnitMultiplier_coeFn (q3SpectralPhase_continuous z).aestronglyMeasurable
    (q3SpectralPhase_norm z) f

theorem q3SpectralTranslation_character (h : ℝ) (z x : Vec 2) :
    q3SpectralTranslation h z (q3SpectralCharacter h (q3SpectralPoint x)) =
      q3SpectralCharacter h (q3SpectralPoint (z + x)) := by
  apply Lp.ext
  filter_upwards [q3SpectralTranslation_coeFn h z
    (q3SpectralCharacter h (q3SpectralPoint x)),
    q3SpectralCharacter_coeFn h (q3SpectralPoint x),
    q3SpectralCharacter_coeFn h (q3SpectralPoint (z + x))] with ξ ht hx hzx
  rw [ht, hx, hzx]
  simp only [q3SpectralPhase, q3SpectralPoint, WithLp.toLp_fst, WithLp.toLp_snd, Pi.add_apply]
  rw [← exp_add]
  congr 1
  push_cast
  ring

/-- The concrete spectral isometry intertwines all physical translations. -/
theorem q3SpectralInverse_intertwine
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) (z : Vec 2)
    (f : Lp ℂ 2 (q3SpectralMeasure h)) :
    q3ComplexKoopman M z (q3SpectralInverse M h hM f) =
      q3SpectralInverse M h hM (q3SpectralTranslation h z f) := by
  apply DenseRange.induction_on (q3SpectralCombination_dense h)
    (p := fun g => q3ComplexKoopman M z (q3SpectralInverse M h hM g) =
      q3SpectralInverse M h hM (q3SpectralTranslation h z g)) f
  · exact isClosed_eq
      ((q3ComplexKoopman M z).continuous.comp (q3SpectralInverse M h hM).continuous)
      ((q3SpectralInverse M h hM).continuous.comp (q3SpectralTranslation h z).continuous)
  · intro c
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
      q3SpectralInverse_character, q3SpectralTranslation_character, q3ComplexKoopman_stream]

end ASDExplicitGamma.Model
