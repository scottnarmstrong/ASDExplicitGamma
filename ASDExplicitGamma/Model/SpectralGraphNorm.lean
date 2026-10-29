module

public import ASDExplicitGamma.Model.SpectralMeasure

@[expose] public section

open MeasureTheory

namespace ASDExplicitGamma.Model

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {w : α → ℝ}

private theorem le_graphWeight_measure (hw : ∀ x, 1 ≤ w x) :
    μ ≤ μ.withDensity (fun x => ENNReal.ofReal (w x)) := by
  conv_lhs => rw [← withDensity_one (μ := μ)]
  apply withDensity_mono
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Pi.one_apply, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hw x)

private theorem integrable_graphWeight_norm_sq
    (hwm : AEMeasurable w μ) (hw : ∀ x, 1 ≤ w x)
    (f : Lp ℂ 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    Integrable (fun x => w x * ‖f x‖ ^ 2) μ := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp
    (Lp.memLp f)
  have h := (integrable_withDensity_iff_integrable_smul₀' hwm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
  simpa only [ENNReal.toReal_ofReal (zero_le_one.trans (hw _)), smul_eq_mul] using h

/-- Multiplication by `a` maps the weighted `L²` space into the base space
whenever `|a|² ≤ w`. -/
theorem memLp_graphWeight_mul
    (hwm : AEMeasurable w μ) (hw : ∀ x, 1 ≤ w x)
    {a : α → ℂ} (ham : AEStronglyMeasurable a μ) (ha : ∀ x, ‖a x‖ ^ 2 ≤ w x)
    (f : Lp ℂ 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    MemLp (fun x => a x * f x) 2 μ := by
  have hf : MemLp (fun x => f x) 2 μ :=
    MemLp.mono_measure (le_graphWeight_measure hw) (Lp.memLp f)
  apply (memLp_two_iff_integrable_sq_norm (ham.mul hf.aestronglyMeasurable)).mpr
  apply (integrable_graphWeight_norm_sq hwm hw f).mono'
    ((ham.mul hf.aestronglyMeasurable).norm.pow 2)
  exact Filter.Eventually.of_forall fun x => by
    change ‖‖a x * f x‖ ^ 2‖ ≤ w x * ‖f x‖ ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (ha x) (sq_nonneg _)

private theorem lp_norm_sq (ν : Measure α) (f : Lp ℂ 2 ν) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

/-- The weighted multiplier is a contraction for the graph norm. -/
theorem norm_graphWeight_mul_le
    (hwm : AEMeasurable w μ) (hw : ∀ x, 1 ≤ w x)
    {a : α → ℂ} (ham : AEStronglyMeasurable a μ) (ha : ∀ x, ‖a x‖ ^ 2 ≤ w x)
    (f : Lp ℂ 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    ‖(memLp_graphWeight_mul hwm hw ham ha f).toLp (fun x => a x * f x)‖ ≤ ‖f‖ := by
  let hg := memLp_graphWeight_mul hwm hw ham ha f
  have hleft : ‖hg.toLp (fun x => a x * f x)‖ ^ 2 =
      ∫ x, ‖a x * f x‖ ^ 2 ∂μ := by
    rw [lp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx]
  have hright : ‖f‖ ^ 2 = ∫ x, w x * ‖f x‖ ^ 2 ∂μ := by
    rw [lp_norm_sq, integral_withDensity_eq_integral_toReal_smul₀ hwm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (zero_le_one.trans (hw _)), smul_eq_mul]
  have hi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hs : ‖hg.toLp (fun x => a x * f x)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [hleft, hright]
    apply integral_mono hi (integrable_graphWeight_norm_sq hwm hw f)
    intro x
    change ‖a x * f x‖ ^ 2 ≤ w x * ‖f x‖ ^ 2
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (ha x) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

/-- The continuous map from a graph-weight `L²` space to its multiplier image. -/
noncomputable def graphWeightMultiplier
    (hwm : AEMeasurable w μ) (hw : ∀ x, 1 ≤ w x)
    {a : α → ℂ} (ham : AEStronglyMeasurable a μ) (ha : ∀ x, ‖a x‖ ^ 2 ≤ w x) :
    Lp ℂ 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))) →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_graphWeight_mul hwm hw ham ha f).toLp (fun x => a x * f x)
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [(memLp_graphWeight_mul hwm hw ham ha (f + g)).coeFn_toLp,
          (memLp_graphWeight_mul hwm hw ham ha f).coeFn_toLp,
          (memLp_graphWeight_mul hwm hw ham ha g).coeFn_toLp,
          Lp.coeFn_add
            ((memLp_graphWeight_mul hwm hw ham ha f).toLp (fun x => a x * f x))
            ((memLp_graphWeight_mul hwm hw ham ha g).toLp (fun x => a x * g x)),
          ae_mono (le_graphWeight_measure hw) (Lp.coeFn_add f g)] with x hsum hf hg hout hin
        simp only [Pi.add_apply] at hout hin
        rw [hsum, hout, hf, hg, hin]
        exact mul_add _ _ _
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [(memLp_graphWeight_mul hwm hw ham ha (c • f)).coeFn_toLp,
          (memLp_graphWeight_mul hwm hw ham ha f).coeFn_toLp,
          Lp.coeFn_smul c
            ((memLp_graphWeight_mul hwm hw ham ha f).toLp (fun x => a x * f x)),
          ae_mono (le_graphWeight_measure hw) (Lp.coeFn_smul c f)] with x hcf hf hout hin
        simp only [RingHom.id_apply]
        simp only [Pi.smul_apply] at hout hin
        rw [hcf, hout, hf, hin]
        simp only [smul_eq_mul]
        ring }
    1 (fun f => by
      change ‖(memLp_graphWeight_mul hwm hw ham ha f).toLp (fun x => a x * f x)‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact norm_graphWeight_mul_le hwm hw ham ha f)

/-- The continuous multiplier is represented by pointwise multiplication. -/
theorem graphWeightMultiplier_coeFn
    (hwm : AEMeasurable w μ) (hw : ∀ x, 1 ≤ w x)
    {a : α → ℂ} (ham : AEStronglyMeasurable a μ) (ha : ∀ x, ‖a x‖ ^ 2 ≤ w x)
    (f : Lp ℂ 2 (μ.withDensity (fun x => ENNReal.ofReal (w x)))) :
    (graphWeightMultiplier hwm hw ham ha f : α → ℂ) =ᵐ[μ] fun x => a x * f x :=
  (memLp_graphWeight_mul hwm hw ham ha f).coeFn_toLp

/-- Forget the graph weight while keeping the same spectral function. -/
noncomputable def q3SpectralGraphToBase (h : ℝ) :
    Lp ℂ 2 (q3SpectralGraphMeasure h) →L[ℂ] Lp ℂ 2 (q3SpectralMeasure h) :=
  graphWeightMultiplier (μ := q3SpectralMeasure h)
    (w := fun ξ : Q3FrequencyPlane => 1 + ‖ξ‖ ^ 2)
    (by fun_prop) (fun ξ => le_add_of_nonneg_right (sq_nonneg ‖ξ‖))
    (a := fun _ => 1) aestronglyMeasurable_const (fun ξ => by simpa only [norm_one, one_pow] using le_add_of_nonneg_right (sq_nonneg ‖ξ‖))

/-- A real coordinate on the Euclidean frequency plane. -/
def q3FrequencyCoordinate (i : Fin 2) (ξ : Q3FrequencyPlane) : ℝ :=
  if i = 0 then ξ.fst else ξ.snd

theorem q3FrequencyCoordinate_continuous (i : Fin 2) :
    Continuous (q3FrequencyCoordinate i) := by
  unfold q3FrequencyCoordinate
  split_ifs <;> fun_prop

theorem q3FrequencyCoordinate_sq_le (i : Fin 2) (ξ : Q3FrequencyPlane) :
    (q3FrequencyCoordinate i ξ) ^ 2 ≤ 1 + ‖ξ‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [Real.norm_eq_abs, sq_abs, q3FrequencyCoordinate]
  split_ifs <;> nlinarith only [sq_nonneg ξ.fst, sq_nonneg ξ.snd]

/-- Coordinate multiplication is bounded from graph norm to base norm. -/
noncomputable def q3SpectralGraphCoordinate (h : ℝ) (i : Fin 2) :
    Lp ℂ 2 (q3SpectralGraphMeasure h) →L[ℂ] Lp ℂ 2 (q3SpectralMeasure h) :=
  graphWeightMultiplier (μ := q3SpectralMeasure h)
    (w := fun ξ : Q3FrequencyPlane => 1 + ‖ξ‖ ^ 2)
    (by fun_prop) (fun ξ => le_add_of_nonneg_right (sq_nonneg ‖ξ‖))
    (a := fun ξ => (q3FrequencyCoordinate i ξ : ℂ))
    (Complex.continuous_ofReal.comp (q3FrequencyCoordinate_continuous i)).aestronglyMeasurable
    (fun ξ => by
      simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact q3FrequencyCoordinate_sq_le i ξ)

/-- The multiplier domain coincides with the weighted `L²` carrier. -/
theorem q3Spectral_memLp_graphWeight
    (h : ℝ) (f : Lp ℂ 2 (q3SpectralMeasure h))
    (hf : ∀ i : Fin 2, MemLp (fun ξ => (q3FrequencyCoordinate i ξ : ℂ) * f ξ)
      2 (q3SpectralMeasure h)) :
    MemLp (f : Q3FrequencyPlane → ℂ) 2 (q3SpectralGraphMeasure h) := by
  have hm : AEStronglyMeasurable (f : Q3FrequencyPlane → ℂ)
      (q3SpectralGraphMeasure h) :=
    (Lp.memLp f).aestronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (integrable_withDensity_iff_integrable_smul₀'
    (by fun_prop : AEMeasurable (fun ξ : Q3FrequencyPlane => ENNReal.ofReal (1 + ‖ξ‖ ^ 2))
      (q3SpectralMeasure h))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  have hi0 := (memLp_two_iff_integrable_sq_norm (hf 0).aestronglyMeasurable).mp (hf 0)
  have hi1 := (memLp_two_iff_integrable_sq_norm (hf 1).aestronglyMeasurable).mp (hf 1)
  have hif := (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp
    (Lp.memLp f)
  convert (hif.add hi0).add hi1 using 1
  funext ξ
  simp only [smul_eq_mul, Pi.add_apply, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, q3FrequencyCoordinate, WithLp.prod_norm_sq_eq_of_L2,
    ite_true]
  norm_num
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

theorem q3SpectralMeasure_le_graphMeasure (h : ℝ) :
    q3SpectralMeasure h ≤ q3SpectralGraphMeasure h :=
  le_graphWeight_measure (fun ξ => le_add_of_nonneg_right (sq_nonneg ‖ξ‖))

theorem q3SpectralGraphToBase_coeFn (h : ℝ)
    (f : Lp ℂ 2 (q3SpectralGraphMeasure h)) :
    (q3SpectralGraphToBase h f : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h] f := by
  unfold q3SpectralGraphToBase
  apply (graphWeightMultiplier_coeFn _ _ _ _ f).trans
  exact Filter.Eventually.of_forall fun ξ => one_mul (f ξ)

theorem q3SpectralGraphCoordinate_coeFn (h : ℝ) (i : Fin 2)
    (f : Lp ℂ 2 (q3SpectralGraphMeasure h)) :
    (q3SpectralGraphCoordinate h i f : Q3FrequencyPlane → ℂ) =ᵐ[q3SpectralMeasure h]
      fun ξ => (q3FrequencyCoordinate i ξ : ℂ) * f ξ :=
  graphWeightMultiplier_coeFn (by fun_prop)
    (fun ξ => le_add_of_nonneg_right (sq_nonneg ‖ξ‖))
    (Complex.continuous_ofReal.comp (q3FrequencyCoordinate_continuous i)).aestronglyMeasurable
    (fun ξ => by
      simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs] using q3FrequencyCoordinate_sq_le i ξ) f

end ASDExplicitGamma.Model
