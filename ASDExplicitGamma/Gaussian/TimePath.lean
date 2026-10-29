module

public import ASDExplicitGamma.Gaussian.TimeRegularity

/-! # Differentiation along a time-dependent random insertion -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- The ordinary chain-rule derivative before Gaussian integration by parts. -/
noncomputable def timePathDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G D : ℝ → E → ℝ) (x z : E) (t : ℝ) : ℝ :=
  D t (x + Real.sqrt t • z) + (1 / (2 * Real.sqrt t)) *
    fderiv ℝ (G t) (x + Real.sqrt t • z) z

/-- At positive interior time, differentiation under any law with polynomial moments is valid.
This step uses only the source regularity (8.8), without a Gaussian assumption. -/
theorem TimeRegularity.hasDerivAt_integral_path
    {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {G D : ℝ → E → ℝ} (hG : TimeRegularity G D)
    (X Z : Ω → E) (hX : Measurable X) (hZ : Measurable Z)
    (hMom : ∀ d : ℕ, Integrable (fun ω => (1 + ‖X ω‖ + ‖Z ω‖) ^ d) μ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun ω => timePathDerivative G D (X ω) (Z ω) t) μ ∧
    HasDerivAt (fun s => ∫ ω, G s (X ω + Real.sqrt s • Z ω) ∂μ)
      (∫ ω, timePathDerivative G D (X ω) (Z ω) t ∂μ) t := by
  obtain ⟨C, hC, d, hb⟩ := hG.polynomial_bound
  let M : Ω → ℝ := fun ω => 1 + ‖X ω‖ + ‖Z ω‖
  let a : ℝ := t / 2
  let b : ℝ := (t + 1) / 2
  let K : ℝ := C * (1 + 1 / (2 * Real.sqrt a))
  let bound : Ω → ℝ := fun ω => K * M ω ^ (d + 1)
  have ha : 0 < a := by dsimp [a]; linarith only [ht.1]
  have hat : a < t := by dsimp [a]; linarith only [ht.1]
  have htb : t < b := by dsimp [b]; linarith only [ht.2]
  have hb1 : b < 1 := by dsimp [b]; linarith only [ht.2]
  have hsub {s : ℝ} (hs : s ∈ Ioo a b) : s ∈ Icc (0 : ℝ) 1 :=
    ⟨(ha.trans hs.1).le, (hs.2.trans hb1).le⟩
  have hpathMeas (s : ℝ) : Measurable (fun ω => X ω + Real.sqrt s • Z ω) :=
    hX.add (hZ.const_smul (Real.sqrt s))
  have hGmeas (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : Measurable (G s) :=
    (hG.field_c2 s hs).continuous.measurable
  have hDmeas (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : Measurable (D s) := by
    have hc : Continuous (D s) := hG.continuous_time.comp_continuous
      (continuous_const.prodMk continuous_id) (fun x => ⟨hs, mem_univ x⟩)
    exact hc.measurable
  have harg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ω : Ω) :
      1 + ‖X ω + Real.sqrt s • Z ω‖ ≤ M ω := by
    have htri := norm_add_le (X ω) (Real.sqrt s • Z ω)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s)] at htri
    have hsqrt : Real.sqrt s ≤ 1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hs.2
    have hm := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (Z ω))
    dsimp [M]
    linarith
  have hval (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (ω : Ω) :
      ‖G s (X ω + Real.sqrt s • Z ω)‖ ≤ C * M ω ^ d := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (harg s hs ω) d) hC
    have h := hb s hs (X ω + Real.sqrt s • Z ω)
    rw [Real.norm_eq_abs]
    linarith [abs_nonneg (D s (X ω + Real.sqrt s • Z ω)),
      norm_nonneg (fderiv ℝ (G s) (X ω + Real.sqrt s • Z ω)),
      norm_nonneg (fderiv ℝ (fderiv ℝ (G s)) (X ω + Real.sqrt s • Z ω))]
  have hderivMeas : AEStronglyMeasurable
      (fun ω => timePathDerivative G D (X ω) (Z ω) t) μ := by
    have hdf : Continuous (fderiv ℝ (G t)) :=
      ((hG.field_c2 t ⟨ht.1.le, ht.2.le⟩).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous
    exact ((hDmeas t ⟨ht.1.le, ht.2.le⟩).comp (hpathMeas t) |>.add
      (measurable_const.mul ((hdf.measurable.comp (hpathMeas t)).clm_apply hZ))).aestronglyMeasurable
  have hbound : ∀ ω s, s ∈ Ioo a b →
      ‖timePathDerivative G D (X ω) (Z ω) s‖ ≤ bound ω := by
    intro ω s hs
    have hsmem := hsub hs
    let y := X ω + Real.sqrt s • Z ω
    have hpoly : |D s y| + ‖fderiv ℝ (G s) y‖ ≤ C * M ω ^ d := by
      have h := hb s hsmem y
      have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (harg s hsmem ω) d) hC
      linarith [abs_nonneg (G s y), norm_nonneg (fderiv ℝ (fderiv ℝ (G s)) y)]
    have hM1 : 1 ≤ M ω := by dsimp [M]; linarith [norm_nonneg (X ω), norm_nonneg (Z ω)]
    have hz : ‖Z ω‖ ≤ M ω := by dsimp [M]; linarith [norm_nonneg (X ω), norm_nonneg (Z ω)]
    have hfactor : 0 ≤ 1 / (2 * Real.sqrt s) := by positivity
    have hfactor_le : 1 / (2 * Real.sqrt s) ≤ 1 / (2 * Real.sqrt a) := by
      exact one_div_le_one_div_of_le (by positivity) (by gcongr; exact hs.1.le)
    have hD : |D s y| ≤ C * M ω ^ d := by linarith [norm_nonneg (fderiv ℝ (G s) y)]
    have hdf : ‖fderiv ℝ (G s) y‖ ≤ C * M ω ^ d := by linarith [abs_nonneg (D s y)]
    have hnorm : |fderiv ℝ (G s) y (Z ω)| ≤ C * M ω ^ d * M ω :=
      ((fderiv ℝ (G s) y).le_opNorm _).trans (mul_le_mul hdf hz (norm_nonneg _) (by positivity))
    have hpow : M ω ^ d ≤ M ω ^ (d + 1) := pow_le_pow_right₀ hM1 (Nat.le_succ d)
    calc
      ‖timePathDerivative G D (X ω) (Z ω) s‖ ≤
          |D s y| + (1 / (2 * Real.sqrt s)) * |fderiv ℝ (G s) y (Z ω)| := by
        simpa only [timePathDerivative, Real.norm_eq_abs, abs_mul, abs_of_nonneg hfactor]
          using abs_add_le (D s y) ((1 / (2 * Real.sqrt s)) * fderiv ℝ (G s) y (Z ω))
      _ ≤ C * M ω ^ (d + 1) + (1 / (2 * Real.sqrt a)) * (C * M ω ^ d * M ω) :=
        add_le_add (hD.trans (mul_le_mul_of_nonneg_left hpow hC))
          (mul_le_mul hfactor_le hnorm (abs_nonneg _) (by positivity))
      _ = bound ω := by dsimp [bound, K]; rw [pow_succ]; ring
  have hboundInt : Integrable bound μ := (hMom (d + 1)).const_mul K
  have hFint : Integrable (fun ω => G t (X ω + Real.sqrt t • Z ω)) μ :=
    ((hMom d).const_mul C).mono' ((hGmeas t ⟨ht.1.le, ht.2.le⟩).comp (hpathMeas t)).aestronglyMeasurable
      (Eventually.of_forall (hval t ⟨ht.1.le, ht.2.le⟩))
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s ω => G s (X ω + Real.sqrt s • Z ω))
    (F' := fun s ω => timePathDerivative G D (X ω) (Z ω) s)
    (bound := bound) (Ioo_mem_nhds hat htb)
    (by filter_upwards [Ioo_mem_nhds hat htb] with s hs
        exact ((hGmeas s (hsub hs)).comp (hpathMeas s)).aestronglyMeasurable)
    hFint hderivMeas (Eventually.of_forall hbound) hboundInt
    (Eventually.of_forall fun ω s hs => hG.hasDerivAt_path (X ω) (Z ω) ⟨(ha.trans hs.1), hs.2.trans hb1⟩)

end ASDExplicitGamma.Gaussian
