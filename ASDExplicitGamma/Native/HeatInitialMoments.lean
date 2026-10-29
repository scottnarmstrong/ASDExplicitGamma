module

public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Inverse.AnchorAdapter
public import ASDExplicitGamma.Numerics.Native.HistoryConstants
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Model.CutoffVariance
public import ASDExplicitGamma.Gaussian.NormalScaledMoments
public import ASDExplicitGamma.Cold.NativeGraphTraceAverage
public import ASDExplicitGamma.Cold.NativeGraphTraceMoment

/-! Earlier-label native starting bounds for the vector-heat interpolation. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal BigOperators

/-- Hölder interpolation between the first and twentieth moments, in the
source's probability-norm-before-moment form. -/
theorem lintegral_enorm_natPow_le_holder20 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ ≤
      (eLpNorm f 20 μ ^ (20 : ℝ)) ^ (((k : ℝ) - 1) / 19) *
        (∫⁻ ω, ‖f ω‖ₑ ∂μ) ^ ((20 - (k : ℝ)) / 19) := by
  let p : ℝ := ((k : ℝ) - 1) / 19
  let q : ℝ := (20 - (k : ℝ)) / 19
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk20R : (k : ℝ) ≤ 20 := by exact_mod_cast hk20
  have hp : 0 ≤ p := by dsimp [p]; exact div_nonneg (sub_nonneg.mpr hk1R) (by norm_num)
  have hq : 0 ≤ q := by dsimp [q]; exact div_nonneg (sub_nonneg.mpr hk20R) (by norm_num)
  have hpq : p + q = 1 := by dsimp [p, q]; ring
  have hpower : 20 * p + q = (k : ℝ) := by dsimp [p, q]; ring
  have h20p : 0 ≤ 20 * p := by positivity
  have hfun : (fun ω => (‖f ω‖ₑ ^ (20 : ℝ)) ^ p * ‖f ω‖ₑ ^ q) =
      (fun ω => ‖f ω‖ₑ ^ (k : ℝ)) := by
    funext ω
    rw [← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ h20p hq, hpower]
  have hHolder :
      (∫⁻ ω, (‖f ω‖ₑ ^ (20 : ℝ)) ^ p * ‖f ω‖ₑ ^ q ∂μ) ≤
        (∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ) ^ p *
          (∫⁻ ω, ‖f ω‖ₑ ∂μ) ^ q :=
    ENNReal.lintegral_mul_norm_pow_le
      (hf.enorm.pow_const 20) hf.enorm hp hq hpq
  have h20norm : eLpNorm f (20 : ℝ≥0∞) μ = eLpNorm' f 20 μ := by
    simpa using (eLpNorm_eq_eLpNorm' (p := (20 : ℝ≥0∞)) (by norm_num)
      (by norm_num) hf)
  have h20 : eLpNorm f (20 : ℝ≥0∞) μ ^ (20 : ℝ) =
      ∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ := by
    rw [h20norm]
    exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < 20)).symm
  calc
    ∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ =
        ∫⁻ ω, (‖f ω‖ₑ ^ (20 : ℝ)) ^ p * ‖f ω‖ₑ ^ q ∂μ := by
          apply lintegral_congr
          intro ω
          exact (congrFun hfun ω).symm
    _ ≤ (∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ) ^ p *
        (∫⁻ ω, ‖f ω‖ₑ ∂μ) ^ q := hHolder
    _ = _ := by rw [← h20]

/-- The Hölder table with the first moment and L20 norm replaced by explicit
ENNReal caps. -/
theorem lintegral_enorm_natPow_le_holder20_of_caps {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) {A B : ℝ≥0∞}
    (h20 : eLpNorm f 20 μ ≤ A) (hfirst : ∫⁻ ω, ‖f ω‖ₑ ∂μ ≤ B) :
    ∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ ≤
      (A ^ (20 : ℝ)) ^ (((k : ℝ) - 1) / 19) *
        B ^ ((20 - (k : ℝ)) / 19) := by
  let p : ℝ := ((k : ℝ) - 1) / 19
  let q : ℝ := (20 - (k : ℝ)) / 19
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk20R : (k : ℝ) ≤ 20 := by exact_mod_cast hk20
  have hp : 0 ≤ p := by dsimp [p]; exact div_nonneg (sub_nonneg.mpr hk1R) (by norm_num)
  have hq : 0 ≤ q := by dsimp [q]; exact div_nonneg (sub_nonneg.mpr hk20R) (by norm_num)
  have hbase := lintegral_enorm_natPow_le_holder20 hf k hk1 hk20
  have h20pow : eLpNorm f 20 μ ^ (20 : ℝ) ≤ A ^ (20 : ℝ) :=
    ENNReal.rpow_le_rpow h20 (by norm_num)
  have h20outer : (eLpNorm f 20 μ ^ (20 : ℝ)) ^ p ≤
      (A ^ (20 : ℝ)) ^ p := ENNReal.rpow_le_rpow h20pow hp
  have hfirstpow : (∫⁻ ω, ‖f ω‖ₑ ∂μ) ^ q ≤ B ^ q :=
    ENNReal.rpow_le_rpow hfirst hq
  calc
    ∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ ≤
        (eLpNorm f 20 μ ^ (20 : ℝ)) ^ p *
          (∫⁻ ω, ‖f ω‖ₑ ∂μ) ^ q := hbase
    _ ≤ (A ^ (20 : ℝ)) ^ p * B ^ q :=
      mul_le_mul h20outer hfirstpow (by simp) (by simp)
    _ = _ := by rfl

/-- Real-exponent interpolation between the first moment and the twentieth
moment. This is the form needed when the shear estimate asks for exponent
`k/2`, which need not be an integer. -/
theorem nativeHeat_eLpNorm'_interp_1_20 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (q : ℝ) (hq1 : 1 ≤ q) (hq20 : q ≤ 20)
    {A B : ℝ≥0∞} (h20 : eLpNorm' f 20 μ ≤ A) (h1 : eLpNorm' f 1 μ ≤ B) :
    eLpNorm' f q μ ≤ A ^ (20 * (q - 1) / (19 * q)) *
      B ^ ((20 - q) / (19 * q)) := by
  let α : ℝ := (q - 1) / 19
  let β : ℝ := (20 - q) / 19
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hαβ : α + β = 1 := by dsimp [α, β]; ring
  have hpow : 20 * α + β = q := by dsimp [α, β]; ring
  have hfun : (fun ω => (‖f ω‖ₑ ^ (20 : ℝ)) ^ α * ‖f ω‖ₑ ^ β) =
      (fun ω => ‖f ω‖ₑ ^ q) := by
    funext ω
    rw [← ENNReal.rpow_mul,
      ← ENNReal.rpow_add_of_nonneg _ _ (by positivity : 0 ≤ 20 * α) hβ,
      hpow]
  have hHolder :
      (∫⁻ ω, (‖f ω‖ₑ ^ (20 : ℝ)) ^ α * ‖f ω‖ₑ ^ β ∂μ) ≤
        (∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ) ^ α *
          (∫⁻ ω, ‖f ω‖ₑ ∂μ) ^ β :=
    ENNReal.lintegral_mul_norm_pow_le (hf.enorm.pow_const 20) hf.enorm hα hβ hαβ
  have hMom20 :
      ∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ = eLpNorm' f 20 μ ^ (20 : ℝ) :=
    lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num)
  have hMom1 : ∫⁻ ω, ‖f ω‖ₑ ∂μ = eLpNorm' f 1 μ := by
    have hh := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f) (q := (1 : ℝ))
      (μ := μ) (by norm_num)
    simpa using hh
  have h20cap :
      (∫⁻ ω, ‖f ω‖ₑ ^ (20 : ℝ) ∂μ) ≤ A ^ (20 : ℝ) := by
    rw [hMom20]
    exact ENNReal.rpow_le_rpow h20 (by norm_num)
  have h1cap : (∫⁻ ω, ‖f ω‖ₑ ∂μ) ≤ B := by
    rw [hMom1]
    exact h1
  have hαcap := ENNReal.rpow_le_rpow h20cap hα
  have hβcap := ENNReal.rpow_le_rpow h1cap hβ
  have hqMoment : (∫⁻ ω, ‖f ω‖ₑ ^ q ∂μ) ≤
      (A ^ (20 : ℝ)) ^ α * B ^ β := by
    calc
      _ = ∫⁻ ω, (‖f ω‖ₑ ^ (20 : ℝ)) ^ α * ‖f ω‖ₑ ^ β ∂μ := by
        rw [← hfun]
      _ ≤ _ := hHolder
      _ ≤ _ := mul_le_mul hαcap hβcap (by simp) (by simp)
  have hqRoot := ENNReal.rpow_le_rpow hqMoment (by positivity : 0 ≤ 1 / q)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / q),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hqRoot
  rw [← ENNReal.rpow_mul] at hqRoot
  have hAexp : (20 : ℝ) * (α * (1 / q)) = 20 * (q - 1) / (19 * q) := by
    dsimp [α]
    field_simp
  have hBexp : β * (1 / q) = (20 - q) / (19 * q) := by
    dsimp [β]
    field_simp
  rw [hAexp, hBexp] at hqRoot
  simpa [eLpNorm', one_div] using hqRoot

/-- Source shear-moment conversion. If the old trace `T` is nonnegative and
the inverse profile splits as `b + R`, the discriminant bound
`z^2 ≤ 2 (b + R) T` gives the exact two-part estimate used in the initial
heat vector. The rare product `R*T` uses exponents `128` and
`128 k/(256-k) ≤ 20`, so no independence of the old variables is assumed. -/
theorem nativeHeat_shearTraceMoment_of_positive_profile
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z T R : Ω → ℝ) (k : ℕ) (hk2 : 2 ≤ k) (hk20 : k ≤ 20)
    {b : ℝ} {ε Hk H20 : ℝ≥0∞} (hb : 0 ≤ b)
    (hTnonneg : ∀ ω, 0 ≤ T ω) (hRnonneg : ∀ ω, 0 ≤ R ω)
    (hzSq : ∀ᵐ ω ∂μ, z ω ^ 2 ≤ 2 * (b + R ω) * T ω)
    (hTmeas : AEStronglyMeasurable T μ) (hRmeas : AEStronglyMeasurable R μ)
    (hTmoment : eLpNorm' T ((k : ℝ) / 2) μ ≤ Hk)
    (hT20 : eLpNorm' T 20 μ ≤ H20)
    (hR128 : eLpNorm' R 128 μ ≤ ε) :
    eLpNorm' z (k : ℝ) μ ^ 2 ≤
      ENNReal.ofReal (2 * b) * Hk + 2 * ε * H20 := by
  let r : ℝ := (k : ℝ) / 2
  let q : ℝ := 128 * (k : ℝ) / (256 - (k : ℝ))
  let Z2 : Ω → ℝ := fun ω => ‖z ω‖ ^ (2 : ℝ)
  let F1 : Ω → ℝ := fun ω => (2 * b) * T ω
  let RT : Ω → ℝ := fun ω => R ω * T ω
  let F2 : Ω → ℝ := fun ω => 2 * RT ω
  let F : Ω → ℝ := fun ω => F1 ω + F2 ω
  have hkR2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hkR20 : (k : ℝ) ≤ 20 := by exact_mod_cast hk20
  have hrpos : 0 < r := by dsimp [r]; linarith
  have hr1 : 1 ≤ r := by dsimp [r]; nlinarith [hkR2]
  have hqpos : 0 < q := by
    dsimp [q]
    apply div_pos
    · positivity
    · linarith
  have hq20 : q ≤ 20 := by
    dsimp [q]
    apply (div_le_iff₀ (by linarith : 0 < 256 - (k : ℝ))).2
    nlinarith
  have hrlt128 : r < 128 := by dsimp [r]; linarith
  have hHolder : 1 / r = 1 / 128 + 1 / q := by
    dsimp [r, q]
    have hkpos : 0 < (k : ℝ) := by linarith
    field_simp
    ring
  have hZbound : ∀ᵐ ω ∂μ, ‖Z2 ω‖ ≤ ‖F ω‖ := by
    filter_upwards [hzSq] with ω hzSqω
    have hzNorm : ‖Z2 ω‖ = z ω ^ 2 := by
      simp [Z2, Real.norm_eq_abs, sq_abs]
    have hFnonneg : 0 ≤ F ω := by
      dsimp [F, F1, F2, RT]
      positivity [hTnonneg ω, hRnonneg ω, hb]
    calc
      ‖Z2 ω‖ = z ω ^ 2 := hzNorm
      _ ≤ 2 * (b + R ω) * T ω := hzSqω
      _ = (2 * b) * T ω + 2 * (R ω * T ω) := by ring
      _ = F ω := by rfl
      _ = ‖F ω‖ := (Real.norm_of_nonneg hFnonneg).symm
  have hZleF : eLpNorm' Z2 r μ ≤ eLpNorm' F r μ :=
    eLpNorm'_mono_ae (le_of_lt hrpos) hZbound
  have hF1meas : AEStronglyMeasurable F1 μ := by
    dsimp [F1]
    exact hTmeas.const_mul (2 * b)
  have hRTmeas : AEStronglyMeasurable RT μ := by
    dsimp [RT]
    exact hRmeas.mul hTmeas
  have hF2meas : AEStronglyMeasurable F2 μ := by
    dsimp [F2]
    exact hRTmeas.const_mul 2
  have htri : eLpNorm' F r μ ≤ eLpNorm' F1 r μ + eLpNorm' F2 r μ := by
    dsimp [F]
    exact eLpNorm'_add_le hF1meas hF2meas hr1
  have hScale1 : eLpNorm' F1 r μ = ENNReal.ofReal (2 * b) * eLpNorm' T r μ := by
    have heq : F1 = (2 * b) • T := by
      funext ω
      simp [F1, smul_eq_mul]
    rw [heq, eLpNorm'_const_smul (2 * b) hrpos]
    rw [Real.enorm_eq_ofReal (mul_nonneg (by norm_num) hb)]
  have hScale2 : eLpNorm' F2 r μ = 2 * eLpNorm' RT r μ := by
    have heq : F2 = (2 : ℝ) • RT := by
      funext ω
      simp [F2, smul_eq_mul]
    rw [heq, eLpNorm'_const_smul (2 : ℝ) hrpos]
    rw [Real.enorm_eq_ofReal (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  have hmul : eLpNorm' RT r μ ≤ eLpNorm' R 128 μ * eLpNorm' T q μ := by
    have hh := eLpNorm'_le_eLpNorm'_mul_eLpNorm'
      (p := (128 : ℝ)) (q := q) (r := r) (f := R) (g := T)
      hRmeas hTmeas (fun x y : ℝ => x * y) (1 : NNReal)
      (by
        filter_upwards [] with ω
        simp)
      hrpos hrlt128 hHolder
    simpa [RT] using hh
  have hTq : eLpNorm' T q μ ≤ H20 := by
    calc
      eLpNorm' T q μ ≤ eLpNorm' T 20 μ :=
        eLpNorm'_le_eLpNorm'_of_exponent_le hqpos hq20 μ hTmeas
      _ ≤ H20 := hT20
  have hRTcap : eLpNorm' RT r μ ≤ ε * H20 := by
    calc
      eLpNorm' RT r μ ≤ eLpNorm' R 128 μ * eLpNorm' T q μ := hmul
      _ ≤ ε * H20 := mul_le_mul hR128 hTq (by positivity) (by positivity)
  have hFcap : eLpNorm' F r μ ≤ ENNReal.ofReal (2 * b) * Hk + 2 * ε * H20 := by
    calc
      eLpNorm' F r μ ≤ eLpNorm' F1 r μ + eLpNorm' F2 r μ := htri
      _ ≤ ENNReal.ofReal (2 * b) * Hk + 2 * (ε * H20) := by
        apply add_le_add
        · rw [hScale1]
          exact mul_le_mul_of_nonneg_left hTmoment bot_le
        · rw [hScale2]
          exact mul_le_mul_of_nonneg_left hRTcap bot_le
      _ = ENNReal.ofReal (2 * b) * Hk + 2 * ε * H20 := by ring
  have hZ2norm : eLpNorm' Z2 r μ = eLpNorm' z (k : ℝ) μ ^ (2 : ℕ) := by
    calc
      eLpNorm' Z2 r μ = eLpNorm' (fun ω => ‖z ω‖ ^ (2 : ℝ)) r μ := rfl
      _ = eLpNorm' z (r * 2) μ ^ 2 := eLpNorm'_norm_rpow z r 2 (by norm_num)
      _ = eLpNorm' z (k : ℝ) μ ^ (2 : ℝ) := by
        have hrEq : r * 2 = (k : ℝ) := by dsimp [r]; ring
        rw [hrEq]
      _ = eLpNorm' z (k : ℝ) μ ^ (2 : ℕ) := by
        exact ENNReal.rpow_natCast _ 2
  rw [← hZ2norm]
  exact hZleF.trans hFcap

end ASDExplicitGamma.Native
