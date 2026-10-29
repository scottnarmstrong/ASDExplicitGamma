module

public import ASDExplicitGamma.Native.HeatInitialRefinedRare
public import ASDExplicitGamma.Native.HeatInitialRefinedGaussianGen
public import ASDExplicitGamma.Native.HeatInitialRefinedIndepGen

/-! The depth-four rare quadratic row for `ns` shells. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open Algsuperdiff.Section3.Provider.BadEvents Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section4.Provider.Annular
open scoped ENNReal NNReal BigOperators Nat
set_option linter.constructorNameAsVariable false

private theorem nativeHeat_standardEvenMoment_le_gm (k : ℕ)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) ≤
      ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) ^ k := by
  have hdouble : Nat.factorial (2 * k) =
      (2 ^ k * Nat.factorial k) * (2 * k - 1)‼ := by
    have h := Nat.factorial_eq_mul_doubleFactorial (2 * k - 1)
    have hidx : 2 * k - 1 + 1 = 2 * k := by omega
    rw [hidx, Nat.doubleFactorial_two_mul] at h
    exact h
  have hdoubleR : (Nat.factorial (2 * k) : ℝ) =
      (2 : ℝ) ^ k * (Nat.factorial k : ℝ) * ((2 * k - 1)‼ : ℝ) := by
    exact_mod_cast hdouble
  have hratio : ((2 * k - 1)‼ : ℝ) =
      ((Nat.factorial (2 * k) : ℝ) /
        ((2 : ℝ) ^ k * (Nat.factorial k : ℝ))) := by
    have hden : (2 : ℝ) ^ k * (Nat.factorial k : ℝ) ≠ 0 := by positivity
    rw [hdoubleR]
    field_simp
  have hstd : (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 1) =
      ((Nat.factorial (2 * k) : ℝ) /
        ((2 : ℝ) ^ k * (Nat.factorial k : ℝ))) := by
    rw [normal_even_moment_eq_doubleFactorial k hk1, hratio]
  have hgmQ :
      (Nat.factorial (2 * k) : ℚ) / (2 ^ k * Nat.factorial k) ≤
        (nativeHeatParametersData.gm.getD k 0) ^ k := by
    interval_cases k
    · simpa using nativeHeatGM01_powers.2
    · simpa using nativeHeatGM02_powers.2
    · simpa using nativeHeatGM03_powers.2
    · simpa using nativeHeatGM04_powers.2
    · simpa using nativeHeatGM05_powers.2
    · simpa using nativeHeatGM06_powers.2
    · simpa using nativeHeatGM07_powers.2
    · simpa using nativeHeatGM08_powers.2
    · simpa using nativeHeatGM09_powers.2
    · simpa using nativeHeatGM10_powers.2
    · simpa using nativeHeatGM11_powers.2
    · simpa using nativeHeatGM12_powers.2
    · simpa using nativeHeatGM13_powers.2
    · simpa using nativeHeatGM14_powers.2
    · simpa using nativeHeatGM15_powers.2
    · simpa using nativeHeatGM16_powers.2
    · simpa using nativeHeatGM17_powers.2
    · simpa using nativeHeatGM18_powers.2
    · simpa using nativeHeatGM19_powers.2
    · simpa using nativeHeatGM20_powers.2
  have hgmR :
      ((Nat.factorial (2 * k) : ℝ) /
        ((2 : ℝ) ^ k * (Nat.factorial k : ℝ))) ≤
        ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) ^ k := by
    have hcast :
        (((Nat.factorial (2 * k) : ℚ) / (2 ^ k * Nat.factorial k) : ℚ) : ℝ) ≤
          (((nativeHeatParametersData.gm.getD k 0) ^ k : ℚ) : ℝ) := by
      exact_mod_cast hgmQ
    simpa using hcast
  rw [hstd]
  exact hgmR

private theorem nativeHeat_gaussianEvenMoment_le_gm (v : ℝ≥0) (k : ℕ)
    (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal 0 v) ≤
      (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) * (v : ℝ)) ^ k := by
  rw [gaussianReal_eq_map_sqrt v, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]
  have hscale : Real.sqrt (v : ℝ) ^ (2 * k) = (v : ℝ) ^ k := by
    calc
      Real.sqrt (v : ℝ) ^ (2 * k) = (Real.sqrt (v : ℝ) ^ 2) ^ k := by rw [pow_mul]
      _ = (v : ℝ) ^ k := congrArg (fun z : ℝ => z ^ k) (Real.sq_sqrt v.property)
  rw [hscale]
  have hbound := mul_le_mul_of_nonneg_left
    (nativeHeat_standardEvenMoment_le_gm k hk1 hk20) (pow_nonneg v.property k)
  calc
    _ ≤ (v : ℝ) ^ k * (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) ^ k) := hbound
    _ = (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) ^ k) * (v : ℝ) ^ k := by ring

private theorem nativeHeat_gm_nonneg (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    0 ≤ ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) := by
  interval_cases k <;> first
    | exact_mod_cast nativeHeatGM01_powers.1
    | exact_mod_cast nativeHeatGM02_powers.1
    | exact_mod_cast nativeHeatGM03_powers.1
    | exact_mod_cast nativeHeatGM04_powers.1
    | exact_mod_cast nativeHeatGM05_powers.1
    | exact_mod_cast nativeHeatGM06_powers.1
    | exact_mod_cast nativeHeatGM07_powers.1
    | exact_mod_cast nativeHeatGM08_powers.1
    | exact_mod_cast nativeHeatGM09_powers.1
    | exact_mod_cast nativeHeatGM10_powers.1
    | exact_mod_cast nativeHeatGM11_powers.1
    | exact_mod_cast nativeHeatGM12_powers.1
    | exact_mod_cast nativeHeatGM13_powers.1
    | exact_mod_cast nativeHeatGM14_powers.1
    | exact_mod_cast nativeHeatGM15_powers.1
    | exact_mod_cast nativeHeatGM16_powers.1
    | exact_mod_cast nativeHeatGM17_powers.1
    | exact_mod_cast nativeHeatGM18_powers.1
    | exact_mod_cast nativeHeatGM19_powers.1
    | exact_mod_cast nativeHeatGM20_powers.1

/-- A degree-k moment is controlled by the L128 norm on a probability space. -/
private theorem nativeHeat_lintegral_enorm_natPow_le_eLpNorm128
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (k : ℕ)
    (hk1 : 1 ≤ k) (hk128 : k ≤ 128) :
    ∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ ≤ eLpNorm f 128 μ ^ k := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk128R : (k : ℝ) ≤ 128 := by exact_mod_cast hk128
  have hmono : eLpNorm' f (k : ℝ) μ ≤ eLpNorm' f 128 μ :=
    eLpNorm'_le_eLpNorm'_of_exponent_le hkpos hk128R μ hf
  have h128 : eLpNorm f 128 μ = eLpNorm' f 128 μ := by
    simpa using (eLpNorm_eq_eLpNorm' (p := (128 : ℝ≥0∞))
      (by norm_num) (by norm_num) hf)
  calc
    _ = eLpNorm' f (k : ℝ) μ ^ (k : ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos
    _ ≤ eLpNorm' f 128 μ ^ (k : ℝ) :=
      ENNReal.rpow_le_rpow hmono (by positivity)
    _ = eLpNorm f 128 μ ^ k := by rw [← h128, ENNReal.rpow_natCast]

/-- A finite average is a contraction on every real `Lᵖ`, `p ≥ 1`. This is
stated for an abstract finite index so consumers can use large structured
partitions without unfolding their enumeration. -/
private theorem nativeHeat_eLpNorm'_average_le
    {α ι : Type*} [MeasurableSpace α] [Fintype ι] [Nonempty ι]
    {μ : Measure α} {p cap : ℝ} (hp : 1 ≤ p) (hcap0 : 0 ≤ cap)
    (f : ι → α → ℝ) (hf : ∀ i, Measurable (f i))
    (hbound : ∀ i, eLpNorm' (f i) p μ ≤ ENNReal.ofReal cap) :
    eLpNorm' (fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ω) p μ ≤
      ENNReal.ofReal cap := by
  let N : ℝ := (Fintype.card ι : ℝ)
  let S : α → ℝ := ∑ i, f i
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  have hN0 : 0 ≤ N := hNpos.le
  have hNinv0 : 0 ≤ N⁻¹ := inv_nonneg.mpr hN0
  have hsumLp : eLpNorm' S p μ ≤ ∑ i, eLpNorm' (f i) p μ := by
    change eLpNorm' (∑ i, f i) p μ ≤ _
    exact eLpNorm'_sum_le (μ := μ) (f := f) (s := Finset.univ)
      (fun i _ => (hf i).aestronglyMeasurable) hp
  have hsumCap : ∑ i, eLpNorm' (f i) p μ ≤ ENNReal.ofReal (N * cap) := by
    calc
      _ ≤ ∑ i, ENNReal.ofReal cap := Finset.sum_le_sum fun i _ => hbound i
      _ = (Fintype.card ι : ℝ≥0∞) * ENNReal.ofReal cap := by simp
      _ = ENNReal.ofReal (N * cap) := by
        rw [ENNReal.ofReal_mul hN0]
        simp [N, ENNReal.ofReal_natCast]
  have hpoint : (fun ω => N⁻¹ * S ω) = N⁻¹ • S := by
    funext ω
    simp [smul_eq_mul]
  have hscaleLp :
      eLpNorm' (N⁻¹ • S) p μ = ENNReal.ofReal N⁻¹ * eLpNorm' S p μ :=
    by
      simpa only [Real.enorm_eq_ofReal hNinv0] using
        (eLpNorm'_const_smul N⁻¹ (by positivity : 0 < p) (f := S) (μ := μ))
  have hsumBound : eLpNorm' S p μ ≤ ENNReal.ofReal (N * cap) :=
    hsumLp.trans hsumCap
  have havgSmul : eLpNorm' (N⁻¹ • S) p μ ≤ ENNReal.ofReal cap := by
    rw [hscaleLp]
    calc
      _ ≤ ENNReal.ofReal N⁻¹ * ENNReal.ofReal (N * cap) :=
        mul_le_mul_of_nonneg_left hsumBound (by positivity)
      _ = ENNReal.ofReal cap := by
        rw [← ENNReal.ofReal_mul hNinv0]
        congr 1
        field_simp [hNpos.ne']
  have havg :
      eLpNorm' (fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ω) p μ ≤
        ENNReal.ofReal cap := by
    rw [show (fun ω => (Fintype.card ι : ℝ)⁻¹ * ∑ i, f i ω) =
      (fun ω => N⁻¹ * S ω) by
        funext ω
        simp [N, S, Fintype.sum_apply]]
    rw [hpoint]
    simpa [N, S] using havgSmul
  exact havg

/-- The actual normalized fresh coordinate at a depth-ten child has the configured scalar
Gaussian moments, at the heat-inflated variance. -/
theorem nativeHeatQ3RefinedZ_moment_le_gmGen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hstate : nativeInductionState M h (m + 1))
    (ij : Fin (3^10) × Fin (3^10)) (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceZGen ns M m ω (finProdFinEquiv ij)‖ₑ ^
        (2 * (k : ℝ)) ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
        ((nativeHeatGenVariance ns) : ℝ)) ^ (k : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let K := nativeHeatQ3GridCenterSet 10
  let shells : Fin ns → ℤ := fun d => ((d.val + 2 : ℕ) : ℤ) - ((10 : ℕ) : ℤ)
  let T : Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 := fun ω =>
    ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma (m + 10)
      (Cutoff.translateCutoffSample
        (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) ω)
  let S : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    modelBand K shells ω (nativeHeatQ3GridCenterPoint 10 ij)
  let B : ℝ := Real.rpow 3 (M.gamma * ((m + 10 : ℤ) : ℝ))
  let σ : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ)
  let α : ℝ := Real.sqrt (1 + (nativeHeatTheta : ℝ)) * B / σ
  let x : Vec 2 := q3GridCenterVector 10 ij
  let cov : Fin ns → ℝ := fun d => q3ShellCovariance M h (shells d) x x
  let vcan : ℝ≥0 := ∑ d, Real.toNNReal (cov d)
  let vscaled : ℝ≥0 := ⟨α ^ 2, sq_nonneg α⟩ * vcan
  let Z : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    nativeHeatQ3RefinedCarrierSourceZGen ns M m ω (finProdFinEquiv ij)
  let F : ℝ → ℝ≥0∞ := fun y => ‖y‖ₑ ^ (2 * (k : ℝ))
  have hθ : 0 ≤ 1 + (nativeHeatTheta : ℝ) := by norm_num [nativeHeatTheta]
  have hshells : Function.Injective shells := by
    intro d₁ d₂ hde
    apply Fin.ext
    dsimp [shells] at hde
    omega
  have hSmeas : Measurable S := by
    dsimp [S, K]
    exact (ContinuousMap.evalCLM ℝ (nativeHeatQ3GridCenterPoint 10 ij)).continuous.measurable.comp
      (measurable_modelBand (nativeHeatQ3GridCenterSet 10) shells)
  have hcanonical : μ.map S = gaussianReal 0 vcan := by
    have h := nativeHeat_q3FiniteBand_gridCombination_law M h hM
      (b := ns) shells hshells 10 (J := Unit)
      (x := fun _ : Unit => ij) (t := fun _ : Unit => (1 : ℝ))
    simpa [μ, S, K, shells, vcan, cov, x] using h
  have hBsq : B ^ 2 = (3 : ℝ) ^ (2 * M.gamma * ((m + 10 : ℤ) : ℝ)) := by
    dsimp [B]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  have hZ (ω : Cutoff.CutoffSample 2) : Z ω = α * S (T ω) := by
    dsimp only [Z, α, σ, B, S, T, K, shells]
    unfold nativeHeatQ3RefinedCarrierSourceZGen
    rw [nativeHeatQ3RefinedFreshRaw_eq_scaled_bandGen ns M m ω ij]
    ring
  have hvcan : (vcan : ℝ) = ∑ d, cov d := by
    rw [NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact Real.coe_toNNReal _
      (q3ShellCovariance_nonnegative M h (shells d) x x)
  have hscaleCap : α ^ 2 = (1 + (nativeHeatTheta : ℝ)) *
      ((3 : ℝ) ^ (2 * M.gamma * ((m + 10 : ℤ) : ℝ)) / σ ^ 2) := by
    dsimp only [α]
    rw [div_pow, mul_pow, Real.sq_sqrt hθ, hBsq]
    ring
  let e : ℝ := (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))
  have hterm (d : Fin ns) : α ^ 2 * cov d ≤ (1 + (nativeHeatTheta : ℝ)) * e := by
    have hcov : cov d = (h * (3 : ℝ) ^ (M.gamma * (shells d : ℝ))) ^ 2 := by
      dsimp [cov, x]
      rw [q3ShellCovariance_diagonal]
      rw [nativeHeat_q3ShellAmplitude_sq]
    have hsource := nativeHeatRefined_shellCapGen ns M h (m + 1) 1 (by norm_num) d hstate
    have hlabel : (((m + 1 : ℤ) + 9 : ℤ) : ℝ) = ((m + 10 : ℤ) : ℝ) := by
      push_cast; ring
    rw [hlabel] at hsource
    rw [hscaleCap, hcov]
    have := mul_le_mul_of_nonneg_left hsource hθ
    simp only [one_mul] at this
    calc
      _ = (1 + (nativeHeatTheta : ℝ)) *
          ((3 : ℝ) ^ (2 * M.gamma * ((m + 10 : ℤ) : ℝ)) / σ ^ 2 *
            (h * (3 : ℝ) ^ (M.gamma * (shells d : ℝ))) ^ 2) := by ring
      _ ≤ _ := by simpa [σ, shells, e] using this
  have hvscaled : (vscaled : ℝ) ≤ ((nativeHeatGenVariance ns) : ℝ) := by
    change α ^ 2 * (vcan : ℝ) ≤ _
    rw [hvcan]
    calc
      α ^ 2 * ∑ d, cov d = ∑ d, α ^ 2 * cov d := by rw [Finset.mul_sum]
      _ ≤ ∑ d : Fin ns, (1 + (nativeHeatTheta : ℝ)) * e :=
        Finset.sum_le_sum fun d hd => hterm d
      _ = (ns : ℝ) * ((1 + (nativeHeatTheta : ℝ)) * e) := by simp
      _ ≤ ((nativeHeatGenVariance ns) : ℝ) := by
        simpa [e] using nativeHeat009_scaledVariance_capGen ns hnum M hgamma
  have hmapScaled : (μ.map S).map (fun y : ℝ => α * y) =
      μ.map (fun ω => α * S ω) := by
    rw [show (fun ω => α * S ω) = (fun y : ℝ => α * y) ∘ S by rfl]
    exact Measure.map_map (μ := μ) (g := fun y : ℝ => α * y) (f := S)
      (by fun_prop) hSmeas
  have hscaled : μ.map (fun ω => α * S ω) = gaussianReal 0 vscaled := by
    calc
      _ = (μ.map S).map (fun y : ℝ => α * y) := hmapScaled.symm
      _ = gaussianReal 0 vscaled := by
        rw [hcanonical, gaussianReal_map_const_mul]
        simp only [mul_zero]
        rfl
  have hFmeas : Measurable F := by
    dsimp [F]
    exact ENNReal.continuous_rpow_const.measurable.comp measurable_enorm
  let G : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω => F (α * S ω)
  have hGmeas : Measurable G := hFmeas.comp (measurable_const.mul hSmeas)
  have hshift := nativeHeat_cutoff_lintegral_translate_scale_shift M
    (nativeHeatQ3ParentOrigin (originCube 2 (m + 10))) (m + 10) G hGmeas
  have hmapMoment :
      ∫⁻ ω, F (α * S ω) ∂μ = ∫⁻ y, F y ∂gaussianReal 0 vscaled := by
    rw [← hscaled]
    exact (MeasureTheory.lintegral_map hFmeas (measurable_const.mul hSmeas)).symm
  have hkpow : ENNReal.ofReal (2 * (k : ℝ)) = (2 * k : ℕ) := by
    rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring]
    simp
  have hmem : MemLp (id : ℝ → ℝ) (2 * k : ℕ) (gaussianReal 0 vscaled) := by
    rw [← hkpow]; exact memLp_id_gaussianReal' _ ENNReal.ofReal_ne_top
  have hpowNonneg (y : ℝ) : 0 ≤ y ^ (2 * k) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg y) k
  have hInt : Integrable (fun y : ℝ => y ^ (2 * k)) (gaussianReal 0 vscaled) := by
    have h := hmem.integrable_norm_pow (p := 2 * k) (by omega : 2 * k ≠ 0)
    convert h using 1
    ext y
    rw [Real.norm_eq_abs]
    calc
      y ^ (2 * k) = |y ^ (2 * k)| := (abs_of_nonneg (hpowNonneg y)).symm
      _ = |y| ^ (2 * k) := abs_pow y (2 * k)
  have hpointF (y : ℝ) : F y = ENNReal.ofReal (y ^ (2 * k)) := by
    dsimp [F]
    rw [show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
      ENNReal.rpow_natCast]
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg y)]
    congr 1
    calc
      |y| ^ (2 * k) = |y ^ (2 * k)| := (abs_pow y (2 * k)).symm
      _ = y ^ (2 * k) := abs_of_nonneg (hpowNonneg y)
  have htoENN :
      ∫⁻ y, F y ∂gaussianReal 0 vscaled =
        ENNReal.ofReal (∫ y, y ^ (2 * k) ∂gaussianReal 0 vscaled) := by
    calc
      _ = ∫⁻ y, ENNReal.ofReal (y ^ (2 * k)) ∂gaussianReal 0 vscaled := by
        apply lintegral_congr
        intro y
        exact hpointF y
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hInt
        (Filter.Eventually.of_forall fun y => hpowNonneg y)).symm
  have hgm0 := nativeHeat_gm_nonneg k hk1 hk20
  have hmoment := nativeHeat_gaussianEvenMoment_le_gm vscaled k hk1 hk20
  have hvar0 : 0 ≤ ((nativeHeatGenVariance ns) : ℝ) :=
    (NNReal.coe_nonneg vscaled).trans hvscaled
  have hrealCap : 0 ≤
      ((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
        ((nativeHeatGenVariance ns) : ℝ) := mul_nonneg hgm0 hvar0
  have hvarianceMoment := mul_le_mul_of_nonneg_left hvscaled hgm0
  have hpowerMoment :
      (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) * (vscaled : ℝ)) ^ k ≤
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ)) ^ k :=
    pow_le_pow_left₀ (mul_nonneg hgm0 (NNReal.coe_nonneg vscaled)) hvarianceMoment k
  calc
    _ = ∫⁻ ω, F (Z ω) ∂μ := rfl
    _ = ∫⁻ ω, G (T ω) ∂μ := by
      apply lintegral_congr
      intro ω
      simp only [G, hZ ω]
    _ = ∫⁻ ω, G ω ∂μ := hshift
    _ = ∫⁻ y, F y ∂gaussianReal 0 vscaled := hmapMoment
    _ ≤ ENNReal.ofReal
        ((((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ)) ^ k) := by
      rw [htoENN]
      exact ENNReal.ofReal_le_ofReal (hmoment.trans hpowerMoment)
    _ = ENNReal.ofReal
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ)) ^ (k : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hrealCap (by positivity)]
      rw [Real.rpow_natCast]

theorem nativeHeatQ3RefinedFreshRaw_measurableGen (ns : ℕ) [NeZero ns] (m : ℤ) :
    Measurable (nativeHeatQ3RefinedCarrierSourceFreshRawGen ns m) := by
  unfold nativeHeatQ3RefinedCarrierSourceFreshRawGen
  exact (nativeHeatQ3RefinedCarrierSourceCenterMap m).continuous.measurable.comp
    (measurable_modelBand (nativeHeatQ3RefinedCarrierDomain m)
      (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns))

theorem nativeHeatQ3RefinedFreshRaw_shellLocalGen (ns : ℕ) [NeZero ns] (m : ℤ) :
    @Measurable (Cutoff.CutoffSample 2) (nativeHeatQ3RefinedCarrierIndex → ℝ)
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + ns + 1))).comap Subtype.val)
      inferInstance (nativeHeatQ3RefinedCarrierSourceFreshRawGen ns m) := by
  classical
  let J : Set ℤ := Set.Icc (m + 2) (m + ns + 1)
  let K := nativeHeatQ3RefinedCarrierDomain m
  letI : MeasurableSpace (Cutoff.CutoffSample 2) :=
    (Cutoff.shellIndexSigma J).comap Subtype.val
  have hlabel (d : Fin ns) : nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d ∈ J :=
    nativeHeatQ3RefinedCarrierPhysicalShellsGen_mem m d
  have hcoord (d : Fin ns) : @Measurable (Cutoff.CutoffSample 2) (ShellField 2)
      ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance
      (fun ω => ω.1 (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d)) := by
    apply measurable_iff_comap_le.mpr
    exact MeasurableSpace.comap_le_comap_of_eq_comp
      (fun ξ : Cutoff.ShellSeq 2 => ξ (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns d))
      (Cutoff.measurable_shellCoordinate_shellIndexSigma (hlabel d))
      (by funext ω; rfl)
  have hband : @Measurable (Cutoff.CutoffSample 2) (C(K, ℝ))
      ((Cutoff.shellIndexSigma J).comap Subtype.val) inferInstance
      (fun ω => modelBand K (nativeHeatQ3RefinedCarrierPhysicalShellsGen m ns) ω) := by
    unfold Gaussian.modelBand
    apply Finset.measurable_sum
    intro d hd
    exact (measurable_shellFieldScalarRestriction K).comp (hcoord d)
  unfold nativeHeatQ3RefinedCarrierSourceFreshRawGen
  exact (nativeHeatQ3RefinedCarrierSourceCenterMap m).continuous.measurable.comp hband

/-- The depth-four-root rare quadratic of the refined source start. -/
noncomputable def nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4Gen (ns : ℕ) [NeZero ns]
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  2 * ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
    ∑ i : nativeHeatQ3RefinedCarrierIndex,
      nativeHeatOldInverseRemainderDepth4 M
        (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
          (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i) ^ 2)

theorem nativeHeatQ3RefinedZ_measurableGen (ns : ℕ) [NeZero ns] (M : ABKModel 2) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    Measurable (fun ω => nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i) := by
  unfold nativeHeatQ3RefinedCarrierSourceZGen
  exact (((measurable_pi_apply i).comp
    (nativeHeatQ3RefinedFreshRaw_measurableGen ns m)).const_mul _).div_const _

theorem nativeHeatQ3RefinedZ_shellLocalGen (ns : ℕ) [NeZero ns] (M : ABKModel 2) (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    @Measurable (Cutoff.CutoffSample 2) ℝ
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + ns + 1))).comap Subtype.val)
      inferInstance (fun ω => nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i) := by
  letI : MeasurableSpace (Cutoff.CutoffSample 2) :=
    (Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + ns + 1))).comap Subtype.val
  unfold nativeHeatQ3RefinedCarrierSourceZGen
  exact (((measurable_pi_apply i).comp
    (nativeHeatQ3RefinedFreshRaw_shellLocalGen ns m)).const_mul _).div_const _

/-- One child: the depth-four OLD remainder times the squared normalized fresh centre. -/
theorem nativeHeatQ3RefinedRareCell_moment_leGen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (i : nativeHeatQ3RefinedCarrierIndex) (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatOldInverseRemainderDepth4 M
        (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
          (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i) ^ 2‖ₑ ^ (k : ℝ)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal ((inverseBankReserve .localInverse : ℝ) *
          (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let R : Cutoff.CutoffSample 2 → ℝ := nativeHeatOldInverseRemainderDepth4 M Q (m + 1)
  let Z : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i
  have hchild : Q.scale + 1 = m + 1 := by
    have := nativeHeatQ3RefinedCarrierChild_scale m i
    simp only [Q]; omega
  have hprofile := nativeHeatRefined_oldInverseTraceProfileDepth4_of_states
    M h hM hgamma Q (m + 1) hchild hpast
  have hRmeas : Measurable R := by simpa [R] using hprofile.1
  have hRlocal : @Measurable (Cutoff.CutoffSample 2) ℝ
      (Cutoff.cutoffSampleLocalSigma M (m + 1) Set.univ) (borel ℝ) R := by
    simpa [R] using (nativeHeatRefined_oldInverseRemainderDepth4_local M Q (m + 1)).mono
      (cutoffSampleLocalSigma_mono M le_rfl
        (Set.subset_univ (cubeSet Q))) le_rfl
  have hZmeas : Measurable Z := nativeHeatQ3RefinedZ_measurableGen ns M m i
  have hZlocal : @Measurable (Cutoff.CutoffSample 2) ℝ
      ((Cutoff.shellIndexSigma (Set.Icc (m + 2) (m + ns + 1))).comap Subtype.val)
      inferInstance Z := nativeHeatQ3RefinedZ_shellLocalGen ns M m i
  have hJ : Disjoint (Set.Iic (m + 1)) (Set.Icc (m + 2) (m + ns + 1)) := by
    apply Set.disjoint_left.mpr
    intro z hz hzJ
    rcases hzJ with ⟨hzLo, hzHi⟩
    change z ≤ m + 1 at hz
    omega
  have hIndep : IndepFun R Z μ := by
    simpa [μ] using nativeHeat_cutoffLocal_freshBlock_independent M (m + 1)
      (Set.Icc (m + 2) (m + ns + 1)) hJ R hRlocal Z hZlocal
  have hR0 : ∀ ω, 0 ≤ R ω := by simpa [R] using hprofile.2.1
  let RP : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω => ENNReal.ofReal (R ω ^ k)
  let ZP : Cutoff.CutoffSample 2 → ℝ≥0∞ := fun ω => ENNReal.ofReal (Z ω ^ (2 * k))
  have hRPmeas : Measurable RP := ENNReal.measurable_ofReal.comp (hRmeas.pow_const k)
  have hZPmeas : Measurable ZP :=
    ENNReal.measurable_ofReal.comp (hZmeas.pow_const (2 * k))
  have hIndPow : IndepFun RP ZP μ := by
    change (fun ω => ENNReal.ofReal (R ω ^ k)) ⟂ᵢ[μ]
      (fun ω => ENNReal.ofReal (Z ω ^ (2 * k)))
    exact hIndep.comp
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const k))
      (ENNReal.measurable_ofReal.comp (measurable_id.pow_const (2 * k)))
  have hRmoment :
      ∫⁻ ω, ‖R ω‖ₑ ^ (k : ℝ) ∂μ ≤
        ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) ^ (k : ℝ) := by
    have h128 := nativeHeat_lintegral_enorm_natPow_le_eLpNorm128
      (μ := μ) (f := R) hRmeas.aestronglyMeasurable k hk1
      (le_trans hk20 (by norm_num))
    have hcap : eLpNorm R 128 μ ≤
        ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) := by
      simpa [R, μ] using hprofile.2.2.2
    have hpow := ENNReal.rpow_le_rpow hcap (by positivity : 0 ≤ (k : ℝ))
    have hpowNat : eLpNorm R 128 μ ^ k ≤
        ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) ^ k := by
      simpa [ENNReal.rpow_natCast] using hpow
    simpa [ENNReal.rpow_natCast] using h128.trans hpowNat
  have hZmoment :
      ∫⁻ ω, ‖Z ω‖ₑ ^ (2 * (k : ℝ)) ∂μ ≤
        ENNReal.ofReal
          ((((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ) := by
    obtain ⟨ij, hij⟩ := finProdFinEquiv.surjective i
    have := nativeHeatQ3RefinedZ_moment_le_gmGen ns hnum M h hM hgamma m hstate ij k hk1 hk20
    rw [hij] at this
    simpa [Z, μ] using this
  have hRPpoint (ω : Cutoff.CutoffSample 2) : RP ω = ‖R ω‖ₑ ^ (k : ℝ) := by
    dsimp [RP]
    rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal (hR0 ω), ENNReal.ofReal_pow (hR0 ω)]
  have hZPpoint (ω : Cutoff.CutoffSample 2) : ZP ω = ‖Z ω‖ₑ ^ (2 * (k : ℝ)) := by
    dsimp [ZP]
    have hpowNonneg : 0 ≤ Z ω ^ (2 * k) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg (Z ω)) k
    calc
      ENNReal.ofReal (Z ω ^ (2 * k)) = ‖Z ω ^ (2 * k)‖ₑ := by
        symm
        exact Real.enorm_eq_ofReal hpowNonneg
      _ = ‖Z ω‖ₑ ^ (2 * k) := by rw [enorm_pow]
      _ = ‖Z ω‖ₑ ^ (2 * (k : ℝ)) := by
        rw [show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
          ENNReal.rpow_natCast]
  have hRPint : ∫⁻ ω, RP ω ∂μ ≤
      ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) ^ (k : ℝ) := by
    rw [lintegral_congr hRPpoint]
    exact hRmoment
  have hZPint : ∫⁻ ω, ZP ω ∂μ ≤
      ENNReal.ofReal
        ((((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ) := by
    rw [lintegral_congr hZPpoint]
    exact hZmoment
  have hProductPoint (ω : Cutoff.CutoffSample 2) :
      ‖R ω * Z ω ^ 2‖ₑ ^ (k : ℝ) = RP ω * ZP ω := by
    have hnonneg : 0 ≤ R ω * Z ω ^ 2 := mul_nonneg (hR0 ω) (sq_nonneg _)
    dsimp [RP, ZP]
    rw [ENNReal.rpow_natCast, Real.enorm_eq_ofReal hnonneg,
      ← ENNReal.ofReal_pow hnonneg, mul_pow, pow_mul,
      ENNReal.ofReal_mul (pow_nonneg (hR0 ω) k)]
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (f := RP) (g := ZP) hRPmeas hZPmeas hIndPow
  have hε0 : 0 ≤ (inverseBankReserve .localInverse : ℝ) := by
    norm_num [inverseBankReserve]
  have hgm0 := nativeHeat_gm_nonneg k hk1 hk20
  have hvariance0 : 0 ≤ ((nativeHeatGenVariance ns) : ℝ) := by
    exact_mod_cast hnum.variance_nonneg
  have hgauss0 : 0 ≤ (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
      ((nativeHeatGenVariance ns) : ℝ)) := mul_nonneg hgm0 hvariance0
  calc
    _ = ∫⁻ ω, RP ω * ZP ω ∂μ := by
      apply lintegral_congr
      intro ω
      exact hProductPoint ω
    _ = (∫⁻ ω, RP ω ∂μ) * ∫⁻ ω, ZP ω ∂μ := hfactor
    _ ≤ ENNReal.ofReal (inverseBankReserve .localInverse : ℝ) ^ (k : ℝ) *
        ENNReal.ofReal
          ((((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ) :=
          mul_le_mul hRPint hZPint (by positivity) (by positivity)
    _ = ENNReal.ofReal ((inverseBankReserve .localInverse : ℝ) *
          (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
            ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ) := by
      rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ (k : ℝ)),
        ← ENNReal.ofReal_mul hε0]

/-- The restated rare bound: depth-four local roots at cutoff `m+1`. -/
theorem nativeHeatQ3RefinedCarrierSourceRareQuadraticMoment_le_009_depth4_Gen (ns : ℕ) [NeZero ns] (hnum : NativeHeatGenNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (hgamma : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h (m + 1))
    (hpast : ∀ n < m + 1, nativeInductionState M h n)
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ∫⁻ ω, ‖nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4Gen ns M m ω‖ₑ ^
        (k : ℝ) ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (2 * (inverseBankReserve .localInverse : ℝ) *
        (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
          ((nativeHeatGenVariance ns) : ℝ))) ^ (k : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let cap : ℝ := (inverseBankReserve .localInverse : ℝ) *
    (((nativeHeatParametersData.gm.getD k 0 : ℚ) : ℝ) *
      ((nativeHeatGenVariance ns) : ℝ))
  let U : nativeHeatQ3RefinedCarrierIndex → Cutoff.CutoffSample 2 → ℝ := fun i ω =>
    nativeHeatOldInverseRemainderDepth4 M
      (nativeHeatQ3RefinedCarrierChild m i) (m + 1) ω *
        (nativeHeatQ3RefinedCarrierSourceZGen ns M m ω i) ^ 2
  let S : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑ i, U i ω
  let N : ℝ := (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)
  have hmeanPoint : (fun ω => N⁻¹ * S ω) = N⁻¹ • S := by
    funext ω
    simp [smul_eq_mul]
  have hcap0 : 0 ≤ cap := by
    dsimp [cap]
    exact mul_nonneg (by norm_num [inverseBankReserve])
      (mul_nonneg (nativeHeat_gm_nonneg k hk1 hk20)
        (by exact_mod_cast hnum.variance_nonneg))
  have hcellMeas (i : nativeHeatQ3RefinedCarrierIndex) : Measurable (U i) := by
    have hchild : (nativeHeatQ3RefinedCarrierChild m i).scale + 1 = m + 1 := by
      have := nativeHeatQ3RefinedCarrierChild_scale m i
      omega
    have hprofile := nativeHeatRefined_oldInverseTraceProfileDepth4_of_states
      M h hM hgamma (nativeHeatQ3RefinedCarrierChild m i) (m + 1) hchild hpast
    exact hprofile.1.mul ((nativeHeatQ3RefinedZ_measurableGen ns M m i).pow_const 2)
  have hcellMoment (i : nativeHeatQ3RefinedCarrierIndex) :
      ∫⁻ ω, ‖U i ω‖ₑ ^ (k : ℝ) ∂μ ≤ ENNReal.ofReal cap ^ (k : ℝ) :=
    nativeHeatQ3RefinedRareCell_moment_leGen ns hnum M h hM m hgamma hstate hpast i k hk1 hk20
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1R : 1 ≤ (k : ℝ) := by exact_mod_cast hk1
  have hcellLp (i : nativeHeatQ3RefinedCarrierIndex) :
      eLpNorm' (U i) (k : ℝ) μ ≤ ENNReal.ofReal cap := by
    have hpow : eLpNorm' (U i) (k : ℝ) μ ^ (k : ℝ) ≤
        ENNReal.ofReal cap ^ (k : ℝ) := by
      rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos]
      exact hcellMoment i
    exact (ENNReal.rpow_le_rpow_iff hkpos).mp hpow
  haveI : Nonempty nativeHeatQ3RefinedCarrierIndex :=
    ⟨⟨0, by norm_num⟩⟩
  have hmeanLp := nativeHeat_eLpNorm'_average_le (μ := μ) hk1R hcap0
    U hcellMeas hcellLp
  have hrareFun : nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4Gen ns M m =
      fun ω => 2 * (N⁻¹ * S ω) := by
    funext ω
    rfl
  have hrareLp :
      eLpNorm' (nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4Gen ns M m) (k : ℝ) μ ≤
        ENNReal.ofReal (2 * cap) := by
    have htwoPoint : (fun ω => 2 * (N⁻¹ * S ω)) =
        (2 : ℝ) • (N⁻¹ • S) := by
      funext ω
      simp [smul_eq_mul]
    have hscaleLp : eLpNorm' (fun ω => 2 * (N⁻¹ * S ω)) (k : ℝ) μ =
        ENNReal.ofReal 2 * eLpNorm' (fun ω => N⁻¹ * S ω) (k : ℝ) μ := by
      calc
        _ = eLpNorm' ((2 : ℝ) • (N⁻¹ • S)) (k : ℝ) μ := by rw [htwoPoint]
        _ = ENNReal.ofReal 2 * eLpNorm' (N⁻¹ • S) (k : ℝ) μ := by
          simpa only [Real.enorm_eq_ofReal (by norm_num : 0 ≤ (2 : ℝ))] using
            (eLpNorm'_const_smul (2 : ℝ) hkpos (f := N⁻¹ • S) (μ := μ))
        _ = _ := by rw [← hmeanPoint]
    rw [hrareFun]
    calc
      _ = ENNReal.ofReal 2 * eLpNorm' (fun ω => N⁻¹ * S ω) (k : ℝ) μ := hscaleLp
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal cap :=
        mul_le_mul_of_nonneg_left hmeanLp (by positivity)
      _ = ENNReal.ofReal (2 * cap) := by
        rw [← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
  calc
    _ = eLpNorm' (nativeHeatQ3RefinedCarrierSourceRareQuadraticDepth4Gen ns M m) (k : ℝ) μ ^
        (k : ℝ) := lintegral_rpow_enorm_eq_rpow_eLpNorm' hkpos
    _ ≤ ENNReal.ofReal (2 * cap) ^ (k : ℝ) :=
      ENNReal.rpow_le_rpow hrareLp (by positivity)
    _ = _ := by
      simp only [cap]
      congr 2
      ring

end ASDExplicitGamma.Native
