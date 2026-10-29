module

public import ASDExplicitGamma.Variational.LemmaVEstimate
public import ASDExplicitGamma.Variational.LemmaVH2Constants
public import ASDExplicitGamma.Main.Q3W2Jets
public import ASDExplicitGamma.Main.HessianTrial
public import ASDExplicitGamma.Main.LocalizedHessian
public import ASDExplicitGamma.Main.Q3RowProduct
public import ASDExplicitGamma.Main.Q3RemainderCaps
public import ASDExplicitGamma.Gaussian.SupMeanKernelCovariance
public import ASDExplicitGamma.Variational.LemmaVH2ClosedBandRemainder
public import ASDExplicitGamma.Numerics.GeneratorMuStar

/-! Weighted finite-family algebra used by the generator and bracket bounds. -/

@[expose] public section

namespace ASDExplicitGamma.Gaussian

open scoped BigOperators
open ASDExplicitGamma.Variational
open ASDExplicitGamma.Response
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Model
open Homogenization MeasureTheory

open ASDExplicitGamma.Numerics

/-! The one-shell specialization of the closed H2 band constant. -/

/-- For a single q3 shell, Lemma V's stationary-band constant is at most twice
the square root of its variance when the tile is at most `1/243` of the shell.
The deliberately coarse bound is sufficient for the source carré-du-champ
constant after Lemma V's factor four is retained. -/
theorem single_shell_h2_constant_le_two_sqrt
    (r v L : ℝ) (hr : 0 ≤ r) (hv : 0 ≤ v) (hL : 0 < L)
    (hρ : r / L ≤ 1 / 243) :
    lemmaVH2BandConstant r v (v / L ^ 2) (v / L ^ 4) ≤ 2 * Real.sqrt v := by
  let ρ : ℝ := r / L
  have hρ0 : 0 ≤ ρ := div_nonneg hr hL.le
  have hρcap : ρ ≤ 1 / 243 := hρ
  have hroot2 : Real.sqrt (v / L ^ 2) = Real.sqrt v / L := by
    rw [Real.sqrt_div hv, Real.sqrt_sq hL.le]
  have hroot4 : Real.sqrt (v / L ^ 4) = Real.sqrt v / L ^ 2 := by
    rw [Real.sqrt_div hv, show L ^ 4 = (L ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg L)]
  have hmoment2 : Real.sqrt ((78 / 5 : ℝ) * (v / L ^ 2)) =
      Real.sqrt (78 / 5) * (Real.sqrt v / L) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 78 / 5), hroot2]
  have hmoment4 : Real.sqrt (((3432 / 5 : ℝ) + (78 / 5 : ℝ) ^ 2) *
      (v / L ^ 4)) =
      Real.sqrt ((3432 / 5 : ℝ) + (78 / 5 : ℝ) ^ 2) *
        (Real.sqrt v / L ^ 2) := by
    rw [Real.sqrt_mul (by positivity), hroot4]
  have hrad1 : Real.sqrt (78 / 5 : ℝ) < 4 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 4)).mpr (by norm_num)
  have hrad2 : Real.sqrt ((3432 / 5 : ℝ) + (78 / 5 : ℝ) ^ 2) < 31 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 31)).mpr (by norm_num)
  have hcoef1 : (36 / 25 : ℝ) * Real.sqrt (78 / 5) ≤ 6 := by
    nlinarith only [hrad1]
  have hcoef2 : (57 / 200 : ℝ) *
      Real.sqrt ((3432 / 5 : ℝ) + (78 / 5 : ℝ) ^ 2) ≤ 9 := by
    nlinarith only [hrad2]
  have hρsq : ρ ^ 2 ≤ (1 / 243 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (ρ - 1 / 243 : ℝ)]
  have hfactor : 1 + (36 / 25 : ℝ) * Real.sqrt (78 / 5) * ρ +
      (57 / 200 : ℝ) * Real.sqrt ((3432 / 5 : ℝ) + (78 / 5 : ℝ) ^ 2) * ρ ^ 2 ≤ 2 := by
    calc
      _ ≤ 1 + 6 * ρ + 9 * ρ ^ 2 := by
        gcongr
      _ ≤ 2 := by nlinarith [hρcap, hρsq]
  calc
    lemmaVH2BandConstant r v (v / L ^ 2) (v / L ^ 4) =
        Real.sqrt v * (1 + (36 / 25 : ℝ) * Real.sqrt (78 / 5) * ρ +
          (57 / 200 : ℝ) *
            Real.sqrt ((3432 / 5 : ℝ) + (78 / 5 : ℝ) ^ 2) * ρ ^ 2) := by
      unfold lemmaVH2BandConstant lemmaVH2C1 lemmaVH2C2 lemmaVH2R1 lemmaVH2A2
      simp only [lemmaVH2R1]
      rw [hmoment2, hmoment4]
      dsimp [ρ]
      field_simp [hL.ne']
    _ ≤ 2 * Real.sqrt v := by
      have := mul_le_mul_of_nonneg_left hfactor (Real.sqrt_nonneg v)
      nlinarith only [this]

/-! The actual white-noise CM directions satisfy the full cross-point and
cross-jet covariance contract consumed by Lemma V. -/

/-- The bounded response coefficient represented by a single white-noise
coordinate, restricted to the compact closure of a triadic observation cube. -/
noncomputable def mainShellResponseCoefficient (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (u : WhiteNoise) :
    ResponseCoefficient (openCubeSet Q) := by
  letI compactObservationCube : CompactSpace (closure (openCubeSet Q)) :=
    isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => q3Convolution b L h3Zero u x.1,
      (q3Convolution_continuous b L h3Zero u).comp continuous_subtype_val⟩

theorem mainShellResponseCoefficient_extension (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (u : WhiteNoise) {x : Vec 2}
    (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (mainShellResponseCoefficient Q b L u) x =
      q3Convolution b L h3Zero u x := by
  rw [responseCoefficientExtension_eq _ hx]
  rfl

/-! The source row estimate has the precise shell constant consumed by the
localized generator cross term. -/

/-- For a nonnegative shell amplitude, the actual q3 DIAG row coefficient is
bounded by the conservative feedback coefficient on the source ratio gate. -/
theorem main_q3_row_constant_le_generatorKB {r b L : ℝ}
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hL : 0 < L) :
    mainQ3RowConstant r b L ≤ generatorKB (r / L) * b := by
  have hρ0 : 0 ≤ r / L := div_nonneg hr hL.le
  have hterm2 : Real.sqrt ((78 / 5 : ℝ) * b ^ 2 / L ^ 2) =
      b / L * Real.sqrt (78 / 5 : ℝ) := by
    have hsq : (78 / 5 : ℝ) * b ^ 2 / L ^ 2 =
        (b / L) ^ 2 * (78 / 5 : ℝ) := by ring
    rw [hsq, Real.sqrt_mul (sq_nonneg (b / L)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (div_nonneg hb hL.le)]
  have hterm4 : Real.sqrt ((23244 / 25 : ℝ) * b ^ 2 / L ^ 4) =
      b / L ^ 2 * Real.sqrt (23244 / 25 : ℝ) := by
    have hsq : (23244 / 25 : ℝ) * b ^ 2 / L ^ 4 =
        (b / L ^ 2) ^ 2 * (23244 / 25 : ℝ) := by ring
    rw [hsq, Real.sqrt_mul (sq_nonneg (b / L ^ 2)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (div_nonneg hb (sq_nonneg L))]
  have hc1 : (36 / 25 : ℝ) ≤ 2.36412 := by norm_num
  have hc2 : (57 / 200 : ℝ) ≤ 0.52288 := by norm_num
  have hrad1 : 0 ≤ Real.sqrt (78 / 5 : ℝ) := Real.sqrt_nonneg _
  have hrad2 : 0 ≤ Real.sqrt (23244 / 25 : ℝ) := Real.sqrt_nonneg _
  have h0 : (1 : ℝ) ≤ 1.860 := by norm_num
  have h1 : 0 ≤ (2.36412 - 36 / 25) * Real.sqrt (78 / 5) * (r / L) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc1) hrad1) hρ0
  have h2 : 0 ≤ (0.52288 - 57 / 200) * Real.sqrt (23244 / 25) * (r / L) ^ 2 :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hc2) hrad2) (sq_nonneg (r / L))
  have hcoef :
      1 + (36 / 25 : ℝ) * (r / L) * Real.sqrt (78 / 5) +
          (57 / 200 : ℝ) * (r / L) ^ 2 * Real.sqrt (23244 / 25) ≤
        1.860 + 2.36412 * (r / L) * Real.sqrt (78 / 5) +
          0.52288 * (r / L) ^ 2 * Real.sqrt (23244 / 25) := by
    nlinarith [h0, h1, h2]
  have hbase : Real.sqrt (b ^ 2) = b := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hb]
  unfold mainQ3RowConstant generatorKB
  rw [hbase, hterm2, hterm4]
  have hfactor :
      r * (36 / 25 : ℝ) * (b / L * Real.sqrt (78 / 5)) =
        b * ((36 / 25 : ℝ) * (r / L) * Real.sqrt (78 / 5)) := by
    field_simp [hL.ne']
  have hfactor4 :
      r ^ 2 * (57 / 200 : ℝ) * (b / L ^ 2 * Real.sqrt (23244 / 25)) =
        b * ((57 / 200 : ℝ) * (r / L) ^ 2 * Real.sqrt (23244 / 25)) := by
    field_simp [hL.ne']
  calc
    b + r * (36 / 25 : ℝ) * (b / L * Real.sqrt (78 / 5)) +
        r ^ 2 * (57 / 200 : ℝ) * (b / L ^ 2 * Real.sqrt (23244 / 25)) =
      b * (1 + (36 / 25 : ℝ) * (r / L) * Real.sqrt (78 / 5) +
        (57 / 200 : ℝ) * (r / L) ^ 2 * Real.sqrt (23244 / 25)) := by
          rw [hfactor, hfactor4]
          ring
    _ ≤ b * (1.860 + 2.36412 * (r / L) * Real.sqrt (78 / 5) +
        0.52288 * (r / L) ^ 2 * Real.sqrt (23244 / 25)) :=
          mul_le_mul_of_nonneg_left hcoef hb
    _ = (1.860 + 2.36412 * (r / L) * Real.sqrt (78 / 5) +
        0.52288 * (r / L) ^ 2 * Real.sqrt (23244 / 25)) * b := by ring

/-- The actual finite q3 value column has trace at most the shell variance.
This is the finite Bessel form of the exact same-point value covariance. -/
theorem main_q3_finite_value_norm_sq_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    ‖mainQ3FiniteValue e s b L x‖ ^ 2 ≤ b ^ 2 := by
  let a : ι → ℝ := fun n =>
    q3Convolution b L (mainQ3JetIndex .value) (e n) x
  have hcov := main_q3_jet_covariance e b L .value .value x
  have htsum : (∑' n, a n ^ 2) = b ^ 2 := by
    simpa [a, pow_two, q3ScaledJetCovariance_value_diagonal] using hcov.tsum_eq
  have hs : Summable (fun n => a n ^ 2) := by
    simpa [a, pow_two] using hcov.summable
  have hfinite : (∑ n ∈ s, a n ^ 2) ≤ b ^ 2 := by
    calc
      (∑ n ∈ s, a n ^ 2) ≤ ∑' n, a n ^ 2 := hs.sum_le_tsum s
        (fun n _ => sq_nonneg (a n))
      _ = b ^ 2 := htsum
  calc
    ‖mainQ3FiniteValue e s b L x‖ ^ 2 = ∑ n ∈ s, a n ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [mainQ3FiniteValue, WithLp.ofLp_toLp, a]
      exact Finset.sum_coe_sort s (fun n =>
        (q3Convolution b L (mainQ3JetIndex .value) (e n) x) ^ 2)
    _ ≤ b ^ 2 := hfinite

/-- The outward decimal source coefficient is below the frozen CIR source
coefficient, with the physical shell variance and length left explicit. -/
theorem q3_source_coefficient_le_generatorKA {r b L : ℝ}
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hL : 0 < L) :
    b + mainQ3RemainderConstant r b L ≤ generatorKA (r / L) * b := by
  have hroot2 : Real.sqrt ((156/5:ℝ)*b^2/L^2) =
      Real.sqrt (156/5) * (b/L) := by
    rw [Real.sqrt_div (by positivity),
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 156/5),
      Real.sqrt_sq hb, Real.sqrt_sq hL.le]
    ring
  have hroot4 : Real.sqrt ((46488/25:ℝ)*b^2/L^4) =
      Real.sqrt (46488/25) * (b/L^2) := by
    rw [Real.sqrt_div (by positivity),
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 46488/25),
      Real.sqrt_sq hb, show L^4 = (L^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg L)]
    ring
  let ρ : ℝ := r/L
  have hρ : 0 ≤ ρ := div_nonneg hr hL.le
  have heq2 : r*(b/L) = ρ*b := by
    dsimp [ρ]
    field_simp [hL.ne']
  have heq4 : r^2*(b/L^2) = ρ^2*b := by
    dsimp [ρ]
    field_simp [hL.ne']
  have hrem : mainQ3RemainderConstant r b L =
      (2018/1000:ℝ)*(ρ*b*Real.sqrt (156/5)) +
        (285/1000:ℝ)*(ρ^2*b*Real.sqrt (46488/25)) := by
    unfold mainQ3RemainderConstant
    rw [hroot2, hroot4]
    calc
      _ = (2018/1000:ℝ)*(r*(b/L)*Real.sqrt (156/5)) +
          (285/1000:ℝ)*(r^2*(b/L^2)*Real.sqrt (46488/25)) := by ring
      _ = _ := by rw [heq2, heq4]
  have hlin : 0 ≤ ρ*b*Real.sqrt (156/5) :=
    mul_nonneg (mul_nonneg hρ hb) (Real.sqrt_nonneg _)
  have hquad : 0 ≤ ρ^2*b*Real.sqrt (46488/25) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hb) (Real.sqrt_nonneg _)
  have hbase : b ≤ (1.860:ℝ)*b := by nlinarith only [hb]
  have hlin' : (2018/1000:ℝ)*(ρ*b*Real.sqrt (156/5)) ≤
      2.36412*(ρ*b*Real.sqrt (156/5)) :=
    mul_le_mul_of_nonneg_right (by norm_num) hlin
  have hquad' : (285/1000:ℝ)*(ρ^2*b*Real.sqrt (46488/25)) ≤
      0.52288*(ρ^2*b*Real.sqrt (46488/25)) :=
    mul_le_mul_of_nonneg_right (by norm_num) hquad
  rw [hrem]
  unfold generatorKA
  calc
    b + ((2018/1000:ℝ)*(ρ*b*Real.sqrt (156/5)) +
        (285/1000:ℝ)*(ρ^2*b*Real.sqrt (46488/25))) ≤
      (1.860:ℝ)*b + 2.36412*(ρ*b*Real.sqrt (156/5)) +
        0.52288*(ρ^2*b*Real.sqrt (46488/25)) := by linarith only [hbase,hlin',hquad']
    _ = (1.860+2.36412*ρ*Real.sqrt (156/5)+
        0.52288*ρ^2*Real.sqrt (46488/25))*b := by ring

/-! The source generator matrix is controlled by its larger characteristic
root. This isolates the numeric gate from the variational producer. -/

/-- The DIAG two-variable quadratic form is bounded by its largest root and,
under the shell ratio gate, by the source constant 19. -/
theorem generator_quadratic_le_19 (ρ x y : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 243) :
    generatorH * (generatorKA ρ) ^ 2 * x ^ 2 +
        2 * generatorFeedback * generatorKA ρ * generatorKB ρ * x * y ≤
      19 * (x ^ 2 + y ^ 2) := by
  obtain ⟨hmu19, _⟩ := generator_mu_star_lt ρ hρ0 hρ
  let a : ℝ := generatorH * (generatorKA ρ) ^ 2
  let d : ℝ := generatorFeedback * generatorKA ρ * generatorKB ρ
  let μ : ℝ := generatorMuStar ρ
  have ha : 0 ≤ a := by dsimp [a]; norm_num [generatorH]; positivity
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (mul_pos generator_feedback_caps.1
      (generator_coefficient_caps ρ hρ0 hρ).1)
      (generator_coefficient_caps ρ hρ0 hρ).2.2.1
  have hμa : a ≤ μ := by
    dsimp [a, μ, generatorMuStar, generatorLambdaMax]
    have hs : Real.sqrt ((generatorH * (generatorKA ρ) ^ 2) ^ 2 +
        4 * (generatorFeedback * generatorKA ρ * generatorKB ρ) ^ 2) ≥
        generatorH * (generatorKA ρ) ^ 2 := by
      apply Real.le_sqrt_of_sq_le
      nlinarith only [sq_nonneg (generatorFeedback * generatorKA ρ * generatorKB ρ)]
    linarith
  have hroot : μ ^ 2 - a * μ - d ^ 2 = 0 := by
    simpa [a, d, μ, generatorMuStar, generatorLambdaMax] using
      generator_characteristic_root
        (generatorH * (generatorKA ρ) ^ 2)
        (generatorFeedback * generatorKA ρ * generatorKB ρ)
  have hprod : (μ - a) * μ = d ^ 2 := by nlinarith only [hroot]
  have hμ : 0 ≤ μ := le_trans ha hμa
  have hrootprod : Real.sqrt (μ - a) * Real.sqrt μ = d := by
    have hs1 : 0 ≤ μ - a := sub_nonneg.mpr hμa
    have hs2 : 0 ≤ μ := hμ
    rw [← Real.sqrt_mul hs1, hprod, Real.sqrt_sq_eq_abs, abs_of_pos hd]
  have hsquare :
      μ * (x ^ 2 + y ^ 2) -
          (a * x ^ 2 + 2 * d * x * y) =
        (Real.sqrt (μ - a) * x - Real.sqrt μ * y) ^ 2 := by
    have hs1 : Real.sqrt (μ - a) ^ 2 = μ - a := Real.sq_sqrt (sub_nonneg.mpr hμa)
    have hs2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ
    calc
      _ = (μ - a) * x ^ 2 - 2 * d * x * y + μ * y ^ 2 := by ring
      _ = (Real.sqrt (μ - a) ^ 2) * x ^ 2 - 2 * d * x * y +
          (Real.sqrt μ ^ 2) * y ^ 2 := by rw [hs1, hs2]
      _ = (Real.sqrt (μ - a) ^ 2) * x ^ 2 -
          2 * (Real.sqrt (μ - a) * Real.sqrt μ) * x * y +
          (Real.sqrt μ ^ 2) * y ^ 2 := by rw [hrootprod]
      _ = _ := by ring
  have hquad : a * x ^ 2 + 2 * d * x * y ≤ μ * (x ^ 2 + y ^ 2) := by
    nlinarith only [hsquare, sq_nonneg (Real.sqrt (μ - a) * x - Real.sqrt μ * y)]
  have hsum : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  calc
    generatorH * (generatorKA ρ) ^ 2 * x ^ 2 +
        2 * generatorFeedback * generatorKA ρ * generatorKB ρ * x * y =
      a * x ^ 2 + 2 * d * x * y := by dsimp [a, d]; ring
    _ ≤ μ * (x ^ 2 + y ^ 2) := hquad
    _ ≤ 19 * (x ^ 2 + y ^ 2) := mul_le_mul_of_nonneg_right hmu19.le hsum

/-! Exact projection form of the nilpotent-shear Hessian. This is the
source's carré-du-champ identity before inserting any localized estimates. -/

/-- Weighted Cauchy--Schwarz for a finite family of nonnegative weights. -/
theorem weighted_sqrt_product_sum_sq_le {ι : Type*} (s : Finset ι)
    (w A B : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hA : ∀ i ∈ s, 0 ≤ A i) (hB : ∀ i ∈ s, 0 ≤ B i) :
    (∑ i ∈ s, w i * Real.sqrt (A i) * Real.sqrt (B i)) ^ 2 ≤
      (∑ i ∈ s, w i * A i) * (∑ i ∈ s, w i * B i) := by
  let X : ι → ℝ := fun i => Real.sqrt (w i) * Real.sqrt (A i)
  let Z : ι → ℝ := fun i => Real.sqrt (w i) * Real.sqrt (B i)
  have hX : (∑ i ∈ s, X i ^ 2) = ∑ i ∈ s, w i * A i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [X, mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hA i hi)]
  have hZ : (∑ i ∈ s, Z i ^ 2) = ∑ i ∈ s, w i * B i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Z, mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hB i hi)]
  have hXZ : (∑ i ∈ s, X i * Z i) =
      ∑ i ∈ s, w i * Real.sqrt (A i) * Real.sqrt (B i) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [X, Z]
    calc
      _ = (Real.sqrt (w i) * Real.sqrt (w i)) *
          Real.sqrt (A i) * Real.sqrt (B i) := by ring
      _ = (Real.sqrt (w i) ^ 2) * Real.sqrt (A i) * Real.sqrt (B i) := by ring
      _ = w i * Real.sqrt (A i) * Real.sqrt (B i) := by rw [Real.sq_sqrt (hw i hi)]
  rw [← hXZ, ← hX, ← hZ]
  exact Finset.sum_mul_sq_le_sq_mul_sq s X Z

/-- The generator estimate is preserved by a nonnegative finite average. -/
theorem weighted_generator_of_local {ι : Type*} (s : Finset ι)
    (w T B Lc : ι → ℝ) (vbar : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hlocal : ∀ i ∈ s, Lc i ≤ 19 * vbar * B i ^ 2 * (T i + 4)) :
    (∑ i ∈ s, w i * Lc i) ≤
      19 * vbar * (∑ i ∈ s, w i * B i ^ 2 * (T i + 4)) := by
  calc
    (∑ i ∈ s, w i * Lc i) ≤
        ∑ i ∈ s, w i * (19 * vbar * B i ^ 2 * (T i + 4)) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hlocal i hi) (hw i hi)
    _ = 19 * vbar * (∑ i ∈ s, w i * B i ^ 2 * (T i + 4)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- A finite average retains the full carré-du-champ bound, including all
cross terms, when the gradients live in their common Hilbert space. -/
theorem weighted_bracket_of_local {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (w T B : ι → ℝ) (G : ι → E) (vbar : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hT : ∀ i ∈ s, 0 ≤ T i)
    (hvbar : 0 ≤ vbar)
    (hlocal : ∀ i ∈ s,
      ‖G i‖ ^ 2 ≤ 16 * vbar * T i * (B i ^ 2 * (T i + 4))) :
    ‖∑ i ∈ s, w i • G i‖ ^ 2 ≤
      16 * vbar * (∑ i ∈ s, w i * T i) *
        (∑ i ∈ s, w i * B i ^ 2 * (T i + 4)) := by
  let F : ι → ℝ := fun i => B i ^ 2 * (T i + 4)
  let c : ℝ := 16 * vbar
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hF (i : ι) (hi : i ∈ s) : 0 ≤ F i :=
    mul_nonneg (sq_nonneg _) (by linarith [hT i hi])
  have hroot (i : ι) (hi : i ∈ s) :
      ‖G i‖ ≤ Real.sqrt c * Real.sqrt (T i) * Real.sqrt (F i) := by
    have hfactor : Real.sqrt (16 * vbar * T i * (B i ^ 2 * (T i + 4))) =
        Real.sqrt c * Real.sqrt (T i) * Real.sqrt (F i) := by
      rw [show 16 * vbar * T i * (B i ^ 2 * (T i + 4)) = c * (T i * F i) by
        dsimp [c, F]; ring,
        Real.sqrt_mul hc, Real.sqrt_mul (hT i hi)]
      ring
    calc
      ‖G i‖ = Real.sqrt (‖G i‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ Real.sqrt (16 * vbar * T i * (B i ^ 2 * (T i + 4))) :=
        Real.sqrt_le_sqrt (hlocal i hi)
      _ = Real.sqrt c * Real.sqrt (T i) * Real.sqrt (F i) := hfactor
  have hSnon : 0 ≤ ∑ i ∈ s, w i * Real.sqrt (T i) * Real.sqrt (F i) :=
    Finset.sum_nonneg fun i hi =>
      mul_nonneg (mul_nonneg (hw i hi) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hnorm : ‖∑ i ∈ s, w i • G i‖ ≤
      Real.sqrt c * (∑ i ∈ s, w i * Real.sqrt (T i) * Real.sqrt (F i)) := by
    calc
      ‖∑ i ∈ s, w i • G i‖ ≤ ∑ i ∈ s, ‖w i • G i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, w i * ‖G i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      _ ≤ ∑ i ∈ s, w i *
          (Real.sqrt c * Real.sqrt (T i) * Real.sqrt (F i)) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hroot i hi) (hw i hi)
      _ = Real.sqrt c * (∑ i ∈ s, w i * Real.sqrt (T i) * Real.sqrt (F i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have hcs := weighted_sqrt_product_sum_sq_le s w T F hw hT hF
  have hnormSq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hSnon)).mpr hnorm
  calc
    ‖∑ i ∈ s, w i • G i‖ ^ 2 ≤
        (Real.sqrt c * (∑ i ∈ s, w i * Real.sqrt (T i) * Real.sqrt (F i))) ^ 2 := hnormSq
    _ = c * (∑ i ∈ s, w i * Real.sqrt (T i) * Real.sqrt (F i)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc]
    _ ≤ c * ((∑ i ∈ s, w i * T i) * (∑ i ∈ s, w i * F i)) :=
      mul_le_mul_of_nonneg_left hcs hc
    _ = 16 * vbar * (∑ i ∈ s, w i * T i) *
        (∑ i ∈ s, w i * B i ^ 2 * (T i + 4)) := by
      dsimp [c, F]
      rw [show (∑ i ∈ s, w i * (B i ^ 2 * (T i + 4))) =
          ∑ i ∈ s, w i * B i ^ 2 * (T i + 4) by
        apply Finset.sum_congr rfl
        intro i hi
        ring]
      ring

end ASDExplicitGamma.Gaussian
