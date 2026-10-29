/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationBounded
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth truncations for Gaussian concentration

This module constructs smooth bounded approximations and carries the polynomial derivative bounds
through their composition with the input function.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory

namespace ASDExplicitGamma.Gaussian

/-- A smooth bounded scalar approximation to the identity. -/
noncomputable def gaussianConcentrationTruncation (R s : ℝ) : ℝ := R * Real.sin (s / R)

private theorem hasDerivAt_gaussianConcentrationTruncation {R s : ℝ} (hR : 0 < R) :
    HasDerivAt (gaussianConcentrationTruncation R) (Real.cos (s / R)) s := by
  have hscale : HasDerivAt (fun y : ℝ => y / R) (1 / R) s :=
    (hasDerivAt_id s).div_const R
  have h := (Real.hasDerivAt_sin (s / R)).comp s hscale
  have h' := h.const_mul R
  change HasDerivAt (fun y => R * Real.sin (y / R)) (Real.cos (s / R)) s
  convert h' using 1
  · ext y
    simp [div_eq_mul_inv]
  · field_simp [hR.ne']

private theorem deriv_gaussianConcentrationTruncation {R : ℝ} (hR : 0 < R) :
    deriv (gaussianConcentrationTruncation R) = fun s => Real.cos (s / R) := by
  funext s
  exact (hasDerivAt_gaussianConcentrationTruncation hR).deriv

private theorem deriv2_gaussianConcentrationTruncation {R : ℝ} (hR : 0 < R) :
    deriv (deriv (gaussianConcentrationTruncation R)) =
      fun s => (-1 / R) * Real.sin (s / R) := by
  funext s
  rw [deriv_gaussianConcentrationTruncation hR]
  have hscale : HasDerivAt (fun y : ℝ => y / R) (1 / R) s :=
    (hasDerivAt_id s).div_const R
  have h := (Real.hasDerivAt_cos (s / R)).comp s hscale
  have hfun : (fun y : ℝ => Real.cos (y / R)) = Real.cos ∘ (fun y => y / R) := rfl
  rw [hfun]
  convert h.deriv using 1
  field_simp [hR.ne']

private theorem deriv3_gaussianConcentrationTruncation {R : ℝ} (hR : 0 < R) :
    deriv (deriv (deriv (gaussianConcentrationTruncation R))) =
      fun s => (-1 / R ^ 2) * Real.cos (s / R) := by
  funext s
  rw [deriv2_gaussianConcentrationTruncation hR]
  have hscale : HasDerivAt (fun y : ℝ => y / R) (1 / R) s :=
    (hasDerivAt_id s).div_const R
  have h := (Real.hasDerivAt_sin (s / R)).comp s hscale
  have hfun : (fun y : ℝ => (-1 / R) * Real.sin (y / R)) =
      (fun y => (-1 / R) * (Real.sin ∘ (fun z => z / R)) y) := rfl
  rw [hfun]
  convert (h.const_mul (-1 / R)).deriv using 1
  field_simp [hR.ne']

/-- The scalar truncation is smooth through order three. -/
theorem contDiff_gaussianConcentrationTruncation {R : ℝ} :
    ContDiff ℝ 3 (gaussianConcentrationTruncation R) := by
  exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_id.div_const R))

/-- The sine truncation is pointwise dominated by the identity in absolute value. -/
theorem abs_gaussianConcentrationTruncation_le {R s : ℝ} (hR : 0 < R) :
    |gaussianConcentrationTruncation R s| ≤ |s| := by
  rw [gaussianConcentrationTruncation, abs_mul, abs_of_pos hR]
  calc
    R * |Real.sin (s / R)| ≤ R * |s / R| :=
      mul_le_mul_of_nonneg_left Real.abs_sin_le_abs hR.le
    _ = |s| := by rw [abs_div, abs_of_pos hR]; field_simp

/-- The sine truncation is bounded by its scale. -/
theorem abs_gaussianConcentrationTruncation_le_R {R s : ℝ} (hR : 0 ≤ R) :
    |gaussianConcentrationTruncation R s| ≤ R := by
  rw [gaussianConcentrationTruncation, abs_mul, abs_of_nonneg hR]
  calc
    R * |Real.sin (s / R)| ≤ R * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (s / R)) hR
    _ = R := by ring

/-- The sine truncation converges to the identity with an explicit cubic error bound. -/
theorem abs_gaussianConcentrationTruncation_sub_le {R s : ℝ} (hR : 0 < R) :
    |gaussianConcentrationTruncation R s - s| ≤ |s| ^ 3 / (6 * R ^ 2) := by
  rw [gaussianConcentrationTruncation]
  have hsin := Real.abs_sub_sin_le (s / R)
  have halg : R * Real.sin (s / R) - s = R * (Real.sin (s / R) - s / R) := by
    field_simp [hR.ne']
  have hscale : |R * Real.sin (s / R) - s| = R * |Real.sin (s / R) - s / R| := by
    rw [halg, abs_mul, abs_of_pos hR]
  rw [hscale]
  have hsin' : |Real.sin (s / R) - s / R| ≤ |s / R| ^ 3 / 6 := by
    simpa [abs_sub_comm] using hsin
  calc
    R * |Real.sin (s / R) - s / R| ≤ R * (|s / R| ^ 3 / 6) :=
      mul_le_mul_of_nonneg_left hsin' hR.le
    _ = |s| ^ 3 / (6 * R ^ 2) := by
      rw [abs_div, abs_of_pos hR]
      field_simp

/-- The sine truncation is one-Lipschitz. -/
theorem abs_deriv_gaussianConcentrationTruncation_le {R s : ℝ} (hR : 0 < R) :
    |deriv (gaussianConcentrationTruncation R) s| ≤ 1 := by
  rw [deriv_gaussianConcentrationTruncation hR]
  simpa using Real.abs_cos_le_one (s / R)

private theorem abs_deriv2_gaussianConcentrationTruncation_le {R s : ℝ}
    (hR : 1 ≤ R) :
    |deriv (deriv (gaussianConcentrationTruncation R)) s| ≤ 1 := by
  rw [deriv2_gaussianConcentrationTruncation (by linarith : 0 < R), abs_mul]
  have hsin : |Real.sin (s / R)| ≤ 1 := Real.abs_sin_le_one (s / R)
  have hRpos : 0 < R := by linarith
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))]
  have hcoeff : -(-1 / R) = 1 / R := by field_simp [ne_of_gt hRpos]
  rw [hcoeff]
  calc
    (1 / R) * |Real.sin (s / R)| ≤ (1 / R) * 1 :=
      mul_le_mul_of_nonneg_left hsin (by positivity)
    _ ≤ 1 := by simpa using (div_le_one hRpos).2 hR

private theorem abs_deriv3_gaussianConcentrationTruncation_le {R s : ℝ}
    (hR : 1 ≤ R) :
    |deriv (deriv (deriv (gaussianConcentrationTruncation R))) s| ≤ 1 := by
  rw [deriv3_gaussianConcentrationTruncation (by linarith : 0 < R), abs_mul]
  have hcos : |Real.cos (s / R)| ≤ 1 := Real.abs_cos_le_one (s / R)
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))]
  have hcoeff : -(-1 / R ^ 2) = 1 / R ^ 2 := by field_simp
  rw [hcoeff]
  calc
    (1 / R ^ 2) * |Real.cos (s / R)| ≤ (1 / R ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hcos (by positivity)
    _ ≤ 1 := by
      have hR2 : 1 ≤ R ^ 2 := by nlinarith
      simpa using (div_le_one (by positivity : 0 < R ^ 2)).2 hR2

private theorem contDiff_coordinateDerivative_truncation_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) (i : Fin n) :
    ContDiff ℝ 2 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 2)
    (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hp : ContDiff ℝ 2
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  convert h.comp hp using 1
  ext x
  rfl

private theorem coordinateDerivative_mul_truncation_local {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinateDerivative (fun y => f y * g y) i x =
      coordinateDerivative f i x * g x + f x * coordinateDerivative g i x := by
  let e : Fin n → ℝ := Pi.single i 1
  have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L e) (fderiv_fun_mul hf hg)
  simpa [coordinateDerivative, e, smul_apply, smul_eq_mul, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc] using h

private theorem coordinateDerivative_add_truncation_local {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinateDerivative (fun y => f y + g y) i x =
      coordinateDerivative f i x + coordinateDerivative g i x := by
  let e : Fin n → ℝ := Pi.single i 1
  have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L e) (fderiv_fun_add hf hg)
  simpa [coordinateDerivative, e] using h

/-- Coordinate differentiation commutes with smooth scalar composition by the chain rule. -/
theorem coordinateDerivative_comp_truncation_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 1 g) (i : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y => g (F y)) i x =
      deriv g (F x) * coordinateDerivative F i x := by
  let e : Fin n → ℝ := Pi.single i 1
  have hinner := (hF.differentiable_one x).hasFDerivAt
  have houter := (hg.differentiable_one (F x)).hasDerivAt.hasFDerivAt
  have hcomp := houter.comp x hinner
  have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L e) hcomp.fderiv
  simpa [Function.comp_def, coordinateDerivative, e, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, mul_comm, mul_left_comm, mul_assoc] using h

private theorem coordinateDerivative_second_comp_truncation_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) (i j : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (coordinateDerivative (fun y => g (F y)) i) j x =
      deriv (deriv g) (F x) * coordinateDerivative F j x * coordinateDerivative F i x +
        deriv g (F x) * coordinateDerivative (coordinateDerivative F i) j x := by
  let A : (Fin n → ℝ) → ℝ := fun y => deriv g (F y)
  let B : (Fin n → ℝ) → ℝ := coordinateDerivative F i
  have hF₁ : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hg₁ : ContDiff ℝ 1 (deriv g) := by
    have h := hg.contDiff_fderiv_apply (m := 1) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hp : ContDiff ℝ 1 (fun z : ℝ => (z, (1 : ℝ))) := contDiff_id.prodMk contDiff_const
    convert h.comp hp using 1
    ext z
    rfl
  have hA₁ : ContDiff ℝ 1 A := hg₁.comp hF₁
  have hB₁ : ContDiff ℝ 1 B := by
    have h := hF.contDiff_fderiv_apply (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hp : ContDiff ℝ 1
        (fun y : Fin n → ℝ => (y, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
      contDiff_id.prodMk contDiff_const
    convert h.comp hp using 1
    ext y
    rfl
  have hfirst : coordinateDerivative (fun y => g (F y)) i = fun y => A y * B y := by
    funext y
    exact coordinateDerivative_comp_truncation_local hF₁
      (hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) (i := i) y
  have hprod := coordinateDerivative_mul_truncation_local
    (hA₁.differentiable_one x) (hB₁.differentiable_one x) j
  rw [hfirst, hprod]
  have hAder : coordinateDerivative A j x =
      deriv (deriv g) (F x) * coordinateDerivative F j x :=
    coordinateDerivative_comp_truncation_local hF₁ hg₁ j x
  rw [hAder]

private theorem contDiff_deriv_one_of_two_truncation_local {g : ℝ → ℝ}
    (hg : ContDiff ℝ 2 g) : ContDiff ℝ 1 (deriv g) := by
  have h := hg.contDiff_fderiv_apply (m := 1)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hp : ContDiff ℝ 1 (fun z : ℝ => (z, (1 : ℝ))) := contDiff_id.prodMk contDiff_const
  convert h.comp hp using 1
  ext z
  rfl

private theorem contDiff_deriv_two_of_three_truncation_local {g : ℝ → ℝ}
    (hg : ContDiff ℝ 3 g) : ContDiff ℝ 2 (deriv g) := by
  have h := hg.contDiff_fderiv_apply (m := 2)
    (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hp : ContDiff ℝ 2 (fun z : ℝ => (z, (1 : ℝ))) := contDiff_id.prodMk contDiff_const
  convert h.comp hp using 1
  ext z
  rfl

private theorem contDiff_deriv2_one_of_three_truncation_local {g : ℝ → ℝ}
    (hg : ContDiff ℝ 3 g) : ContDiff ℝ 1 (deriv (deriv g)) :=
  contDiff_deriv_one_of_two_truncation_local
    (contDiff_deriv_two_of_three_truncation_local hg)

private theorem coordinateDerivative_third_comp_truncation_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) {g : ℝ → ℝ}
    (hg : ContDiff ℝ 3 g) (i j k : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (coordinateDerivative (coordinateDerivative
      (fun y => g (F y)) i) j) k x =
        deriv (deriv (deriv g)) (F x) * coordinateDerivative F k x *
            coordinateDerivative F j x * coordinateDerivative F i x +
          deriv (deriv g) (F x) *
            coordinateDerivative (coordinateDerivative F j) k x *
            coordinateDerivative F i x +
          deriv (deriv g) (F x) * coordinateDerivative F j x *
            coordinateDerivative (coordinateDerivative F i) k x +
          deriv (deriv g) (F x) * coordinateDerivative F k x *
            coordinateDerivative (coordinateDerivative F i) j x +
          deriv g (F x) *
            coordinateDerivative (coordinateDerivative (coordinateDerivative F i) j) k x := by
  let P : (Fin n → ℝ) → ℝ := fun y => deriv (deriv g) (F y)
  let Q : (Fin n → ℝ) → ℝ := fun y => deriv g (F y)
  let Fi : (Fin n → ℝ) → ℝ := coordinateDerivative F i
  let Fj : (Fin n → ℝ) → ℝ := coordinateDerivative F j
  let Fij : (Fin n → ℝ) → ℝ := coordinateDerivative (coordinateDerivative F i) j
  have hF₂ : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hF₁ : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hQ₁ : ContDiff ℝ 1 Q := by
    change ContDiff ℝ 1 (deriv g ∘ F)
    exact (contDiff_deriv_two_of_three_truncation_local hg).of_le (by norm_num) |>.comp hF₁
  have hP₁ : ContDiff ℝ 1 P :=
    (contDiff_deriv2_one_of_three_truncation_local hg).comp hF₁
  have hFi₂ : ContDiff ℝ 2 Fi := contDiff_coordinateDerivative_truncation_local hF i
  have hFj₂ : ContDiff ℝ 2 Fj := contDiff_coordinateDerivative_truncation_local hF j
  have hFij₁ : ContDiff ℝ 1 Fij := by
    have h := hFi₂.contDiff_fderiv_apply (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hp : ContDiff ℝ 1
        (fun y : Fin n → ℝ => (y, (Pi.single j (1 : ℝ) : Fin n → ℝ))) :=
      contDiff_id.prodMk contDiff_const
    convert h.comp hp using 1
    ext y
    rfl
  have hsecond : coordinateDerivative (coordinateDerivative
      (fun y => g (F y)) i) j = fun y =>
        deriv (deriv g) (F y) * coordinateDerivative F j y * coordinateDerivative F i y +
          deriv g (F y) * coordinateDerivative (coordinateDerivative F i) j y := by
    funext y
    exact coordinateDerivative_second_comp_truncation_local hF₂
      (hg.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) i j y
  have hsum := coordinateDerivative_add_truncation_local
    (show DifferentiableAt ℝ (fun y => P y * Fj y * Fi y) x from
      ((hP₁.differentiable_one x).mul
        ((hFj₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one x)).mul
        ((hFi₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one x))
    (show DifferentiableAt ℝ (fun y => Q y * Fij y) x from
      (hQ₁.differentiable_one x).mul (hFij₁.differentiable_one x)) k
  rw [hsecond, hsum]
  have hleft1 := coordinateDerivative_mul_truncation_local
    (hP₁.differentiable_one x)
    (((contDiff_coordinateDerivative_truncation_local hF j).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one x) k
  have hleft2 := coordinateDerivative_mul_truncation_local
    ((hP₁.mul ((contDiff_coordinateDerivative_truncation_local hF j).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2))).differentiable_one x)
    ((hFi₂.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one x) k
  have hright := coordinateDerivative_mul_truncation_local
    (hQ₁.differentiable_one x) (hFij₁.differentiable_one x) k
  rw [hleft2, hleft1, hright]
  have hPder : coordinateDerivative P k x =
      deriv (deriv (deriv g)) (F x) * coordinateDerivative F k x :=
    coordinateDerivative_comp_truncation_local hF₁
      (contDiff_deriv2_one_of_three_truncation_local hg) k x
  have hQder : coordinateDerivative Q k x =
      deriv (deriv g) (F x) * coordinateDerivative F k x :=
    coordinateDerivative_comp_truncation_local hF₁
      ((contDiff_deriv_two_of_three_truncation_local hg).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) k x
  have hFjder : coordinateDerivative Fj k x =
      coordinateDerivative (coordinateDerivative F j) k x := rfl
  have hFider : coordinateDerivative Fi k x =
      coordinateDerivative (coordinateDerivative F i) k x := rfl
  have hFijder : coordinateDerivative Fij k x =
      coordinateDerivative (coordinateDerivative (coordinateDerivative F i) j) k x := rfl
  rw [hPder, hQder, hFjder, hFider, hFijder]
  dsimp [P, Q, Fi, Fj, Fij]
  ring

/-- Smooth bounded truncation preserves the polynomial bounds through coordinate order three. -/
theorem hasPolynomiallyBoundedThirdCoordinateDerivatives_truncation_comp
    {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {R : ℝ} (hR : 1 ≤ R) :
    HasPolynomiallyBoundedThirdCoordinateDerivatives
      (fun x => gaussianConcentrationTruncation R (F x)) := by
  rcases hF with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  let T : (Fin n → ℝ) → ℝ := fun x => 1 + ‖x‖
  let H : (Fin n → ℝ) → ℝ := fun x => C * T x ^ d
  let C' : ℝ := R + 10 * C + 10 * C ^ 2 + 10 * C ^ 3
  let G : (Fin n → ℝ) → ℝ := fun x => gaussianConcentrationTruncation R (F x)
  have hRpos : 0 < R := by linarith
  have hRnonneg : 0 ≤ R := by linarith
  have hcont' : ContDiff ℝ 3 G := by
    change ContDiff ℝ 3 (gaussianConcentrationTruncation R ∘ F)
    exact (contDiff_gaussianConcentrationTruncation (R := R)).comp hcont
  have hT (x : Fin n → ℝ) : 1 ≤ T x := by
    dsimp [T]
    exact le_add_of_nonneg_right (norm_nonneg x)
  have hHnonneg (x : Fin n → ℝ) : 0 ≤ H x := by
    dsimp [H]
    positivity
  have hpow1 (x : Fin n → ℝ) : T x ^ d ≤ T x ^ (3 * d) :=
    pow_le_pow_right₀ (hT x) (by omega)
  have hpow2 (x : Fin n → ℝ) : T x ^ (d * 2) ≤ T x ^ (3 * d) :=
    pow_le_pow_right₀ (hT x) (by omega)
  have hH1 (x : Fin n → ℝ) : H x ≤ C * T x ^ (3 * d) := by
    dsimp [H]
    exact mul_le_mul_of_nonneg_left (hpow1 x) hC
  have hH2 (x : Fin n → ℝ) : H x ^ 2 ≤ C ^ 2 * T x ^ (3 * d) := by
    dsimp [H]
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_left (hpow2 x) (sq_nonneg C)
  have hpow3 (x : Fin n → ℝ) : T x ^ (d * 3) ≤ T x ^ (3 * d) := by
    simp [Nat.mul_comm d 3]
  have hH3 (x : Fin n → ℝ) : H x ^ 3 ≤ C ^ 3 * T x ^ (3 * d) := by
    dsimp [H]
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_left (hpow3 x) (by positivity)
  have hHsq_prod {i j : Fin n} (x : Fin n → ℝ) :
      |coordinateDerivative F i x| * |coordinateDerivative F j x| ≤ H x ^ 2 := by
    calc
      |coordinateDerivative F i x| * |coordinateDerivative F j x| ≤ H x * H x :=
        mul_le_mul (by simpa [H, T] using hone i x)
          (by simpa [H, T] using hone j x) (abs_nonneg _) (by positivity)
      _ = H x ^ 2 := by ring
  have hHcube_prod {i j k : Fin n} (x : Fin n → ℝ) :
      |coordinateDerivative F i x * coordinateDerivative F j x *
        coordinateDerivative F k x| ≤ H x ^ 3 := by
    rw [abs_mul, abs_mul]
    calc
      |coordinateDerivative F i x| * |coordinateDerivative F j x| *
          |coordinateDerivative F k x| ≤ H x ^ 2 * H x :=
        mul_le_mul (hHsq_prod (i := i) (j := j) x)
          (by simpa [H, T] using hone k x) (abs_nonneg _) (by positivity)
      _ = H x ^ 3 := by ring
  have hzero' (x : Fin n → ℝ) : |G x| ≤ C' * T x ^ (3 * d) := by
    have hb := abs_gaussianConcentrationTruncation_le_R (R := R) (s := F x) hRnonneg
    have hp : 1 ≤ T x ^ (3 * d) := by
      simpa using pow_le_pow_right₀ (hT x) (show 0 ≤ 3 * d by omega)
    dsimp [G, C']
    calc
      |gaussianConcentrationTruncation R (F x)| ≤ R := hb
      _ ≤ (R + 10 * C + 10 * C ^ 2 + 10 * C ^ 3) * T x ^ (3 * d) := by
        have hCextra : 0 ≤ 10 * C + 10 * C ^ 2 + 10 * C ^ 3 := by positivity
        have hCprime : R ≤ R + 10 * C + 10 * C ^ 2 + 10 * C ^ 3 := by
          linarith
        calc
          R = R * 1 := by ring
          _ ≤ R * T x ^ (3 * d) := mul_le_mul_of_nonneg_left hp hRnonneg
          _ ≤ (R + 10 * C + 10 * C ^ 2 + 10 * C ^ 3) * T x ^ (3 * d) :=
            mul_le_mul_of_nonneg_right hCprime (by positivity)
  have hone' (i : Fin n) (x : Fin n → ℝ) : |coordinateDerivative G i x| ≤
      C' * T x ^ (3 * d) := by
    have hformula := coordinateDerivative_comp_truncation_local
      (hcont.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3))
      ((contDiff_gaussianConcentrationTruncation (R := R)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) i x
    change |coordinateDerivative (fun y => gaussianConcentrationTruncation R (F y)) i x| ≤
      C' * T x ^ (3 * d)
    rw [hformula, abs_mul]
    calc
      |deriv (gaussianConcentrationTruncation R) (F x)| *
          |coordinateDerivative F i x| ≤ 1 * H x :=
        mul_le_mul (abs_deriv_gaussianConcentrationTruncation_le
          (R := R) (s := F x) hRpos)
          (by simpa [H, T] using hone i x) (abs_nonneg _) (by positivity)
      _ = H x := by ring
      _ ≤ C' * T x ^ (3 * d) := by
        have hsmall : C ≤ C' := by dsimp [C']; nlinarith [hR]
        have hpow : T x ^ d ≤ T x ^ (3 * d) := hpow1 x
        dsimp [H]
        exact (mul_le_mul_of_nonneg_left hpow hC).trans
          (mul_le_mul_of_nonneg_right hsmall (by positivity))
  have htwo' (i j : Fin n) (x : Fin n → ℝ) :
      |coordinateDerivative (coordinateDerivative G i) j x| ≤
        C' * T x ^ (3 * d) := by
    have hformula := coordinateDerivative_second_comp_truncation_local
      (hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      ((contDiff_gaussianConcentrationTruncation (R := R)).of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) i j x
    change |coordinateDerivative (coordinateDerivative
      (fun y => gaussianConcentrationTruncation R (F y)) i) j x| ≤
      C' * T x ^ (3 * d)
    rw [hformula]
    let a := deriv (deriv (gaussianConcentrationTruncation R)) (F x)
      * coordinateDerivative F j x * coordinateDerivative F i x
    let b := deriv (gaussianConcentrationTruncation R) (F x)
      * coordinateDerivative (coordinateDerivative F i) j x
    have ha : |a| ≤ H x ^ 2 := by
      dsimp [a]
      have heq : deriv (deriv (gaussianConcentrationTruncation R)) (F x) *
          coordinateDerivative F j x * coordinateDerivative F i x =
          deriv (deriv (gaussianConcentrationTruncation R)) (F x) *
            (coordinateDerivative F j x * coordinateDerivative F i x) := by ring
      rw [heq]
      simp only [abs_mul]
      calc
        |deriv (deriv (gaussianConcentrationTruncation R)) (F x)| *
            (|coordinateDerivative F j x| * |coordinateDerivative F i x|) ≤
              1 * H x ^ 2 :=
          mul_le_mul (abs_deriv2_gaussianConcentrationTruncation_le
            (R := R) (s := F x) hR)
          (hHsq_prod (i := j) (j := i) x)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
        _ = H x ^ 2 := by ring
    have hb : |b| ≤ H x := by
      dsimp [b]
      rw [abs_mul]
      calc
        |deriv (gaussianConcentrationTruncation R) (F x)| *
            |coordinateDerivative (coordinateDerivative F i) j x| ≤ 1 * H x :=
          mul_le_mul (abs_deriv_gaussianConcentrationTruncation_le
            (R := R) (s := F x) hRpos)
            (by simpa [H, T] using htwo i j x) (abs_nonneg _) (by norm_num)
        _ = H x := by ring
    have hsum : |a + b| ≤ H x ^ 2 + H x := by
      calc
        |a + b| ≤ |a| + |b| := abs_add_le _ _
        _ ≤ H x ^ 2 + H x := add_le_add ha hb
    change |a + b| ≤ C' * T x ^ (3 * d)
    calc
      |a + b| ≤ H x ^ 2 + H x := hsum
      _ ≤ (C ^ 2 + C) * T x ^ (3 * d) := by
        have h := add_le_add (hH2 x) (hH1 x)
        nlinarith [h]
      _ ≤ C' * T x ^ (3 * d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C']
        nlinarith [hR, hC]
  have hthree' (i j k : Fin n) (x : Fin n → ℝ) :
      |coordinateDerivative (coordinateDerivative (coordinateDerivative G i) j) k x| ≤
        C' * T x ^ (3 * d) := by
    have hformula := coordinateDerivative_third_comp_truncation_local hcont
      (contDiff_gaussianConcentrationTruncation (R := R)) i j k x
    change |coordinateDerivative (coordinateDerivative (coordinateDerivative
      (fun y => gaussianConcentrationTruncation R (F y)) i) j) k x| ≤
      C' * T x ^ (3 * d)
    rw [hformula]
    let a := deriv (deriv (deriv (gaussianConcentrationTruncation R))) (F x) *
      coordinateDerivative F k x * coordinateDerivative F j x * coordinateDerivative F i x
    let b := deriv (deriv (gaussianConcentrationTruncation R)) (F x) *
      coordinateDerivative (coordinateDerivative F j) k x * coordinateDerivative F i x
    let c := deriv (deriv (gaussianConcentrationTruncation R)) (F x) *
      coordinateDerivative F j x * coordinateDerivative (coordinateDerivative F i) k x
    let e := deriv (deriv (gaussianConcentrationTruncation R)) (F x) *
      coordinateDerivative F k x * coordinateDerivative (coordinateDerivative F i) j x
    let f := deriv (gaussianConcentrationTruncation R) (F x) *
      coordinateDerivative (coordinateDerivative (coordinateDerivative F i) j) k x
    have ha : |a| ≤ H x ^ 3 := by
      dsimp [a]
      have heq : deriv (deriv (deriv (gaussianConcentrationTruncation R))) (F x) *
          coordinateDerivative F k x * coordinateDerivative F j x * coordinateDerivative F i x =
          deriv (deriv (deriv (gaussianConcentrationTruncation R))) (F x) *
            (coordinateDerivative F k x * coordinateDerivative F j x *
              coordinateDerivative F i x) := by ring
      rw [heq, abs_mul]
      calc
        |deriv (deriv (deriv (gaussianConcentrationTruncation R))) (F x)| *
          |coordinateDerivative F k x * coordinateDerivative F j x * coordinateDerivative F i x| ≤
          1 * H x ^ 3 :=
          mul_le_mul (abs_deriv3_gaussianConcentrationTruncation_le
            (R := R) (s := F x) hR)
            (hHcube_prod (i := k) (j := j) (k := i) x)
            (abs_nonneg _) (by positivity)
        _ = H x ^ 3 := by ring
    have hsecondTerm {a₁ b₁ c₁ : ℝ} (ha₁ : |a₁| ≤ 1)
        (hb₁ : |b₁| ≤ H x) (hc₁ : |c₁| ≤ H x) :
        |a₁ * b₁ * c₁| ≤ H x ^ 2 := by
      rw [abs_mul, abs_mul]
      calc
        |a₁| * |b₁| * |c₁| ≤ 1 * H x * H x := by gcongr
        _ = H x ^ 2 := by ring
    have hb : |b| ≤ H x ^ 2 := by
      exact hsecondTerm
        (a₁ := deriv (deriv (gaussianConcentrationTruncation R)) (F x))
        (b₁ := coordinateDerivative (coordinateDerivative F j) k x)
        (c₁ := coordinateDerivative F i x)
        (abs_deriv2_gaussianConcentrationTruncation_le (R := R) (s := F x) hR)
        (by simpa [H, T] using htwo j k x)
        (by simpa [H, T] using hone i x)
    have hc : |c| ≤ H x ^ 2 := by
      exact hsecondTerm
        (a₁ := deriv (deriv (gaussianConcentrationTruncation R)) (F x))
        (b₁ := coordinateDerivative F j x)
        (c₁ := coordinateDerivative (coordinateDerivative F i) k x)
        (abs_deriv2_gaussianConcentrationTruncation_le (R := R) (s := F x) hR)
        (by simpa [H, T] using hone j x)
        (by simpa [H, T] using htwo i k x)
    have he : |e| ≤ H x ^ 2 := by
      exact hsecondTerm
        (a₁ := deriv (deriv (gaussianConcentrationTruncation R)) (F x))
        (b₁ := coordinateDerivative F k x)
        (c₁ := coordinateDerivative (coordinateDerivative F i) j x)
        (abs_deriv2_gaussianConcentrationTruncation_le (R := R) (s := F x) hR)
        (by simpa [H, T] using hone k x)
        (by simpa [H, T] using htwo i j x)
    have hf : |f| ≤ H x := by
      rw [abs_mul]
      calc
        |deriv (gaussianConcentrationTruncation R) (F x)| *
            |coordinateDerivative (coordinateDerivative (coordinateDerivative F i) j) k x| ≤
              1 * H x :=
          mul_le_mul (abs_deriv_gaussianConcentrationTruncation_le
            (R := R) (s := F x) hRpos)
            (by simpa [H, T] using hthree i j k x) (abs_nonneg _) (by norm_num)
        _ = H x := by ring
    have htriangle : |a + b + c + e + f| ≤
        |a| + |b| + |c| + |e| + |f| := by
      have h₁ := abs_add_le (a + b + c + e) f
      have h₂ := abs_add_le (a + b + c) e
      have h₃ := abs_add_le (a + b) c
      have h₄ := abs_add_le a b
      nlinarith
    change |a + b + c + e + f| ≤ C' * T x ^ (3 * d)
    calc
      |a + b + c + e + f| ≤ H x ^ 3 + 3 * H x ^ 2 + H x := by
        calc
          |a + b + c + e + f| ≤ |a| + |b| + |c| + |e| + |f| := htriangle
          _ ≤ H x ^ 3 + 3 * H x ^ 2 + H x := by nlinarith
      _ ≤ (C ^ 3 + 3 * C ^ 2 + C) * T x ^ (3 * d) := by
        have h := add_le_add (hH3 x)
          (add_le_add (add_le_add (hH2 x) (hH2 x))
            (add_le_add (hH2 x) (hH1 x)))
        nlinarith [h]
      _ ≤ C' * T x ^ (3 * d) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C']
        nlinarith [hR, hC]
  refine ⟨hcont', C', ?_, 3 * d, ?_, ?_, ?_, ?_⟩
  · dsimp [C']
    positivity
  · exact hzero'
  · exact hone'
  · exact htwo'
  · exact hthree'

end ASDExplicitGamma.Gaussian
