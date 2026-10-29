module

public import ASDExplicitGamma.Gaussian.C2Averaging

/-! # Finite sums and integer powers of the source response tests -/

@[expose] public section

namespace ASDExplicitGamma.Gaussian

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Constants belong to the source test class. -/
theorem c2_polynomial_const (c : ℝ) : HasPolynomiallyBoundedC2Derivatives (fun _ : E => c) := by
  refine ⟨contDiff_const, |c|, abs_nonneg c, 0, fun x => by simp only [pow_zero, mul_one, le_refl], ?_, ?_⟩
  · intro x
    simp only [fderiv_const_apply, norm_zero, pow_zero, mul_one]
    exact abs_nonneg c
  · intro x u w
    simp only [fderiv_const_apply, zero_apply, abs_zero, pow_zero, mul_one]
    positivity

private theorem c2_directional_diff {f : E → ℝ} (hf : ContDiff ℝ 2 f) (w : E) :
    Differentiable ℝ (fun x => fderiv ℝ f x w) :=
  ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const).differentiable_one

/-- Products preserve the source polynomial C² bounds. -/
theorem c2_polynomial_mul {f g : E → ℝ}
    (hf : HasPolynomiallyBoundedC2Derivatives f) (hg : HasPolynomiallyBoundedC2Derivatives g) :
    HasPolynomiallyBoundedC2Derivatives (fun x => f x * g x) := by
  obtain ⟨hf2, C, hC, d, hvf, hdf, hhf⟩ := hf
  obtain ⟨hg2, B, hB, e, hvg, hdg, hhg⟩ := hg
  have hfd := hf2.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hgd := hg2.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hscalar_f (x u : E) : |fderiv ℝ f x u| ≤ C * (1 + ‖x‖) ^ d * ‖u‖ :=
    ((fderiv ℝ f x).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hdf x) (norm_nonneg u))
  have hscalar_g (x u : E) : |fderiv ℝ g x u| ≤ B * (1 + ‖x‖) ^ e * ‖u‖ :=
    ((fderiv ℝ g x).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hdg x) (norm_nonneg u))
  have hderiv (x : E) : fderiv ℝ (fun y => f y * g y) x =
      f x • fderiv ℝ g x + g x • fderiv ℝ f x := fderiv_fun_mul (hfd x) (hgd x)
  refine ⟨hf2.mul hg2, 4 * C * B, by positivity, d + e, ?_, ?_, ?_⟩
  · intro x
    rw [abs_mul]
    calc
      |f x| * |g x| ≤ (C * (1 + ‖x‖) ^ d) * (B * (1 + ‖x‖) ^ e) :=
        mul_le_mul (hvf x) (hvg x) (abs_nonneg _) (by positivity)
      _ ≤ 4 * C * B * (1 + ‖x‖) ^ (d + e) := by
        rw [pow_add]
        nlinarith [mul_nonneg (mul_nonneg hC hB) (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) d) (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) e))]
  · intro x
    rw [hderiv]
    calc
      _ ≤ ‖f x • fderiv ℝ g x‖ + ‖g x • fderiv ℝ f x‖ := norm_add_le _ _
      _ = |f x| * ‖fderiv ℝ g x‖ + |g x| * ‖fderiv ℝ f x‖ := by rw [norm_smul, norm_smul]; rfl
      _ ≤ (C * (1 + ‖x‖) ^ d) * (B * (1 + ‖x‖) ^ e) +
          (B * (1 + ‖x‖) ^ e) * (C * (1 + ‖x‖) ^ d) := by gcongr <;> first | exact hvf x | exact hdg x | exact hvg x | exact hdf x
      _ ≤ 4 * C * B * (1 + ‖x‖) ^ (d + e) := by
        rw [pow_add]
        nlinarith [mul_nonneg (mul_nonneg hC hB) (mul_nonneg (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) d) (pow_nonneg (by positivity : 0 ≤ 1 + ‖x‖) e))]
  · intro x u w
    have hfun : (fun y => fderiv ℝ (fun z => f z * g z) y w) =
        fun y => f y * fderiv ℝ g y w + g y * fderiv ℝ f y w := by
      funext y
      rw [hderiv]
      simp only [add_apply, smul_apply, smul_eq_mul]
    have hfg : DifferentiableAt ℝ (fun y => f y * fderiv ℝ g y w) x := (hfd x).mul (c2_directional_diff hg2 w x)
    have hgf : DifferentiableAt ℝ (fun y => g y * fderiv ℝ f y w) x := (hgd x).mul (c2_directional_diff hf2 w x)
    rw [hfun, fderiv_fun_add hfg hgf, add_apply,
      fderiv_fun_mul (hfd x) (c2_directional_diff hg2 w x),
      fderiv_fun_mul (hgd x) (c2_directional_diff hf2 w x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    calc
      _ ≤ |f x| * |fderiv ℝ (fun y => fderiv ℝ g y w) x u| +
          |fderiv ℝ g x w| * |fderiv ℝ f x u| +
          (|g x| * |fderiv ℝ (fun y => fderiv ℝ f y w) x u| +
          |fderiv ℝ f x w| * |fderiv ℝ g x u|) := by
        exact (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul]))
          ((abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul])))
      _ ≤ (C * (1 + ‖x‖) ^ d) * (B * (1 + ‖x‖) ^ e * ‖u‖ * ‖w‖) +
          (B * (1 + ‖x‖) ^ e * ‖w‖) * (C * (1 + ‖x‖) ^ d * ‖u‖) +
          ((B * (1 + ‖x‖) ^ e) * (C * (1 + ‖x‖) ^ d * ‖u‖ * ‖w‖) +
          (C * (1 + ‖x‖) ^ d * ‖w‖) * (B * (1 + ‖x‖) ^ e * ‖u‖)) := by
        gcongr <;> first | exact hvf x | exact hhg x u w | exact hscalar_g x w | exact hscalar_f x u | exact hvg x | exact hhf x u w | exact hscalar_f x w | exact hscalar_g x u
      _ = _ := by rw [pow_add]; ring

/-- Every natural power, including r=1, is covered without a positivity side condition. -/
theorem c2_polynomial_pow {f : E → ℝ} (hf : HasPolynomiallyBoundedC2Derivatives f) (r : ℕ) :
    HasPolynomiallyBoundedC2Derivatives (fun x => f x ^ r) := by
  induction r with
  | zero => simpa only [pow_zero] using c2_polynomial_const (E := E) 1
  | succ r ih => simpa only [pow_succ] using c2_polynomial_mul ih hf

/-- Finite sums preserve the source test class. -/
theorem c2_polynomial_sum {ι : Type*} (s : Finset ι) (f : ι → E → ℝ)
    (hf : ∀ i ∈ s, HasPolynomiallyBoundedC2Derivatives (f i)) :
    HasPolynomiallyBoundedC2Derivatives (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using c2_polynomial_const (E := E) 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact hasPolynomiallyBoundedC2Derivatives_add (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Contractive deterministic coefficient maps preserve the same source C² polynomial bounds. -/
theorem c2_polynomial_comp_contraction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (hL : ∀ x, ‖L x‖ ≤ ‖x‖)
    {f : F → ℝ} (hf : HasPolynomiallyBoundedC2Derivatives f) :
    HasPolynomiallyBoundedC2Derivatives (fun x => f (L x)) := by
  obtain ⟨hf2, C, hC, d, hv, hd, hh⟩ := hf
  have hfd := hf2.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hnormL : ‖L‖ ≤ 1 := L.opNorm_le_bound (by norm_num) (fun x => by simpa only [one_mul] using hL x)
  have hpow (x : E) : (1 + ‖L x‖) ^ d ≤ (1 + ‖x‖) ^ d :=
    pow_le_pow_left₀ (by positivity) (show 1 + ‖L x‖ ≤ 1 + ‖x‖ by linarith [hL x]) d
  have hderiv (x : E) : fderiv ℝ (fun y => f (L y)) x =
      (fderiv ℝ f (L x)).comp L := (hfd (L x)).hasFDerivAt.comp x L.hasFDerivAt |>.fderiv
  refine ⟨hf2.comp L.contDiff, C, hC, d, ?_, ?_, ?_⟩
  · intro x
    exact (hv (L x)).trans (mul_le_mul_of_nonneg_left (hpow x) hC)
  · intro x
    rw [hderiv]
    calc
      _ ≤ ‖fderiv ℝ f (L x)‖ * ‖L‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ f (L x)‖ := mul_le_of_le_one_right (norm_nonneg _) hnormL
      _ ≤ _ := (hd (L x)).trans (mul_le_mul_of_nonneg_left (hpow x) hC)
  · intro x u w
    have hfun : (fun z => fderiv ℝ (fun y => f (L y)) z w) =
        fun z => fderiv ℝ f (L z) (L w) := by
      funext z
      rw [hderiv]
      rfl
    rw [hfun]
    have hD := (c2_directional_diff hf2 (L w) (L x)).hasFDerivAt.comp x L.hasFDerivAt
    rw [show fderiv ℝ (fun z => fderiv ℝ f (L z) (L w)) x = _ from hD.fderiv]
    change |fderiv ℝ (fun z => fderiv ℝ f z (L w)) (L x) (L u)| ≤ _
    exact (hh (L x) (L u) (L w)).trans (by
      gcongr
      · exact hL x
      · exact hL u
      · exact hL w)

/-- A single coordinate response is a polynomial C² test on a finite product. -/
theorem c2_polynomial_component {ι : Type*} [Fintype ι]
    {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    (i : ι) {f : F i → ℝ} (hf : HasPolynomiallyBoundedC2Derivatives f) :
    HasPolynomiallyBoundedC2Derivatives (fun x : ∀ i, F i => f (x i)) :=
  c2_polynomial_comp_contraction (ContinuousLinearMap.proj i) (fun x => norm_le_pi_norm x i) hf

end
end ASDExplicitGamma.Gaussian
