module

public import ASDExplicitGamma.Native.GenericSourceMeans

/-! Monotonicity of the scalar mean terms on the finite source domain. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- The full mean forcing is increasing in its actual trace cap and clock,
including the linear and quadratic rare terms. -/
theorem native_source_mean_L_mono (h : ℕ) (epsilon x y e f : ℝ)
    (hepsilon : 0 ≤ epsilon) (hx : 0 ≤ x) (hxy : x ≤ y)
    (he : 0 ≤ e) (hef : e ≤ f) :
    nativeSourceMeanL h epsilon x e ≤ nativeSourceMeanL h epsilon y f := by
  let A := 2*(h:ℝ)*nativeSourceB128+4*nativeSourceMeanC+2*(h:ℝ)*epsilon+
    (2*nativeSourceK+2*nativeSourceB128*nativeSourceM)*(4*epsilon)+nativeSourceM*(4*epsilon^2)
  let B := (2*nativeSourceK+2*nativeSourceB128*nativeSourceM)*epsilon+nativeSourceM*epsilon^2
  have hA : 0 ≤ A := by
    dsimp [A,nativeSourceB128,nativeSourceMeanC,nativeSourceK,nativeSourceM]
    positivity
  have hB : 0 ≤ B := by dsimp [B,nativeSourceK,nativeSourceB128,nativeSourceM]; positivity
  have hform (z q : ℝ) : nativeSourceMeanL h epsilon z q=q*(A+B*z) := by
    dsimp [nativeSourceMeanL,nativeSourceMeanR,A,B]
    ring
  rw [hform,hform]
  exact mul_le_mul hef (add_le_add (le_refl A) (mul_le_mul_of_nonneg_left hxy hB))
    (add_nonneg hA (mul_nonneg hB hx)) (he.trans hef)

/-- The unframed exponential/phi1 source solution is increasing in its
nonnegative starting mean, trace cap and clock. -/
theorem native_source_mean_solution_mono (h : ℕ) (a a' epsilon x y e f : ℝ)
    (ha : 0 ≤ a) (haa : a ≤ a') (hepsilon : 0 ≤ epsilon)
    (hx : 0 ≤ x) (hxy : x ≤ y) (he : 0 ≤ e) (hef : e ≤ f) :
    a*Real.exp (e*nativeSourceMeanC)+nativeSourceMeanL h epsilon x e*nativeSourcePhiOne (e*nativeSourceMeanC) ≤
      a'*Real.exp (f*nativeSourceMeanC)+nativeSourceMeanL h epsilon y f*nativeSourcePhiOne (f*nativeSourceMeanC) := by
  have hc : 0 ≤ nativeSourceMeanC := by
    norm_num [nativeSourceMeanC,nativeSourceK,nativeSourceM,nativeSourceB128]
  have harg := mul_le_mul_of_nonneg_right hef hc
  have hL := native_source_mean_L_mono h epsilon x y e f hepsilon hx hxy he hef
  have hL0 : 0 ≤ nativeSourceMeanL h epsilon x e := by
    dsimp [nativeSourceMeanL,nativeSourceMeanR,nativeSourceMeanC,nativeSourceK,nativeSourceM,nativeSourceB128]
    positivity
  have hf0 : 0 ≤ nativeSourceMeanL h epsilon y f := hL0.trans hL
  exact add_le_add
    (mul_le_mul haa (Real.exp_le_exp.mpr harg) (Real.exp_pos _).le (ha.trans haa))
    (mul_le_mul hL (native_source_phiOne_mono (mul_nonneg he hc) harg)
      (native_source_phiOne_nonneg _ (mul_nonneg he hc)) hf0)

end
end ASDExplicitGamma.Native
