module

public import ASDExplicitGamma.Triadic.DiagLinear
public import ASDExplicitGamma.Triadic.PlanarPositiveGradient

/-! Weighted Hilbert inequalities for the exact scalar broken-energy assembly. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory

noncomputable section

theorem diagScalarYoung {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    (x-y)^2 ≤ (1+t)*x^2+(1+t⁻¹)*y^2 := by
  have hgap : (1+t)*x^2+(1+t⁻¹)*y^2-(x-y)^2 = t⁻¹*(t*x+y)^2 := by
    field_simp
    ring
  have h := mul_nonneg (inv_nonneg.mpr ht.le) (sq_nonneg (t*x+y))
  rw [← hgap] at h
  exact sub_nonneg.mp h

/-- Weighted two-term L2 inequality, with no triangle loss. -/
theorem diagEnergy_sub_le (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q))
    {t : ℝ} (ht : 0 < t) :
    energy Q (fun x => f x-g x) ≤ (1+t)*energy Q f+(1+t⁻¹)*energy Q g := by
  have hff : Integrable (fun x => f x^2) (normalizedCubeMeasure Q) := by
    convert hf.integrable_mul hf using 1
    funext x
    exact pow_two (f x)
  have hgg : Integrable (fun x => g x^2) (normalizedCubeMeasure Q) := by
    convert hg.integrable_mul hg using 1
    funext x
    exact pow_two (g x)
  have hfg : Integrable (fun x => (f x-g x)^2) (normalizedCubeMeasure Q) := by
    convert (hf.sub hg).integrable_mul (hf.sub hg) using 1
    funext x
    exact pow_two (f x-g x)
  simp only [energy_eq_integral_sq]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hff.const_mul (1+t)) (hgg.const_mul (1+t⁻¹))]
  apply integral_mono_ae hfg ((hff.const_mul (1+t)).add (hgg.const_mul (1+t⁻¹)))
  exact Filter.Eventually.of_forall fun x => diagScalarYoung ht (f x) (g x)

/-- H1 input subtraction commutes with every exact Haar increment. -/
theorem diagH1_increment_sub (Q : TriadicCube 2) (u v : H1Function (openCubeSet Q)) (k : ℕ) :
    cubeIncrement Q k (u-v).toFun = fun x => cubeIncrement Q k u.toFun x-cubeIncrement Q k v.toFun x := by
  have hp (n : ℕ) : cubeProjection Q n (u-v).toFun =
      fun x => cubeProjection Q n u.toFun x-cubeProjection Q n v.toFun x := by
    funext x
    rw [← diagProjectionLinear_apply Q n, map_sub]
    change diagProjectionLinear Q n u x-diagProjectionLinear Q n v x = _
    rw [diagProjectionLinear_apply, diagProjectionLinear_apply]
  cases k with
  | zero => simpa only [cubeIncrement_zero] using hp 0
  | succ k =>
      rw [cubeIncrement_succ, hp (k+1), hp k]
      funext x
      simp only [cubeIncrement_succ]
      ring

/-- Positive Haar energy obeys the same weighted Hilbert inequality on H1 cells. -/
theorem diagPrimalEnergy_sub_le (Q : TriadicCube 2) (u v : H1Function (openCubeSet Q))
    {t : ℝ} (ht : 0 < t) :
    primalEnergy Q (Real.sqrt 3) (u-v).toFun ≤
      (1+t)*primalEnergy Q (Real.sqrt 3) u.toFun+(1+t⁻¹)*primalEnergy Q (Real.sqrt 3) v.toFun := by
  have hs (w : H1Function (openCubeSet Q)) := positiveHaarIncrementSeries_summable Q
    w.memL2_normalizedCubeMeasure w.grad_memL2_normalizedCubeMeasure w.hasWeakGradient
  have hpoint (k : ℕ) : energy Q (cubeIncrement Q k (u-v).toFun) ≤
      (1+t)*energy Q (cubeIncrement Q k u.toFun)+(1+t⁻¹)*energy Q (cubeIncrement Q k v.toFun) := by
    rw [diagH1_increment_sub]
    exact diagEnergy_sub_le Q (increment_memLp Q k u.toFun) (increment_memLp Q k v.toFun) ht
  have hterm (k : ℕ) : (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (u-v).toFun) ≤
      (1+t)*((Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) u.toFun)) +
      (1+t⁻¹)*((Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) v.toFun)) := by
    have h := mul_le_mul_of_nonneg_left (hpoint (k+1))
      (pow_nonneg (Real.sqrt_nonneg (3:ℝ)) (k+1))
    convert h using 1
    ring
  have hsum := (hs (u-v)).tsum_le_tsum hterm
    (((hs u).mul_left (1+t)).add ((hs v).mul_left (1+t⁻¹)))
  rw [((hs u).mul_left (1+t)).tsum_add ((hs v).mul_left (1+t⁻¹)),
    tsum_mul_left, tsum_mul_left] at hsum
  unfold primalEnergy
  have h0 := hpoint 0
  linarith only [h0, hsum]

end

end ASDExplicitGamma.Triadic
