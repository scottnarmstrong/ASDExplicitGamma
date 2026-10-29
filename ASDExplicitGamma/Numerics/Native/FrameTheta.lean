module
public import ASDExplicitGamma.Numerics.Native.Basic
import Mathlib.Tactic.FieldSimp

/-! The source true-frame inequality under proportional variance scaling. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

noncomputable def nativeFrameReal (a t : ℝ) : ℝ :=
  let r := 1/(1-a)
  let c := (r+1/r)/2
  let d := (r-1/r)/2
  c*t+d*Real.sqrt (t*(t+8))+4*(c-1)

noncomputable def nativeFrameQuadratic (a : ℝ) : ℝ := a^2/(2*(1-a))

theorem nativeFrameReal_formula (a t : ℝ) (ha : a < 1) :
    nativeFrameReal a t = t+nativeFrameQuadratic a*t+
      (a+nativeFrameQuadratic a)*Real.sqrt (t*(t+8))+4*nativeFrameQuadratic a := by
  unfold nativeFrameReal nativeFrameQuadratic
  have h : 1-a ≠ 0 := ne_of_gt (sub_pos.mpr ha)
  simp only [one_div,inv_inv]
  field_simp
  ring

theorem nativeFrameQuadratic_nonneg (a : ℝ) (ha : a < 1) : 0 ≤ nativeFrameQuadratic a :=
  div_nonneg (sq_nonneg _) (by linarith)

theorem nativeFrameQuadratic_theta (a θ : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    nativeFrameQuadratic (θ*a) ≤ θ*nativeFrameQuadratic a := by
  have hθa : θ*a ≤ a := mul_le_of_le_one_left ha0 hθ1
  have hd : 0 < 2*(1-a) := by linarith
  have hdθ : 0 < 2*(1-θ*a) := by linarith
  have hsmall : (θ*a)^2 ≤ θ*a^2 := by
    nlinarith only [sq_nonneg a,mul_nonneg hθ0 (sub_nonneg.mpr hθ1)]
  unfold nativeFrameQuadratic
  calc
    (θ*a)^2/(2*(1-θ*a)) ≤ (θ*a)^2/(2*(1-a)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) hd (by linarith)
    _ ≤ (θ*a^2)/(2*(1-a)) := div_le_div_of_nonneg_right hsmall hd.le
    _ = θ*(a^2/(2*(1-a))) := by ring

theorem native_frame_theta (a t θ : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (ht : 0 ≤ t) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    nativeFrameReal (θ*a) (θ*t) ≤ θ*nativeFrameReal a t := by
  have hθa : θ*a ≤ a := mul_le_of_le_one_left ha0 hθ1
  have hθt : θ*t ≤ t := mul_le_of_le_one_left ht hθ1
  have hqt := nativeFrameQuadratic_theta a θ ha0 ha1 hθ0 hθ1
  have hq := nativeFrameQuadratic_nonneg a ha1
  have hqθ := nativeFrameQuadratic_nonneg (θ*a) (lt_of_le_of_lt hθa ha1)
  have hqle : nativeFrameQuadratic (θ*a) ≤ nativeFrameQuadratic a :=
    hqt.trans (mul_le_of_le_one_left hq hθ1)
  have hs : Real.sqrt ((θ*t)*(θ*t+8)) ≤ Real.sqrt (t*(t+8)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul hθt (by linarith) (by positivity) ht
  have hp' : nativeFrameQuadratic (θ*a)*(θ*t) ≤ θ*(nativeFrameQuadratic a*t) := by
    calc
      nativeFrameQuadratic (θ*a)*(θ*t) ≤ nativeFrameQuadratic a*(θ*t) :=
        mul_le_mul_of_nonneg_right hqle (mul_nonneg hθ0 ht)
      _ = θ*(nativeFrameQuadratic a*t) := by ring
  have hm : (θ*a+nativeFrameQuadratic (θ*a))*Real.sqrt ((θ*t)*(θ*t+8)) ≤
      θ*((a+nativeFrameQuadratic a)*Real.sqrt (t*(t+8))) := by
    calc
      _ ≤ (θ*a+θ*nativeFrameQuadratic a)*Real.sqrt (t*(t+8)) :=
        mul_le_mul (add_le_add le_rfl hqt) hs (Real.sqrt_nonneg _)
          (by positivity)
      _ = _ := by ring
  rw [nativeFrameReal_formula _ _ (lt_of_le_of_lt hθa ha1),nativeFrameReal_formula _ _ ha1]
  nlinarith only [hp',hm,hqt]

end ASDExplicitGamma.Numerics.Native
