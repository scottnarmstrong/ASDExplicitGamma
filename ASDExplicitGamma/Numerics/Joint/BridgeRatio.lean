module

public import ASDExplicitGamma.Numerics.Scalar.Frames

/-! NU-BRIDGE-RATIO: the exact scalar shell-sum normalization and tail-scale comparison. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Joint

/-- A positive Taylor sum proves the Padé inequality needed by the shell normalization. -/
theorem exp_pade_lower (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1+t+t^2/3 ≤ (1-t+t^2/3)*Real.exp (2*t) := by
  let P := 1+2*t+2*t^2+(4/3)*t^3+(2/3)*t^4+(4/15)*t^5
  have hP : P ≤ Real.exp (2*t) := by
    have h := Real.sum_le_exp_of_nonneg (by linarith only [ht] : 0 ≤ 2*t) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    dsimp [P]
    nlinarith only [h]
  have hA : 0 ≤ 1-t+t^2/3 := by positivity
  have hprod := mul_le_mul_of_nonneg_left hP hA
  have hr : 0 ≤ (2/45 : ℝ)*t^5*((1-t)+2*t^2) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht _))
      (add_nonneg (sub_nonneg.mpr ht1) (by positivity))
  have heq : (1-t+t^2/3)*P-(1+t+t^2/3) = (2/45 : ℝ)*t^5*((1-t)+2*t^2) := by
    dsimp [P]
    ring
  linarith only [hprod,hr,heq]

/-- Exact second-order Taylor upper bound; the denominator is strictly positive. -/
theorem bernoulli_ratio_bounds (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    1 ≤ 2*t/(1-Real.exp (-2*t)) ∧
    2*t/(1-Real.exp (-2*t)) ≤ 1+t+t^2/3 := by
  have hd : 0 < 1-Real.exp (-2*t) := by
    have h := Real.exp_lt_one_iff.mpr (by linarith only [ht] : -2*t < 0)
    linarith only [h]
  constructor
  · apply (le_div_iff₀ hd).mpr
    have h := Real.add_one_le_exp (-2*t)
    linarith only [h]
  · apply (div_le_iff₀ hd).mpr
    have hp := exp_pade_lower t ht.le ht1
    have he : Real.exp (2*t) ≠ 0 := ne_of_gt (Real.exp_pos _)
    have hpos : 0 ≤ ((1-t+t^2/3)*Real.exp (2*t)-(1+t+t^2/3))/Real.exp (2*t) :=
      div_nonneg (sub_nonneg.mpr hp) (Real.exp_pos _).le
    have hid : ((1-t+t^2/3)*Real.exp (2*t)-(1+t+t^2/3))/Real.exp (2*t) =
        (1+t+t^2/3)*(1-Real.exp (-2*t))-2*t := by
      rw [show -2*t = -(2*t) by ring, Real.exp_neg]
      field_simp
      ring
    rw [hid] at hpos
    linarith only [hpos]

/-- The normalization factor in the exact geometric shell sum. -/
noncomputable def kappa (gamma : ℝ) : ℝ :=
  2*gamma*Real.log 3/(1-(3 : ℝ)^(-2*gamma))

/-- The source Taylor inequality gives all corridor gates, without a frame comparison. -/
theorem bridge_ratio_bounds (gamma : ℝ) (hg : 0 < gamma) (hgmax : gamma ≤ 17/50000) :
    1 ≤ kappa gamma ∧ kappa gamma < 8003/8000 ∧
    31*kappa gamma/50 > 1/4 ∧ (19/50 : ℝ) > 1/4 ∧
    (21/8)*kappa gamma < 168063/64000 ∧ (168063/64000 : ℝ) < 4 := by
  let t := gamma*Real.log 3
  have ht : 0 < t := mul_pos hg (Real.log_pos (by norm_num))
  have htmax : t ≤ 187/500000 := by
    have h1 := mul_le_mul_of_nonneg_left Scalar.log_three_small.2.le hg.le
    have h2 := mul_le_mul_of_nonneg_right hgmax (by norm_num : (0 : ℝ) ≤ 11/10)
    dsimp [t]
    linarith only [h1,h2]
  have ht1 : t ≤ 1 := by linarith only [htmax]
  have hk : kappa gamma = 2*t/(1-Real.exp (-2*t)) := by
    unfold kappa
    rw [Real.rpow_def_of_pos (by norm_num)]
    dsimp [t]
    rw [show Real.log 3 * (-2*gamma) = -2*(gamma*Real.log 3) by ring]
    ring
  obtain ⟨hl,hu⟩ := bernoulli_ratio_bounds t ht ht1
  rw [← hk] at hl hu
  have hsq : t^2 ≤ (187/500000 : ℝ)^2 :=
    pow_le_pow_left₀ ht.le htmax 2
  have hcap : kappa gamma < 8003/8000 := by
    linarith only [hu,htmax,hsq]
  refine ⟨hl,hcap,?_,by norm_num,?_,by norm_num⟩ <;> linarith only [hl,hcap]

/-- The second displayed weak-Orlicz scale is below the frozen T3 scale. -/
theorem bridge_tail_scale (gamma s : ℝ) (hg : 0 < gamma) (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.exp (-Real.log 2/(8192*gamma)) ≤
      (1/s^2)*Real.exp (-(1/2^48 : ℝ)/gamma) := by
  have hlog : (1/2 : ℝ) < Real.log 2 := by
    linarith only [log_two_enclosure.1]
  have hc : (1/2^48 : ℝ) ≤ Real.log 2/8192 := by linarith only [hlog]
  have harg := neg_le_neg (div_le_div_of_nonneg_right hc hg.le)
  have he : Real.exp (-Real.log 2/(8192*gamma)) ≤ Real.exp (-(1/2^48 : ℝ)/gamma) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div, div_div] using harg
  have hinv : (1 : ℝ) ≤ 1/s^2 :=
    (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith only [hs,hs1])
  exact he.trans (by simpa using mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le)

end ASDExplicitGamma.Numerics.Joint
