module

public import ASDExplicitGamma.Inverse.RawShellPureFluxRows
public import ASDExplicitGamma.Inverse.RawShellSourceAlgebra

/-! Retained depth decay in the actual OLD p20 remainder coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Inverse
noncomputable section

/-- The larger two-source eigenvalue is bounded without discarding its
quadratic homogeneity in the covariance coefficients. -/
theorem old_signed_remainder_mu_le (H D A B : ℝ)
    (hH : 0≤H) (hD : 0≤D) (hA : 0≤A) (hB : 0≤B) :
    rawTraceRemainderMu H D A B ≤ H*A^2+D*A*B := by
  have hx : 0≤H*A^2 := mul_nonneg hH (sq_nonneg A)
  have hy : 0≤D*A*B := mul_nonneg (mul_nonneg hD hA) hB
  have hr : Real.sqrt (H^2*A^4+4*D^2*A^2*B^2) ≤ H*A^2+2*(D*A*B) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [mul_nonneg hx hy]
  unfold rawTraceRemainderMu
  linarith only [hr]

/-- The literal source covariance coefficients retain one inverse spatial
scale, with all numerical square-root bounds proved. -/
theorem old_signed_remainder_AB_decay (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    rawTraceRemainderA (z/729) (z/729) ≤ (13/500)*z ∧
    rawTraceRemainderB (z/729) (z/729) ≤ (21/1000)*z := by
  have h78 : Real.sqrt (78/10:ℝ) ≤ 14/5 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h156 : Real.sqrt (156/5:ℝ) ≤ 28/5 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h46488 : Real.sqrt (46488/25:ℝ) ≤ 44 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h785 : Real.sqrt (78/5:ℝ) ≤ 4 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have h23244 : Real.sqrt (23244/25:ℝ) ≤ 31 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hz2 : z^2≤z := by nlinarith only [mul_nonneg hz (sub_nonneg.mpr hz1)]
  have hlinear (c d : ℝ) (hc : c≤d) : c*(z/729)≤d*(z/729) :=
    mul_le_mul_of_nonneg_right hc (div_nonneg hz (by norm_num))
  have hquad (c d : ℝ) (hc : c≤d) : c*(z/729)^2≤d*(z/729)^2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg _)
  have hA0 := hlinear _ _ h78
  have hA1 := hlinear _ _ h156
  have hA2 := hquad _ _ h46488
  have hB1 := hlinear _ _ h785
  have hB2 := hquad _ _ h23244
  constructor
  · unfold rawTraceRemainderA
    nlinarith only [hA0,hA1,hA2,hz2,hz]
  · unfold rawTraceRemainderB
    nlinarith only [hA0,hB1,hB2,hz2,hz]

/-- The covariance derivative coefficient retains two inverse spatial scales. -/
theorem old_signed_remainder_kappa_decay (z : ℝ) :
    rawTraceRemainderKappaF (z/729) (z/729) ≤ (1/10000)*z^2 := by
  have hs : (7/5:ℝ)≤Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hu : Real.sqrt 2≤(3/2:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hdiv : (78/5:ℝ)/Real.sqrt 2≤78/7 := by
    apply (div_le_iff₀ (by positivity : 0<Real.sqrt 2)).mpr
    nlinarith only [hs]
  have h1 := mul_le_mul_of_nonneg_right hdiv (sq_nonneg (z/729))
  have h2 := mul_le_mul_of_nonneg_right hu (sq_nonneg (z/729))
  unfold rawTraceRemainderKappaF
  nlinarith only [h1,h2,sq_nonneg z]

/-- The physical two-source eigenvalue has the same quadratic depth decay. -/
theorem old_signed_remainder_mu_decay (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
      (rawTraceRemainderA (z/729) (z/729)) (rawTraceRemainderB (z/729) (z/729)) ≤
      (1/200)*z^2 := by
  let A := rawTraceRemainderA (z/729) (z/729)
  let B := rawTraceRemainderB (z/729) (z/729)
  have hA : 0≤A := by dsimp [A,rawTraceRemainderA]; positivity
  have hB : 0≤B := by dsimp [B,rawTraceRemainderB]; positivity
  have hH : 0≤rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
  have hD : 0≤rawTraceRemainderD0 := by unfold rawTraceRemainderD0; positivity
  have hD4 : rawTraceRemainderD0≤4 := by
    have hs : Real.sqrt rawTraceRemainderH0≤8/5 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num [rawTraceRemainderH0]⟩
    unfold rawTraceRemainderD0 rawTraceRemainderH0
    unfold rawTraceRemainderH0 at hs
    linarith only [hs]
  have hab := old_signed_remainder_AB_decay z hz hz1
  have ha2 := pow_le_pow_left₀ hA hab.1 2
  have hab2 := mul_le_mul hab.1 hab.2 hB (by positivity : (0:ℝ)≤(13/500)*z)
  have hh := old_signed_remainder_mu_le rawTraceRemainderH0 rawTraceRemainderD0 A B hH hD hA hB
  have hbase := mul_le_mul_of_nonneg_left ha2 hH
  have hcross := (mul_le_mul_of_nonneg_left hab2 hD).trans
    (mul_le_mul_of_nonneg_right hD4 (by positivity : (0:ℝ)≤((13/500)*z)*((21/1000)*z)))
  unfold rawTraceRemainderH0 at hbase
  change rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0 A B≤_
  change rawTraceRemainderD0*(A*B) ≤ _ at hcross
  simp only [rawTraceRemainderH0] at hh ⊢
  nlinarith only [hh,hbase,hcross,sq_nonneg z]

end
end ASDExplicitGamma.Native
