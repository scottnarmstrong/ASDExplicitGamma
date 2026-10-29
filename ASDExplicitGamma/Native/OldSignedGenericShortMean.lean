module

public import ASDExplicitGamma.Native.OldSignedGenericShortCaps
public import ASDExplicitGamma.Native.GenericSourceMeanTransport

/-! A coarse affine initial-mean envelope from generic producers alone. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

private theorem phiOne_le_exp (c : ℝ) (hc : 0≤c) :
    nativeSourcePhiOne c ≤ Real.exp c := by
  rcases hc.eq_or_lt with rfl | hc
  · rw [native_source_phiOne_zero,Real.exp_zero]
  · have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-c)) (Real.exp_pos c).le
    have he : Real.exp (-c)*Real.exp c=1 := by
      rw [←Real.exp_add]; simp only [neg_add_cancel,Real.exp_zero]
    rw [he] at hh
    apply le_of_mul_le_mul_left (a := c) ?_ hc
    rw [native_source_phiOne_mul]
    linarith only [hh]

private theorem exp_short (c : ℝ) (hc : c≤51/5000) : Real.exp c≤1011/1000 := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-c)) (Real.exp_pos c).le
  have he : Real.exp (-c)*Real.exp c=1 := by
    rw [←Real.exp_add]; simp only [neg_add_cancel,Real.exp_zero]
  rw [he] at hh
  have hmul := mul_le_mul_of_nonneg_right hc (Real.exp_pos c).le
  nlinarith only [hh,hmul]

private theorem generic_mean_R_short (h : ℕ) (hh : h≤70) (e x : ℝ)
    (he0 : 0≤e) (he : e≤17/10000) (hx0 : 0≤x) (hx : x≤1000000) :
    nativeSourceMeanR h (3/10^46) x e ≤ 1/10^12 := by
  have hhR : (h:ℝ)≤70 := by exact_mod_cast hh
  have heh := mul_le_mul_of_nonneg_left hhR he0
  have hex := mul_le_mul he hx hx0 (by norm_num : (0:ℝ)≤17/10000)
  unfold nativeSourceMeanR nativeSourceK nativeSourceB128 nativeSourceM
  nlinarith only [heh,hex,he]

/-- A deliberately coarse affine bound for the entire short generic prefix.
The four individual-cap passes are retained through their proved raw majorant. -/
theorem old_signed_generic_short_mean (h : ℕ) (hh : h≤70) :
    nativeSourceGenericMeanProfile (17/50000) 1 h ≤ (11/100:ℝ)+(3/500)*(h:ℝ) := by
  let e := nativeSourceGenericVarianceCap (17/50000) h
  let x := nativeSourceGenericIndividualProfile (17/50000) 1 h
  let C := nativeSourceMeanC
  let L := nativeSourceMeanL h (3/10^46) x e
  let E := nativeSourceE (17/50000) h
  have hc := old_signed_generic_short_variance_full h hh
  have hx := old_signed_generic_individual_short h hh
  have hE := old_signed_generic_E_short h (by omega)
  have hC0 : 0≤C := by norm_num [C,nativeSourceMeanC,nativeSourceK,nativeSourceM,nativeSourceB128]
  have hC6 : C≤6 := by norm_num [C,nativeSourceMeanC,nativeSourceK,nativeSourceM,nativeSourceB128]
  have he0 : 0≤e := hc.1
  have he : e≤17/10000 := hc.2.1
  have hmul := mul_le_mul he hC6 hC0 (by norm_num : (0:ℝ)≤17/10000)
  have heC : e*C≤51/5000 := by linarith only [hmul]
  have hexp := exp_short (e*C) heC
  have hphi := (phiOne_le_exp (e*C) (mul_nonneg he0 hC0)).trans hexp
  have hR := generic_mean_R_short h hh e x he0 he hx.1 hx.2
  have hL0 : 0≤L := by
    dsimp [L,nativeSourceMeanL,nativeSourceMeanR,nativeSourceMeanC,nativeSourceK,nativeSourceM,nativeSourceB128]
    have hx0 : 0≤x := hx.1
    positivity
  have hL : L≤(17/10000)*(3*(h:ℝ)+24)+1/10^12 := by
    have hlinear : 2*(h:ℝ)*nativeSourceB128+4*C≤3*(h:ℝ)+24 := by
      dsimp [nativeSourceB128]
      nlinarith only [hC6,Nat.cast_nonneg (α := ℝ) h]
    have hprod := mul_le_mul he hlinear
      (by dsimp [C,nativeSourceMeanC,nativeSourceK,nativeSourceM,nativeSourceB128]; positivity)
      (by norm_num : (0:ℝ)≤17/10000)
    dsimp only [L,nativeSourceMeanL]
    linarith only [hprod,hR]
  have hinner := add_le_add (mul_le_mul_of_nonneg_left hexp (by norm_num : (0:ℝ)≤3/50))
    (mul_le_mul hL hphi (native_source_phiOne_nonneg _ (mul_nonneg he0 hC0))
      (by positivity : (0:ℝ)≤(17/10000)*(3*(h:ℝ)+24)+1/10^12))
  have hinner0 : 0≤(3/50:ℝ)*Real.exp (e*C)+L*nativeSourcePhiOne (e*C) :=
    add_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (mul_nonneg hL0 (native_source_phiOne_nonneg _ (mul_nonneg he0 hC0)))
  have htotal := mul_le_mul hE.2 hinner hinner0 (by norm_num : (0:ℝ)≤53/50)
  unfold nativeSourceGenericMeanProfile
  rw [ite_eq_left (by omega : h≤160)]
  change E*((3/50:ℝ)*1*Real.exp (e*C)+L*nativeSourcePhiOne (e*C))≤_
  rw [mul_one]
  apply htotal.trans
  nlinarith only [Nat.cast_nonneg (α := ℝ) h]

end
end ASDExplicitGamma.Native
