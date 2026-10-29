module

public import ASDExplicitGamma.Inverse.AssemblyDensitySeries
public import ASDExplicitGamma.Inverse.AssemblyMatrixBandProfile
public import ASDExplicitGamma.Inverse.AssemblyTraceNumerics

/-! Numerical profile cap for the all-height D2 density error. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
noncomputable section

private theorem density_three160_ge_ten75 :
    (10:ℝ)^75 ≤ (3:ℝ)^160 := by
  have hbase : (5*10^4:ℝ) ≤ (3:ℝ)^10 := by norm_num
  calc
    (10:ℝ)^75 ≤ (5*10^4)^16 := by norm_num
    _ ≤ ((3:ℝ)^10)^16 := pow_le_pow_left₀ (by positivity) hbase 16
    _ = (3:ℝ)^160 := by rw [← pow_mul]

private theorem density_localization_zero_cap :
    bandLocalizationCoefficient 4 0 ≤ 1 := by
  let A : ℝ := (3:ℝ)^11/384
  have hA : 0 < A := by dsimp [A]; positivity
  have ht := Real.pow_div_factorial_le_exp A hA.le 128
  have hp : 0 < A^128/(Nat.factorial 128:ℝ) := by positivity
  have hi := one_div_le_one_div_of_le hp ht
  have he : 1/(A^128/(Nat.factorial 128:ℝ)) =
      (Nat.factorial 128:ℝ)/A^128 := by field_simp
  have hexp : Real.exp (-A) ≤
      (Nat.factorial 128:ℝ)/A^128 := by
    calc
      _ = 1/Real.exp A := by simp only [Real.exp_neg, one_div]
      _ ≤ 1/(A^128/(Nat.factorial 128:ℝ)) := hi
      _ = _ := he
  have hrpow : (12000:ℝ)^(1/(2*(64:ℝ))) ≤ 12000 := by
    calc
      _ ≤ (12000:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1:ℝ)≤12000) (by norm_num)
      _ = 12000 := by rw [Real.rpow_one]
  have hsource : bandLocalizationCoefficient 4 0 ≤
      2*(80*4*64:ℝ)^4*12000* (Real.exp (-A))*(3:ℝ)^130 := by
    unfold bandLocalizationCoefficient bandOrderMajorant bandDensityEntrance
    norm_num [A]
    gcongr
    all_goals nlinarith [hrpow]
  calc
    _ ≤ 2*(80*4*64:ℝ)^4*12000*
        ((Nat.factorial 128:ℝ)/A^128)*(3:ℝ)^130 := by
      calc
        _ ≤ 2*(80*4*64:ℝ)^4*12000*Real.exp (-A)*(3:ℝ)^130 := hsource
        _ ≤ _ := by gcongr
    _ ≤ 1 := by norm_num [A, Nat.factorial]

private theorem density_localization_step (k : ℕ) :
    bandLocalizationCoefficient 2 (k+1) ≤
      bandLocalizationCoefficient 2 k := by
  let A : ℝ := (3:ℝ)^(11+k)/384
  have hA : 26 ≤ A := by
    dsimp [A]
    have hpow : (3:ℝ)^11 ≤ (3:ℝ)^(11+k) := by
      rw [pow_add]
      calc
        (3:ℝ)^11 = (3:ℝ)^11*1 := by ring
        _ ≤ (3:ℝ)^11*(3:ℝ)^k := by
          exact mul_le_mul_of_nonneg_left
            (one_le_pow₀ (by norm_num : (1:ℝ)≤3)) (by positivity)
    have hbase : (26:ℝ) ≤ (3:ℝ)^11/384 := by norm_num
    exact hbase.trans (div_le_div_of_nonneg_right hpow (by norm_num))
  have hpowA : (3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1))) = 3*A := by
    dsimp [A]
    rw [show 11+2*(k+1)=(12+k)+(k+1) by omega, pow_add,
      show 12+k=(11+k)+1 by omega, pow_succ, pow_succ]
    field_simp
    norm_num
  have hpowAk : (3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)) = A := by
    dsimp [A]
    rw [show 11+2*k=(11+k)+k by omega, pow_add]
    field_simp
    norm_num
  have hexp : Real.exp (-2*A) ≤ (3:ℝ)^(-26:ℝ) := by
    have hneg : -2*A ≤ -52 := by linarith
    have hmono : Real.exp (-2*A) ≤ Real.exp (-52) := Real.exp_le_exp.mpr hneg
    have htwo : (2:ℝ)^52 ≤ Real.exp (52:ℝ) := by
      rw [show (52:ℝ)=(52:ℕ)*1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 52
    have hinv := one_div_le_one_div_of_le (by positivity) htwo
    have h23 : (3:ℝ)^26 ≤ (2:ℝ)^52 := by norm_num
    have hinv' := one_div_le_one_div_of_le (by positivity) h23
    have hsmall : Real.exp (-52) ≤ ((3:ℝ)^26)⁻¹ := by
      calc
        _ = (Real.exp (52:ℝ))⁻¹ := by rw [Real.exp_neg]
        _ ≤ 1/(2:ℝ)^52 := by simpa only [one_div] using hinv
        _ ≤ ((3:ℝ)^26)⁻¹ := by simpa only [one_div] using hinv'
    have hresult : Real.exp (-2*A) ≤ ((3:ℝ)^26)⁻¹ := hmono.trans hsmall
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
    have hcast : (3:ℝ)^(26:ℝ)=(3:ℝ)^26 := by exact Real.rpow_natCast _ _
    rw [hcast]
    exact hresult
  have hrpow :
      (12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1)))) ≤
        (12000:ℝ)^(1/(2*(64*(3:ℝ)^k))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤12000)
    apply one_div_le_one_div_of_le (by positivity)
    have hk : (3:ℝ)^k ≤ (3:ℝ)^(k+1) := by
      rw [pow_succ]
      nlinarith [show 0 ≤ (3:ℝ)^k by positivity]
    nlinarith
  have hexponent :
      (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) =
        (3:ℝ)^24*(3:ℝ)^(2*((60+12*k+5:ℕ):ℝ)) := by
    have hcast :
        2*((60+12*(k+1)+5:ℕ):ℝ) =
          24+2*((60+12*k+5:ℕ):ℝ) := by
      push_cast
      ring
    rw [hcast, Real.rpow_add (by norm_num : (0:ℝ)<3)]
    have h24 : (3:ℝ)^(24:ℝ)=(3:ℝ)^24 := by
      exact Real.rpow_natCast _ _
    rw [h24]
  have hargA : -(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1))) = -(3*A) := by
    calc
      _ = -((3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) := by ring
      _ = -(3*A) := by rw [hpowA]
  have hargAk : -(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)) = -A := by
    calc
      _ = -((3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k))) := by ring
      _ = -A := by rw [hpowAk]
  have hstep :
      Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) ≤
        Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*(3:ℝ)^(-26:ℝ) := by
    rw [hargA,hargAk,show -(3*A)=(-A)+(-2*A) by ring,Real.exp_add]
    calc
      _ = Real.exp (-A)*Real.exp (-2*A) := by ring
      _ ≤ Real.exp (-A)*(3:ℝ)^(-26:ℝ) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)
  unfold bandLocalizationCoefficient bandOrderMajorant bandDensityEntrance
  have hcoeff : (80*2*(64*(3:ℝ)^(k+1)))^2 ≤
      9*(80*2*(64*(3:ℝ)^k))^2 := by
    rw [pow_succ]
    ring_nf
    exact le_rfl
  have hlocal :
      (12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
        Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) ≤
      (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
        Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*(3:ℝ)^(-26:ℝ) := by
    calc
      _ ≤ (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
          Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) :=
        mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)
      _ ≤ _ := by
        calc
          _ ≤ (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
              (Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
                (3:ℝ)^(-26:ℝ)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = _ := by ring
  calc
    _ = 2*((80*2*(64*(3:ℝ)^(k+1)))^2*
        (12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
        Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))))*
        (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) := by ring_nf
    _ ≤ 2*(9*(80*2*(64*(3:ℝ)^k))^2)*
        ((12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
          Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*(3:ℝ)^(-26:ℝ))*
        (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) := by
      have hlocal0 : 0 ≤ (12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1)))) *
          Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _)
      have hcoeff1 : 0 ≤ 9*(80*2*(64*(3:ℝ)^k))^2 :=
        mul_nonneg (by norm_num) (sq_nonneg _)
      have hcomb := mul_le_mul hcoeff hlocal hlocal0 hcoeff1
      have hscale := mul_le_mul_of_nonneg_left hcomb
        (show (0:ℝ) ≤ 2 by norm_num)
      have hscale' :
          2*((80*2*(64*(3:ℝ)^(k+1)))^2*
              ((12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
                Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))))) ≤
            (2*(9*(80*2*(64*(3:ℝ)^k))^2)) *
              ((12000:ℝ)^(1/(2*(64*(3:ℝ)^k))) *
                Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k))) *
                  (3:ℝ)^(-26:ℝ)) := by
        calc
          _ ≤ 2*(9*(80*2*(64*(3:ℝ)^k))^2 *
              ((12000:ℝ)^(1/(2*(64*(3:ℝ)^k))) *
                Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k))) *
                  (3:ℝ)^(-26:ℝ))) := hscale
          _ = _ := by ring
      have hterminal : 0 ≤ (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) := by
        positivity
      calc
        _ = (2*((80*2*(64*(3:ℝ)^(k+1)))^2*
            ((12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
              Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))))))*
              (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) := by ring
        _ ≤ (2*(9*(80*2*(64*(3:ℝ)^k))^2)*
            ((12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
              Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
                (3:ℝ)^(-26:ℝ)))*
              (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_right hscale' hterminal
        _ = _ := by ring
    _ = 2*(80*2*(64*(3:ℝ)^k))^2*
        (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
        Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
        (3:ℝ)^(2*((60+12*k+5:ℕ):ℝ)) := by
      rw [hexponent]
      have hcancel : (9:ℝ)*(3:ℝ)^24*(3:ℝ)^(-26:ℝ)=1 := by
        have hp : (9:ℝ)*(3:ℝ)^24=(3:ℝ)^26 := by norm_num
        rw [hp, Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
        field_simp
        norm_num
      calc
        _ = (2*(80*2*(64*(3:ℝ)^k))^2*
            (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
            Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
            (3:ℝ)^(2*((60+12*k+5:ℕ):ℝ)))*
            ((9:ℝ)*(3:ℝ)^24*(3:ℝ)^(-26:ℝ)) := by ring
        _ = _ := by rw [hcancel]; ring

private theorem density_localization_step4 (k : ℕ) :
    bandLocalizationCoefficient 4 (k+1) ≤
      9*bandLocalizationCoefficient 4 k := by
  let A : ℝ := (3:ℝ)^(11+k)/384
  have hA : 26 ≤ A := by
    dsimp [A]
    have hpow : (3:ℝ)^11 ≤ (3:ℝ)^(11+k) := by
      rw [pow_add]
      calc
        (3:ℝ)^11 = (3:ℝ)^11*1 := by ring
        _ ≤ (3:ℝ)^11*(3:ℝ)^k := by
          exact mul_le_mul_of_nonneg_left
            (one_le_pow₀ (by norm_num : (1:ℝ)≤3)) (by positivity)
    have hbase : (26:ℝ) ≤ (3:ℝ)^11/384 := by norm_num
    exact hbase.trans (div_le_div_of_nonneg_right hpow (by norm_num))
  have hpowA : (3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1))) = 3*A := by
    dsimp [A]
    rw [show 11+2*(k+1)=(12+k)+(k+1) by omega, pow_add,
      show 12+k=(11+k)+1 by omega, pow_succ, pow_succ]
    field_simp
    norm_num
  have hpowAk : (3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)) = A := by
    dsimp [A]
    rw [show 11+2*k=(11+k)+k by omega, pow_add]
    field_simp
    norm_num
  have hexp : Real.exp (-2*A) ≤ (3:ℝ)^(-26:ℝ) := by
    have hneg : -2*A ≤ -52 := by linarith
    have hmono : Real.exp (-2*A) ≤ Real.exp (-52) := Real.exp_le_exp.mpr hneg
    have htwo : (2:ℝ)^52 ≤ Real.exp (52:ℝ) := by
      rw [show (52:ℝ)=(52:ℕ)*1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le 52
    have hinv := one_div_le_one_div_of_le (by positivity) htwo
    have h23 : (3:ℝ)^26 ≤ (2:ℝ)^52 := by norm_num
    have hinv' := one_div_le_one_div_of_le (by positivity) h23
    have hsmall : Real.exp (-52) ≤ ((3:ℝ)^26)⁻¹ := by
      calc
        _ = (Real.exp (52:ℝ))⁻¹ := by rw [Real.exp_neg]
        _ ≤ 1/(2:ℝ)^52 := by simpa only [one_div] using hinv
        _ ≤ ((3:ℝ)^26)⁻¹ := by simpa only [one_div] using hinv'
    have hresult : Real.exp (-2*A) ≤ ((3:ℝ)^26)⁻¹ := hmono.trans hsmall
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
    have hcast : (3:ℝ)^(26:ℝ)=(3:ℝ)^26 := by exact Real.rpow_natCast _ _
    rw [hcast]
    exact hresult
  have hrpow :
      (12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1)))) ≤
        (12000:ℝ)^(1/(2*(64*(3:ℝ)^k))) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤12000)
    apply one_div_le_one_div_of_le (by positivity)
    have hk : (3:ℝ)^k ≤ (3:ℝ)^(k+1) := by
      rw [pow_succ]
      nlinarith [show 0 ≤ (3:ℝ)^k by positivity]
    nlinarith
  have hexponent :
      (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) =
        (3:ℝ)^24*(3:ℝ)^(2*((60+12*k+5:ℕ):ℝ)) := by
    have hcast :
        2*((60+12*(k+1)+5:ℕ):ℝ) =
          24+2*((60+12*k+5:ℕ):ℝ) := by push_cast; ring
    rw [hcast, Real.rpow_add (by norm_num : (0:ℝ)<3)]
    have h24 : (3:ℝ)^(24:ℝ)=(3:ℝ)^24 := Real.rpow_natCast _ _
    rw [h24]
  have hargA : -(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1))) = -(3*A) := by
    calc
      _ = -((3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) := by ring
      _ = -(3*A) := by rw [hpowA]
  have hargAk : -(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)) = -A := by
    calc
      _ = -((3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k))) := by ring
      _ = -A := by rw [hpowAk]
  have hstep :
      Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) ≤
        Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*(3:ℝ)^(-26:ℝ) := by
    rw [hargA,hargAk,show -(3*A)=(-A)+(-2*A) by ring,Real.exp_add]
    calc
      _ = Real.exp (-A)*Real.exp (-2*A) := by ring
      _ ≤ Real.exp (-A)*(3:ℝ)^(-26:ℝ) :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)
  unfold bandLocalizationCoefficient bandOrderMajorant bandDensityEntrance
  have hcoeff : (80*4*(64*(3:ℝ)^(k+1)))^4 ≤
      81*(80*4*(64*(3:ℝ)^k))^4 := by
    rw [pow_succ]
    ring_nf
    exact le_rfl
  have hlocal :
      (12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
        Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) ≤
      (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
        Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*(3:ℝ)^(-26:ℝ) := by
    calc
      _ ≤ (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
          Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) :=
        mul_le_mul_of_nonneg_right hrpow (Real.exp_nonneg _)
      _ ≤ _ := by
        calc
          _ ≤ (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
              (Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
                (3:ℝ)^(-26:ℝ)) :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
          _ = _ := by ring
  calc
    _ = 2*((80*4*(64*(3:ℝ)^(k+1)))^4*
        (12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
        Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1))))) *
        (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) := by ring_nf
    _ ≤ 2*(81*(80*4*(64*(3:ℝ)^k))^4)*
        ((12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
          Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*(3:ℝ)^(-26:ℝ))*
        (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) := by
      have hlocal0 : 0 ≤ (12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
          Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))) :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _)
      have hcoeff1 : 0 ≤ 81*(80*4*(64*(3:ℝ)^k))^4 := by positivity
      have hcomb := mul_le_mul hcoeff hlocal hlocal0 hcoeff1
      have hscale := mul_le_mul_of_nonneg_left hcomb (show (0:ℝ)≤2 by norm_num)
      have hscale' :
          2*((80*4*(64*(3:ℝ)^(k+1)))^4*
              ((12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
                Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))))) ≤
            (2*(81*(80*4*(64*(3:ℝ)^k))^4)) *
              ((12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
                Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
                  (3:ℝ)^(-26:ℝ)) := by
        calc
          _ ≤ 2*(81*(80*4*(64*(3:ℝ)^k))^4*
              ((12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
                Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
                  (3:ℝ)^(-26:ℝ))) := hscale
          _ = _ := by ring
      have hterminal : 0 ≤ (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) := by positivity
      calc
        _ = (2*((80*4*(64*(3:ℝ)^(k+1)))^4*
            ((12000:ℝ)^(1/(2*(64*(3:ℝ)^(k+1))))*
              Real.exp (-(3:ℝ)^(11+2*(k+1))/(6*(64*(3:ℝ)^(k+1)))))))*
              (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) := by ring
        _ ≤ (2*(81*(80*4*(64*(3:ℝ)^k))^4)*
            ((12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
              Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
                (3:ℝ)^(-26:ℝ)))*
              (3:ℝ)^(2*((60+12*(k+1)+5:ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_right hscale' hterminal
        _ = _ := by ring
    _ = 9*(2*(80*4*(64*(3:ℝ)^k))^4*
        (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
        Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
        (3:ℝ)^(2*((60+12*k+5:ℕ):ℝ))) := by
      rw [hexponent]
      have hcancel : (81:ℝ)*(3:ℝ)^24*(3:ℝ)^(-26:ℝ)=9 := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
        field_simp
        norm_num
      calc
        _ = (2*(80*4*(64*(3:ℝ)^k))^4*
            (12000:ℝ)^(1/(2*(64*(3:ℝ)^k)))*
            Real.exp (-(3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)))*
            (3:ℝ)^(2*((60+12*k+5:ℕ):ℝ)))*
            ((81:ℝ)*(3:ℝ)^24*(3:ℝ)^(-26:ℝ)) := by ring
        _ = _ := by rw [hcancel]; ring

theorem density_localization_coefficient_cap4 (k : ℕ) :
    bandLocalizationCoefficient 4 k ≤ (9:ℝ)^k := by
  induction k with
  | zero => simpa using density_localization_zero_cap
  | succ k ih =>
      calc
        _ ≤ 9*bandLocalizationCoefficient 4 k := density_localization_step4 k
        _ ≤ 9*(9:ℝ)^k := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (9:ℝ)^(k+1) := by rw [pow_succ]; ring

private theorem density_localization_le_one (k : ℕ) :
    bandLocalizationCoefficient 2 k ≤ 1 := by
  induction k with
  | zero =>
      have hcomp : bandLocalizationCoefficient 2 0 ≤
          bandLocalizationCoefficient 4 0 := by
        unfold bandLocalizationCoefficient bandOrderMajorant bandDensityEntrance
        norm_num
        gcongr
        norm_num
      exact hcomp.trans density_localization_zero_cap
  | succ k ih =>
      exact (density_localization_step k).trans ih

private theorem density_coefficient_cap (k : ℕ) (i : Fin 3) :
    bandDensityCoefficient 2 k i ≤ (200000000:ℝ)*(3:ℝ)^k := by
  have hP : bandOrderMajorant k = 64*(3:ℝ)^k := by rfl
  have hP0 : 0 ≤ (3:ℝ)^k := by positivity
  have hvar : uniformDensityVariance 2 = 8 := by
    norm_num [uniformDensityVariance]
  have hcoeff0 : 4*Real.sqrt
      (bandOrderMajorant k*63^2*uniformDensityVariance 2) ≤
      (200000000:ℝ)*(3:ℝ)^k := by
    rw [hP,hvar]
    have hinside : 0 ≤ (64*(3:ℝ)^k)*63^2*8 := by positivity
    have hsqrt : Real.sqrt ((64*(3:ℝ)^k)*63^2*8) ≤
        (64*(3:ℝ)^k)*63^2*8+1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [sq_nonneg ((64*(3:ℝ)^k)*63^2*8)]
    have hthree : 1 ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ)≤3)
    nlinarith [hsqrt]
  have hcoeff1 : 4*bandOrderMajorant k*63^2*12^2 ≤
      (200000000:ℝ)*(3:ℝ)^k := by
    rw [hP]
    calc
      _ = (4*64*63^2*12^2)*(3:ℝ)^k := by ring
      _ ≤ (200000000:ℝ)*(3:ℝ)^k := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hP0
  have hcoeff2 : bandLocalizationCoefficient 2 k ≤
      (200000000:ℝ)*(3:ℝ)^k := by
    have hh := density_localization_le_one k
    have h1 : 1 ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ)≤3)
    nlinarith
  unfold bandDensityCoefficient
  split_ifs with hi0 hi1
  · exact hcoeff0
  · exact hcoeff1
  · exact hcoeff2

private theorem density_offset_cap (i : Fin 3) :
    1+(3:ℝ)^(densityPERate 2 i)+(3:ℝ)^(2*densityPERate 2 i) ≤ 91 := by
  have hν0 : 0 ≤ densityPERate 2 i := by
    fin_cases i <;> norm_num [densityPERate]
  have hν2 : densityPERate 2 i ≤ 2 := by
    fin_cases i <;> norm_num [densityPERate]
  have h1 : (3:ℝ)^(densityPERate 2 i) ≤ 9 := by
    calc
      _ ≤ (3:ℝ)^2 := Real.rpow_le_rpow_of_exponent_le (by norm_num) hν2
      _ = 9 := by norm_num
  have h2 : (3:ℝ)^(2*densityPERate 2 i) ≤ 81 := by
    calc
      _ ≤ (3:ℝ)^4 := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (by nlinarith [hν2])
      _ = 81 := by norm_num
  linarith

private theorem assembly_density_reset_profile_bounds
    (γ : ℝ) (hγ : γ ≤ gammaZero) (k : ℕ) (i : Fin 3) :
    let C := 344+12*k
    let N := 160+5*k
    densityResetPowerSum (2*γ) (densityPERate 2 i) C ≤
      6*(3:ℝ)^(-(N:ℝ)) := by
  let C := 344+12*k
  let N := 160+5*k
  let β : ℝ := 49/100
  let c : ℝ := 59/100
  have hγ' : γ ≤ 17/50000 := by simpa [gammaZero] using hγ
  have hν0 : 0 ≤ densityPERate 2 i := by
    fin_cases i <;> norm_num [densityPERate]
  have hdecay := (density_rates_decay γ hγ 2 (Or.inl rfl) i).1
  have hβ0 : 0 ≤ β := by norm_num [β]
  have hc : 0 ≤ c := by norm_num [c]
  have hc1 : c < 1 := by norm_num [c]
  have hq : (3:ℝ)^(-β) ≤ c := by
    dsimp [β,c]
    exact full_response_three_neg_49_le
  have hN : (N:ℝ) ≤ β*((C+1:ℕ):ℝ) := by
    dsimp [N,β,C]
    push_cast
    nlinarith
  have hβ : β ≤ densityPERate 2 i-2*γ := by
    fin_cases i <;> norm_num [β,densityPERate] <;> nlinarith [hγ']
  have hreset := full_response_retained_reset_bounds
    (2*γ) (densityPERate 2 i) β c C N hdecay hβ hβ0 hN hc hc1 hq
  have hpow : (3:ℝ)^(-densityPERate 2 i) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by norm_num : (1:ℝ)≤3) (by linarith [hν0])
  have hconstant : (3:ℝ)^(-densityPERate 2 i)*(1/(1-c))^2 ≤ 6 := by
    calc
      _ ≤ 1*(1/(1-c))^2 := mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ 6 := by norm_num [c]
  calc
    _ ≤ (3:ℝ)^(-densityPERate 2 i)*(3:ℝ)^(-(N:ℝ))*(1/(1-c))^2 := hreset.1
    _ = ((3:ℝ)^(-densityPERate 2 i)*(1/(1-c))^2)*(3:ℝ)^(-(N:ℝ)) := by ring
    _ ≤ 6*(3:ℝ)^(-(N:ℝ)) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)

private theorem assembly_density_reset_power_nonneg
    (γ : ℝ) (hγ : γ ≤ gammaZero) (k : ℕ) (i : Fin 3) :
    0 ≤ densityResetPowerSum (2*γ) (densityPERate 2 i) (344+12*k) := by
  have hdecay := (density_rates_decay γ hγ 2 (Or.inl rfl) i).1
  have hh := density_reset_power_hasSum (2*γ) (densityPERate 2 i)
    hdecay (344+12*k)
  rw [← hh.tsum_eq]
  exact tsum_nonneg (fun _ => by positivity)

private theorem density_band_decay (k : ℕ) :
    (3:ℝ)^k*(3:ℝ)^(-(160+5*k:ℕ):ℝ) ≤ (3:ℝ)^(-160:ℝ) := by
  have hN : ((160+5*k:ℕ):ℝ)=160+5*(k:ℝ) := by norm_num
  have hrewrite : (3:ℝ)^k*(3:ℝ)^(-(160+5*k:ℕ):ℝ) =
      (3:ℝ)^(-160-4*(k:ℝ)) := by
    rw [hN, ← Real.rpow_natCast (3:ℝ) k,
      ← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  rw [hrewrite]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    (by nlinarith [show 0 ≤ (k:ℝ) by positivity])

/-- The actual all-height D2 density budget at the stopped `E+5` height is
below one hundredth of the additive trace allowance, uniformly over real
orders and the full permitted gamma range. -/
theorem assembly_trace_density_profile_cap
    (γ p : ℝ) (hγ : γ ≤ gammaZero) (_hp : 2 ≤ p) :
    let k := orderBand p
    let E := heightEntrance k
    assemblyDensityBudget γ k (E+5) ≤ 1/100 := by
  let k := orderBand p
  let E := heightEntrance k
  let C := 344+12*k
  let N := 160+5*k
  have hC : E+5-38=C := by
    dsimp [E,C,heightEntrance]
    omega
  have hresponse : rootResponseEnvelope (6*resetAllOrderTau) < 2*10^17 := by
    unfold rootResponseEnvelope
    have hτ0 : 0 ≤ resetAllOrderTau := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    have hτ : resetAllOrderTau ≤ 6*10^15 := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    have hx : 0 ≤ 6*resetAllOrderTau := by positivity
    have hsqrt : Real.sqrt ((6*resetAllOrderTau)*(6*resetAllOrderTau+2)) ≤
        6*resetAllOrderTau+1 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [hx]
    nlinarith [hτ,hsqrt]
  have hcharge : planarGradientCharge 40+1 < (4*10^41:ℝ) := by
    norm_num [planarGradientCharge]
  have hsens := assembly_sensitivity_lt
  have hresp0 : 0 ≤ rootResponseEnvelope (6*resetAllOrderTau) := by
    unfold rootResponseEnvelope
    have hτ0 : 0 ≤ resetAllOrderTau := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    exact add_nonneg (add_nonneg (by norm_num) (by positivity))
      (Real.sqrt_nonneg _)
  have hcharge0 : 0 ≤ planarGradientCharge 40+1 := by
    norm_num [planarGradientCharge]
  have hpref :
      rootAssemblySensitivity*rootResponseEnvelope (6*resetAllOrderTau)*
        (planarGradientCharge 40+1) ≤ (2*10^59:ℝ) := by
    calc
      _ ≤ ((127/100:ℝ)*(2*10^17))*(planarGradientCharge 40+1) := by
        have hfirst : rootAssemblySensitivity ≤ 127/100 := hsens.le
        have hsecond : rootResponseEnvelope (6*resetAllOrderTau) ≤ 2*10^17 := hresponse.le
        have h12 := mul_le_mul hfirst hsecond hresp0 (by norm_num)
        exact mul_le_mul_of_nonneg_right h12 hcharge0
      _ ≤ ((127/100:ℝ)*(2*10^17))*(4*10^41) :=
        mul_le_mul_of_nonneg_left hcharge.le (by norm_num)
      _ ≤ 2*10^59 := by norm_num
  have hcoeff (i : Fin 3) :
      bandDensityCoefficient 2 k i ≤ (200000000:ℝ)*(3:ℝ)^k :=
    density_coefficient_cap k i
  have hoffset (i : Fin 3) :
      1+(3:ℝ)^(densityPERate 2 i)+
        (3:ℝ)^(2*densityPERate 2 i) ≤ 91 := density_offset_cap i
  have hsum :
      ∑ i : Fin 3, bandDensityCoefficient 2 k i*
        (1+(3:ℝ)^(densityPERate 2 i)+
          (3:ℝ)^(2*densityPERate 2 i))*
        densityResetPowerSum (2*γ) (densityPERate 2 i) C ≤
        (327600000000:ℝ)*(3:ℝ)^(-160:ℝ) := by
    have hterm (i : Fin 3) :
        bandDensityCoefficient 2 k i*
          (1+(3:ℝ)^(densityPERate 2 i)+
            (3:ℝ)^(2*densityPERate 2 i))*
          densityResetPowerSum (2*γ) (densityPERate 2 i) C ≤
        (200000000:ℝ)*(3:ℝ)^k*91*6*(3:ℝ)^(-(N:ℝ)) := by
      have hreset := assembly_density_reset_profile_bounds γ hγ k i
      dsimp only [C,N] at hreset
      have hoff0 : 0 ≤ 1+(3:ℝ)^(densityPERate 2 i)+
          (3:ℝ)^(2*densityPERate 2 i) := by positivity
      calc
        _ ≤ (bandDensityCoefficient 2 k i*
            (1+(3:ℝ)^(densityPERate 2 i)+
              (3:ℝ)^(2*densityPERate 2 i)))*
            (6*(3:ℝ)^(-(N:ℝ))) :=
          mul_le_mul_of_nonneg_left hreset
            (mul_nonneg (band_density_coefficient_nonneg 2 k i) (by positivity))
        _ ≤ ((200000000:ℝ)*(3:ℝ)^k*91)*
            (6*(3:ℝ)^(-(N:ℝ))) := by
          have hbase : bandDensityCoefficient 2 k i*
                (1+(3:ℝ)^(densityPERate 2 i)+
                  (3:ℝ)^(2*densityPERate 2 i)) ≤
              (200000000:ℝ)*(3:ℝ)^k*91 := by
            calc
              _ ≤ ((200000000:ℝ)*(3:ℝ)^k)*
                  (1+(3:ℝ)^(densityPERate 2 i)+
                    (3:ℝ)^(2*densityPERate 2 i)) :=
                mul_le_mul_of_nonneg_right (hcoeff i) hoff0
              _ ≤ _ := mul_le_mul_of_nonneg_left (hoffset i)
                (by positivity)
          exact mul_le_mul_of_nonneg_right hbase (by positivity)
        _ = _ := by ring
    calc
      _ ≤ ∑ i : Fin 3,
          ((200000000:ℝ)*(3:ℝ)^k*91*6*(3:ℝ)^(-(N:ℝ))) :=
        Finset.sum_le_sum (fun i _ => hterm i)
      _ = 3*((200000000:ℝ)*(3:ℝ)^k*91*6*(3:ℝ)^(-(N:ℝ))) := by simp
      _ ≤ (327600000000:ℝ)*(3:ℝ)^(-160:ℝ) := by
        have hdecay := density_band_decay k
        dsimp [N] at hdecay ⊢
        have hscaled := mul_le_mul_of_nonneg_left hdecay (by norm_num : (0:ℝ)≤327600000000)
        nlinarith [hscaled]
  have hsum0 : 0 ≤ ∑ i : Fin 3, bandDensityCoefficient 2 k i*
      (1+(3:ℝ)^(densityPERate 2 i)+
        (3:ℝ)^(2*densityPERate 2 i))*
      densityResetPowerSum (2*γ) (densityPERate 2 i) C := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (mul_nonneg (band_density_coefficient_nonneg 2 k i) (by positivity))
      (assembly_density_reset_power_nonneg γ hγ k i)
  have hpower : (3:ℝ)^(-160:ℝ) ≤ (10:ℝ)^(-75:ℝ) := by
    have h := density_three160_ge_ten75
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3),
      Real.rpow_neg (by norm_num : (0:ℝ)≤10)]
    have hcast3 : (3:ℝ)^(160:ℝ)=(3:ℝ)^160 := by exact Real.rpow_natCast _ _
    have hcast10 : (10:ℝ)^(75:ℝ)=(10:ℝ)^75 := by exact Real.rpow_natCast _ _
    have hreal : (10:ℝ)^(75:ℝ) ≤ (3:ℝ)^(160:ℝ) := by
      rw [hcast10,hcast3]
      exact h
    have hh := one_div_le_one_div_of_le (by positivity) hreal
    simpa only [one_div] using hh
  change assemblyDensityBudget γ k (E+5) ≤ 1/100
  unfold assemblyDensityBudget
  rw [hC]
  calc
    _ ≤ (2*10^59:ℝ)*
        (∑ i : Fin 3, bandDensityCoefficient 2 k i*
          (1+(3:ℝ)^(densityPERate 2 i)+
            (3:ℝ)^(2*densityPERate 2 i))*
          densityResetPowerSum (2*γ) (densityPERate 2 i) C) :=
      mul_le_mul_of_nonneg_right hpref hsum0
    _ ≤ (2*10^59:ℝ)*((327600000000:ℝ)*(3:ℝ)^(-160:ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ (2*10^59:ℝ)*(327600000000:ℝ)*(10:ℝ)^(-75:ℝ) := by
      calc
        _ = ((2*10^59:ℝ)*(327600000000:ℝ))*(3:ℝ)^(-160:ℝ) := by ring
        _ ≤ ((2*10^59:ℝ)*(327600000000:ℝ))*(10:ℝ)^(-75:ℝ) :=
          mul_le_mul_of_nonneg_left hpower (by positivity)
        _ = _ := by ring
    _ ≤ 1/100 := by norm_num

end
end ASDExplicitGamma.Inverse
