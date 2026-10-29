module

public import ASDExplicitGamma.Inverse.AssemblyTraceNumerics
public import ASDExplicitGamma.Inverse.FullResponseDecayNumerics
public import ASDExplicitGamma.Inverse.AssemblyWholeRootWaveSelectedSum

/-! Numeric extraction for the baseline and direct selected-wave parts of the
positive trace budget. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Inverse
noncomputable section

private theorem assembly_three_pow_lower (k : ℕ) :
    1+2*(k:ℝ) ≤ (3:ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    push_cast
    nlinarith only [ih]

private theorem assembly_band_tail_argument_lower (p : ℝ) (hp : 2 ≤ p) :
    let k := orderBand p
    let A : ℝ := (3:ℝ)^57/4096
    A*((3:ℝ)^k)^2 ≤
      (heightExponent (heightEntrance k+11)/32)/(2*p) := by
  let k := orderBand p
  let A : ℝ := (3:ℝ)^57/4096
  have hk : p ≤ 64*(3:ℝ)^k := order_band_scale p
  have hz : (3:ℝ)^k = (3:ℝ)^(k:ℝ) := by norm_cast
  have hexp : heightExponent (heightEntrance k+11) =
      (3:ℝ)^(57+3*(k:ℝ)) := by
    unfold heightExponent heightEntrance
    push_cast
    congr 1
    ring
  have htriple : (3:ℝ)^(3*(k:ℝ)) = ((3:ℝ)^(k:ℝ))^3 := by
    rw [← Real.rpow_natCast ((3:ℝ)^(k:ℝ)) 3,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring
  have hsplit : (3:ℝ)^(57+3*(k:ℝ)) = (3:ℝ)^57*((3:ℝ)^k)^3 := by
    rw [Real.rpow_add (by norm_num : (0:ℝ)<3),htriple,hz]
    have h57 : (3:ℝ)^(57:ℝ) = (3:ℝ)^57 := Real.rpow_natCast _ _
    rw [h57]
  have hpos : 0 < 64*p := by positivity
  have hbound : A*((3:ℝ)^k)^2*(64*p) ≤
      heightExponent (heightEntrance k+11) := by
    calc
      _ ≤ A*((3:ℝ)^k)^2*(64*(64*(3:ℝ)^k)) := by gcongr
      _ = (3:ℝ)^57*((3:ℝ)^k)^3 := by dsimp only [A]; ring
      _ = heightExponent (heightEntrance k+11) := by
        rw [← hsplit,← hexp]
  have hden : (heightExponent (heightEntrance k+11)/32)/(2*p) =
      heightExponent (heightEntrance k+11)/(64*p) := by ring
  change A*((3:ℝ)^k)^2 ≤
    (heightExponent (heightEntrance k+11)/32)/(2*p)
  rw [hden]
  exact (le_div_iff₀ hpos).2 hbound

private theorem assembly_band_entrance_clock_bound (k : ℕ) :
    (selectedFirstClock (heightEntrance k):ℝ) ≤ 351*(3:ℝ)^k := by
  have hk := assembly_three_pow_lower k
  unfold selectedFirstClock heightEntrance
  push_cast
  nlinarith only [hk]

private theorem assembly_exp_neg_large :
    Real.exp (-10000:ℝ) ≤ 1/10^6 := by
  have hpow : (2:ℝ)^10000 ≤ Real.exp (10000:ℝ) := by
    rw [show (10000:ℝ)=(10000:ℕ)*1 by norm_num,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) Real.exp_one_gt_two.le _
  have hinv := one_div_le_one_div_of_le
    (by norm_num : (0:ℝ)<(2:ℝ)^10000) hpow
  have hlarge : (10^6:ℝ) ≤ (2:ℝ)^10000 := by
    calc
      (10:ℝ)^6 ≤ 2^20 := by norm_num
      _ ≤ 2^10000 := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega)
  calc
    Real.exp (-10000:ℝ) = (Real.exp (10000:ℝ))⁻¹ := Real.exp_neg _
    _ ≤ ((2:ℝ)^10000)⁻¹ := by simpa [one_div] using hinv
    _ ≤ (10^6:ℝ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hlarge
    _ = 1/10^6 := by ring

private theorem assembly_tail_exp_mass (p : ℝ) (hp : 2 ≤ p) :
    let k := orderBand p
    let x := (heightExponent (heightEntrance k+11)/32)/(2*p)
    (selectedFirstClock (heightEntrance k):ℝ)*Real.exp (-x) ≤ 351/10^6 := by
  let k := orderBand p
  let A : ℝ := (3:ℝ)^57/4096
  let x := (heightExponent (heightEntrance k+11)/32)/(2*p)
  have harg := assembly_band_tail_argument_lower p hp
  have hA : 10000 ≤ A := by norm_num [A]
  have hpowk : (1+2*(k:ℝ)) ≤ (3:ℝ)^k := assembly_three_pow_lower k
  have hpow2 : (3:ℝ)^k ≤ ((3:ℝ)^k)^2 := by
    have h1 : 1 ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ)≤3)
    calc
      (3:ℝ)^k = (3:ℝ)^k*1 := by ring
      _ ≤ (3:ℝ)^k*(3:ℝ)^k := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((3:ℝ)^k)^2 := by ring
  have hx : 10000+20000*(k:ℝ) ≤ x := by
    dsimp only [x]
    have harg' : A*((3:ℝ)^k)^2 ≤
        heightExponent (heightEntrance k+11)/32/(2*p) := by
      simpa only [k,A,x] using harg
    have hbase : 10000*(3:ℝ)^k ≤ A*((3:ℝ)^k)^2 := by
      exact mul_le_mul hA hpow2 (by positivity) (by positivity)
    calc
      _ ≤ 10000*(3:ℝ)^k := by nlinarith [hpowk]
      _ ≤ A*((3:ℝ)^k)^2 := hbase
      _ ≤ _ := harg'
  have hExp20000 : 3 ≤ Real.exp (20000:ℝ) := by
    have hpow : (2:ℝ)^20000 ≤ Real.exp (20000:ℝ) := by
      rw [show (20000:ℝ)=(20000:ℕ)*1 by norm_num,Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) Real.exp_one_gt_two.le _
    have hbig : (2:ℝ)^2 ≤ 2^20000 :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 2 ≤ 20000)
    calc
      3 ≤ (2:ℝ)^2 := by norm_num
      _ ≤ 2^20000 := hbig
      _ ≤ Real.exp (20000:ℝ) := hpow
  have hExpK : (3:ℝ)^k ≤ Real.exp (20000*(k:ℝ)) := by
    rw [show 20000*(k:ℝ)=(k:ℝ)*20000 by ring,Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hExp20000 k
  have hNegK : Real.exp (-(20000*(k:ℝ))) ≤ (3:ℝ)^(-(k:ℝ)) := by
    rw [Real.exp_neg,Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
    simpa [one_div] using one_div_le_one_div_of_le (by positivity) hExpK
  have hNeg : Real.exp (-x) ≤ Real.exp (-10000)*(3:ℝ)^(-(k:ℝ)) := by
    have hmono := Real.exp_le_exp.mpr (neg_le_neg hx)
    calc
      Real.exp (-x) ≤ Real.exp (-(10000+20000*(k:ℝ))) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp (-10000)*Real.exp (-(20000*(k:ℝ))) := by
        rw [show -(10000+20000*(k:ℝ))=(-10000)+(-(20000*(k:ℝ))) by ring,
          Real.exp_add]
      _ ≤ Real.exp (-10000)*(3:ℝ)^(-(k:ℝ)) :=
        mul_le_mul_of_nonneg_left hNegK (Real.exp_nonneg _)
  have hcancel : ((3:ℝ)^k)*(3:ℝ)^(-(k:ℝ))=1 := by
    rw [← Real.rpow_natCast (3:ℝ) k,← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    norm_num
  have hz := assembly_band_entrance_clock_bound k
  calc
    _ ≤ (351*(3:ℝ)^k)*(Real.exp (-10000)*(3:ℝ)^(-(k:ℝ))) :=
      mul_le_mul hz hNeg (by positivity) (by positivity)
    _ = 351*Real.exp (-10000) := by
      calc
        _ = 351*Real.exp (-10000)*((3:ℝ)^k*(3:ℝ)^(-(k:ℝ))) := by ring
        _ = 351*Real.exp (-10000) := by rw [hcancel,mul_one]
    _ ≤ 351/10^6 := by
      calc
        _ ≤ 351*(1/10^6) :=
          mul_le_mul_of_nonneg_left assembly_exp_neg_large (by norm_num)
        _ = 351/10^6 := by ring

theorem assembly_selected_tail_normed_cap
    (γ p : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ) (hp : 2 ≤ p)
    (j : Fin 2) :
    let k := orderBand p
    let E := heightEntrance k
    let Dbase := (3:ℝ)^(4*γ*((E:ℝ)+20))
    (3:ℝ)^(22*γ)*selectedWaveExactTail γ p E j ≤ Dbase/1000 := by
  let k := orderBand p
  let E := heightEntrance k
  let z := selectedFirstClock E
  let x := (heightExponent (E+11)/32)/(2*p)
  let Dbase := (3:ℝ)^(4*γ*((E:ℝ)+20))
  have hE : 333 ≤ E := by unfold E heightEntrance; omega
  have hx : (10000:ℝ) ≤ (heightExponent (E+11)/32)/(2*p) := by
    have harg := assembly_band_tail_argument_lower p hp
    have hlarge : (10000:ℝ) ≤ (3:ℝ)^57/4096*((3:ℝ)^(orderBand p))^2 := by
      have hA : (10000:ℝ) ≤ (3:ℝ)^57/4096 := by norm_num
      have hn : 1 ≤ (3:ℝ)^(orderBand p) := one_le_pow₀ (by norm_num : (1:ℝ)≤3)
      have hpow : (1:ℝ) ≤ ((3:ℝ)^(orderBand p))^2 := by
        have hstep : (3:ℝ)^(orderBand p) ≤ ((3:ℝ)^(orderBand p))^2 := by
          calc
            _ = (3:ℝ)^(orderBand p)*1 := by ring
            _ ≤ (3:ℝ)^(orderBand p)*(3:ℝ)^(orderBand p) :=
              mul_le_mul_of_nonneg_left hn (by positivity)
            _ = _ := by ring
        exact hn.trans hstep
      calc
        (10000:ℝ) ≤ (3:ℝ)^57/4096 := hA
        _ = ((3:ℝ)^57/4096)*1 := by ring
        _ ≤ ((3:ℝ)^57/4096)*((3:ℝ)^(orderBand p))^2 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    simpa [E,k] using le_trans hlarge harg
  have hmass := assembly_tail_exp_mass p hp
  have hz : 1 ≤ z := by
    dsimp only [z]
    have hreal : (333:ℝ) ≤ E := by exact_mod_cast hE
    unfold selectedFirstClock
    linarith
  have htail := selected_wave_exact_tail_le_all_orders γ p E hγ hE hx j
  have hexp : 22*γ+4*γ*z ≤ 4*γ*((E:ℝ)+20) := by
    have hzE : z=(E:ℝ)-26 := by dsimp only [z]; unfold selectedFirstClock; ring
    rw [hzE]
    nlinarith [hγ0]
  have hpow : (3:ℝ)^(22*γ)*(3:ℝ)^(4*γ*z) ≤ Dbase := by
    calc
      _ = (3:ℝ)^(22*γ+4*γ*z) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
      _ ≤ Dbase := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) hexp
  have hmass' : z^j.val*Real.exp (-x) ≤ 351/10^6 := by
    fin_cases j
    · simp only [pow_zero,one_mul]
      have h1 : Real.exp (-x) ≤ z*Real.exp (-x) := by
        calc
          Real.exp (-x) = 1*Real.exp (-x) := by ring
          _ ≤ z*Real.exp (-x) := mul_le_mul_of_nonneg_right hz (Real.exp_nonneg _)
      exact h1.trans hmass
    · simpa only [Fin.val_one,pow_one] using hmass
  have htail' : selectedWaveExactTail γ p E j ≤
      (1000/999)*z^j.val*(3:ℝ)^(4*γ*z)*Real.exp (-x) := by
    simpa only [z,x] using htail
  have hsmall : (1000/999:ℝ)*(351/10^6) ≤ 1/1000 := by norm_num
  have htailnonneg : 0 ≤ z^j.val*Real.exp (-x) := by positivity
  calc
    _ ≤ (3:ℝ)^(22*γ)*((1000/999:ℝ)*z^j.val*(3:ℝ)^(4*γ*z)*Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left htail' (by positivity)
    _ ≤ Dbase/1000 := by
      calc
        _ = ((1000/999:ℝ)*(z^j.val*Real.exp (-x)))*
            ((3:ℝ)^(22*γ)*(3:ℝ)^(4*γ*z)) := by ring
        _ ≤ ((1000/999:ℝ)*(351/10^6))*Dbase := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hmass' (by norm_num)) hpow
            (by positivity) (by positivity)
        _ ≤ Dbase/1000 := by
          calc
            _ ≤ (1/1000)*Dbase :=
              mul_le_mul_of_nonneg_right hsmall (by positivity)
            _ = Dbase/1000 := by ring

theorem assembly_selected_clock_normed_cap
    (γ p : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ) (hp : 2 ≤ p) :
    let k := orderBand p
    let E := heightEntrance k
    assemblySelectedClockBudget γ p E ≤
      (1001/1000:ℝ)*(3:ℝ)^(4*γ*((E:ℝ)+20)) := by
  let k := orderBand p
  let E := heightEntrance k
  let Dbase := (3:ℝ)^(4*γ*((E:ℝ)+20))
  have hE : 333 ≤ E := by unfold E heightEntrance; omega
  let x := (heightExponent (E+11)/32)/(2*p)
  let xtail := (heightExponent (E+11)/32)/(2*(p/2))
  have hx : 10000 ≤ x := by
    have harg := assembly_band_tail_argument_lower p hp
    have hlarge : (10000:ℝ) ≤ (3:ℝ)^57/4096*((3:ℝ)^(orderBand p))^2 := by
      have hA : (10000:ℝ) ≤ (3:ℝ)^57/4096 := by norm_num
      have hn : 1 ≤ (3:ℝ)^(orderBand p) := one_le_pow₀ (by norm_num : (1:ℝ)≤3)
      have hpow : (1:ℝ) ≤ ((3:ℝ)^(orderBand p))^2 := by
        have hstep : (3:ℝ)^(orderBand p) ≤ ((3:ℝ)^(orderBand p))^2 := by
          calc
            _ = (3:ℝ)^(orderBand p)*1 := by ring
            _ ≤ (3:ℝ)^(orderBand p)*(3:ℝ)^(orderBand p) :=
              mul_le_mul_of_nonneg_left hn (by positivity)
            _ = _ := by ring
        exact hn.trans hstep
      calc
        (10000:ℝ) ≤ (3:ℝ)^57/4096 := hA
        _ = ((3:ℝ)^57/4096)*1 := by ring
        _ ≤ ((3:ℝ)^57/4096)*((3:ℝ)^(orderBand p))^2 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
    simpa [E,k,x] using le_trans hlarge harg
  have hxtailEq : xtail = 2*x := by dsimp [xtail,x]; field_simp
  have hxtail : (10000:ℝ) ≤ xtail := by rw [hxtailEq]; linarith
  have hTail := selected_wave_exact_tail_le_all_orders (γ/2) (p/2) E
    (by nlinarith [hγ]) hE (by
      simpa only [xtail] using hxtail) (0:Fin 2)
  have hexpSmall : Real.exp (-xtail) ≤ 1/10^6 :=
    (Real.exp_le_exp.mpr (neg_le_neg hxtail)).trans assembly_exp_neg_large
  have htail : selectedWaveExactTail (γ/2) (p/2) E 0 ≤
      (1000/999:ℝ)*(3:ℝ)^(2*γ*((E:ℝ)-26))*Real.exp (-xtail) := by
    have hz : selectedFirstClock E = (E:ℝ)-26 := by
      unfold selectedFirstClock
      norm_num
    have h := hTail
    rw [hz] at h
    simpa [xtail,Fin.val_zero,show 4*(γ/2)=2*γ by ring] using h
  have hcoef : (1000/999:ℝ)*Real.exp (-xtail) ≤ 1/1000 := by
    calc
      _ ≤ (1000/999:ℝ)*(1/10^6) :=
        mul_le_mul_of_nonneg_left hexpSmall (by norm_num)
      _ ≤ 1/1000 := by norm_num
  have hEplus : 0 ≤ (E:ℝ)+62 := by positivity
  have hEplus' : 0 ≤ (E:ℝ)+61 := by positivity
  have hmainExp : 10*γ+2*γ*((E:ℝ)-27) ≤ 4*γ*((E:ℝ)+20) := by
    have hprod := mul_nonneg hγ0 hEplus
    nlinarith [hprod]
  have htailExp : 10*γ+2*γ*((E:ℝ)-26) ≤ 4*γ*((E:ℝ)+20) := by
    have hprod := mul_nonneg hγ0 hEplus'
    nlinarith [hprod]
  have hmain : (3:ℝ)^(10*γ)*(3:ℝ)^(2*γ*((E:ℝ)-27)) ≤ Dbase := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) hmainExp
  have htailPow : (3:ℝ)^(10*γ)*(3:ℝ)^(2*γ*((E:ℝ)-26)) ≤ Dbase := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) htailExp
  have hTailBound : (3:ℝ)^(10*γ)*selectedWaveExactTail (γ/2) (p/2) E 0 ≤
      Dbase/1000 := by
    calc
      _ ≤ (3:ℝ)^(10*γ)*((1000/999:ℝ)*
          (3:ℝ)^(2*γ*((E:ℝ)-26))*Real.exp (-xtail)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = ((1000/999:ℝ)*Real.exp (-xtail))*
          ((3:ℝ)^(10*γ)*(3:ℝ)^(2*γ*((E:ℝ)-26))) := by ring
      _ ≤ (1/1000)*Dbase :=
        mul_le_mul hcoef htailPow (by positivity) (by positivity)
      _ = Dbase/1000 := by ring
  unfold assemblySelectedClockBudget
  dsimp only [E,k]
  have hparts : (3:ℝ)^(10*γ)*((3:ℝ)^(2*γ*((E:ℝ)-27))+
      selectedWaveExactTail (γ/2) (p/2) E 0) ≤ Dbase+Dbase/1000 := by
    rw [mul_add]
    exact add_le_add hmain hTailBound
  calc
    _ = (3:ℝ)^(10*γ)*((3:ℝ)^(2*γ*((E:ℝ)-27))+
        selectedWaveExactTail (γ/2) (p/2) E 0) := by rfl
    _ ≤ Dbase+Dbase/1000 := hparts
    _ = (1001/1000:ℝ)*Dbase := by ring

end
end ASDExplicitGamma.Inverse
