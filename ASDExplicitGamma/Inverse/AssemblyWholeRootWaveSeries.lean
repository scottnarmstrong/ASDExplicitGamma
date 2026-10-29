module

public import ASDExplicitGamma.Inverse.AssemblyWholeRootWave
public import ASDExplicitGamma.Inverse.SelectedTail
public import ASDExplicitGamma.Inverse.OrderBandBounds

/-! Direct whole-root moments selected at the actual height. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The source logarithmic band leaves the selected-height tail's first
double-exponential argument above the uniform geometric-series threshold at
every real order. -/
theorem selected_wave_tail_argument_lower (p : ℝ) (hp : 2 ≤ p) :
    (10000:ℝ) ≤
      (heightExponent (heightEntrance (orderBand p)+11)/32)/(2*p) := by
  let k := orderBand p
  have hkScale : p ≤ 64*(3:ℝ)^k := order_band_scale p
  have hexp : (57+(k:ℝ)) ≤
      ((heightEntrance k+11:ℕ):ℝ)/4-40 := by
    unfold k heightEntrance
    push_cast
    linarith
  have hpow : (3:ℝ)^(57+(k:ℝ)) ≤
      heightExponent (heightEntrance k+11) := by
    unfold heightExponent
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have hfactor : (3:ℝ)^(57+(k:ℝ)) = (3:ℝ)^57*(3:ℝ)^k := by
    rw [Real.rpow_add (by norm_num : (0:ℝ)<3)]
    rw [Real.rpow_natCast]
    norm_num
  have hconst : (10000*64*64:ℝ) ≤ (3:ℝ)^57 := by norm_num
  have hnumerator : (10000:ℝ)*64*p ≤
      heightExponent (heightEntrance k+11) := by
    calc
      10000*64*p ≤ (10000*64)*(64*(3:ℝ)^k) :=
        mul_le_mul_of_nonneg_left hkScale (by norm_num)
      _ = (10000*64*64)*(3:ℝ)^k := by ring
      _ ≤ (3:ℝ)^57*(3:ℝ)^k :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = (3:ℝ)^(57+(k:ℝ)) := hfactor.symm
      _ ≤ heightExponent (heightEntrance k+11) := hpow
  have hden : 0 < 64*p := by positivity
  rw [show (heightExponent (heightEntrance k+11)/32)/(2*p) =
    heightExponent (heightEntrance k+11)/(64*p) by ring]
  apply (le_div_iff₀ hden).2
  simpa [mul_assoc,mul_left_comm,mul_comm] using hnumerator

/-- All-order sharp tail summation with the first source term retained. -/
theorem selected_wave_exact_tail_le_all_orders
    (γ p : ℝ) (H0 : ℕ) (hγ : γ ≤ gammaZero)
    (hH0 : 333 ≤ H0)
    (hx : (10000:ℝ) ≤ (heightExponent (H0+11)/32)/(2*p))
    (j : Fin 2) :
    selectedWaveExactTail γ p H0 j ≤
      (1000/999)*(selectedFirstClock H0)^j.val*
        (3:ℝ)^(4*γ*selectedFirstClock H0)*
          Real.exp (-((heightExponent (H0+11)/32)/(2*p))) := by
  let a := (3:ℝ)^(4*γ)
  let x := (heightExponent (H0+11)/32)/(2*p)
  let r := (3:ℝ)^(1/4:ℝ)
  let z := selectedFirstClock H0
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have ha3two : 2*a ≤ 3 := by
    dsimp only [a]
    exact selected_wave_clock_ratio γ hγ
  have ha3 : a ≤ 3 := by linarith only [ha3two]
  have hr : (13/10:ℝ) ≤ r := Numerics.Inverse.inv_quarter_growth.le
  have hz : 1 ≤ z := by
    have hh : (333:ℝ) ≤ H0 := by exact_mod_cast hH0
    dsimp only [z,selectedFirstClock]
    linarith only [hh]
  have haPos : 0 < a := by dsimp only [a]; positivity
  have hinner : Summable (fun n : ℕ => (z+(n:ℝ))^j.val*a^n*
        Real.exp (-x*r^n)) ∧
      (∑' n : ℕ, (z+(n:ℝ))^j.val*a^n*Real.exp (-x*r^n)) ≤
        z^j.val*(1000/999)*Real.exp (-x) := by
    fin_cases j
    · simpa only [Fin.val_zero,pow_zero,one_mul,z,a,r] using
        selected_clock_series a x r ha ha3 hx hr
    · simpa only [Fin.val_one,pow_one,z,a,r] using
        selected_linear_clock_series a x r z ha ha3two hx hr hz
  unfold selectedWaveExactTail
  simp_rw [selected_wave_tail_factor γ p H0]
  rw [tsum_mul_left]
  have hh := mul_le_mul_of_nonneg_left hinner.2
    (Real.rpow_nonneg (by norm_num : (0:ℝ)≤3) (4*γ*selectedFirstClock H0))
  simpa only [z,x,r,a,mul_assoc,mul_left_comm,mul_comm] using hh

end
end ASDExplicitGamma.Inverse
