module

public import ASDExplicitGamma.Inverse.AssemblyInverseMoments
public import ASDExplicitGamma.Inverse.AssemblyTraceNumerics
public import ASDExplicitGamma.Inverse.AssemblyMatrixBandProfile
public import ASDExplicitGamma.Inverse.AssemblyDensityProfile
public import ASDExplicitGamma.Inverse.AssemblyWholeRootWaveSeries
public import ASDExplicitGamma.Inverse.OrderResetInterface

/-! Numeric extraction for the actual positive inverse profile. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

private theorem assembly_inverse_exp_neg_large :
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

/-- The actual selected inverse clock has the source inverse-profile exponent;
the full rare tail is retained and pays less than one thousandth. -/
theorem assembly_selected_clock_inverse_profile_cap
    (γ p : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ) (hp : 2 ≤ p) :
    let E := heightEntrance (orderBand p)
    assemblySelectedClockBudget γ p E ≤
      (1001/1000:ℝ)*(3:ℝ)^(2*γ*((E:ℝ)+20)) := by
  let k := orderBand p
  let E := heightEntrance k
  let x := (heightExponent (E+11)/32)/(2*p)
  let xtail := (heightExponent (E+11)/32)/(2*(p/2))
  let T := (3:ℝ)^(2*γ*((E:ℝ)+20))
  have hE : 333 ≤ E := by unfold E heightEntrance; omega
  have hx : 10000 ≤ x := by
    simpa only [x,E,k] using selected_wave_tail_argument_lower p hp
  have hxtailEq : xtail=2*x := by dsimp [xtail,x]; field_simp
  have hxtail : (10000:ℝ) ≤ xtail := by rw [hxtailEq]; linarith
  have hTail := selected_wave_exact_tail_le_all_orders (γ/2) (p/2) E
    (by nlinarith [hγ]) hE (by simpa only [xtail] using hxtail) (0:Fin 2)
  have hexpSmall : Real.exp (-xtail) ≤ 1/10^6 :=
    (Real.exp_le_exp.mpr (neg_le_neg hxtail)).trans assembly_inverse_exp_neg_large
  have htail : selectedWaveExactTail (γ/2) (p/2) E 0 ≤
      (1000/999:ℝ)*(3:ℝ)^(2*γ*((E:ℝ)-26))*Real.exp (-xtail) := by
    have hz : selectedFirstClock E = (E:ℝ)-26 := by
      unfold selectedFirstClock
      norm_num
    have h := hTail
    rw [hz] at h
    simpa only [Fin.val_zero,pow_zero,one_mul,mul_one,xtail,
      show 4*(γ/2)=2*γ by ring] using h
  have hcoef : (1000/999:ℝ)*Real.exp (-xtail) ≤ 1/1000 := by
    calc
      _ ≤ (1000/999:ℝ)*(1/10^6) :=
        mul_le_mul_of_nonneg_left hexpSmall (by norm_num)
      _ ≤ 1/1000 := by norm_num
  have hmainExp : 10*γ+2*γ*((E:ℝ)-27) ≤ 2*γ*((E:ℝ)+20) := by
    have hprod := mul_nonneg hγ0 (show 0 ≤ (E:ℝ)+47 by positivity)
    nlinarith [hprod]
  have htailExp : 10*γ+2*γ*((E:ℝ)-26) ≤ 2*γ*((E:ℝ)+20) := by
    have hprod := mul_nonneg hγ0 (show 0 ≤ (E:ℝ)+46 by positivity)
    nlinarith [hprod]
  have hmain : (3:ℝ)^(10*γ)*(3:ℝ)^(2*γ*((E:ℝ)-27)) ≤ T := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) hmainExp
  have htailPow : (3:ℝ)^(10*γ)*(3:ℝ)^(2*γ*((E:ℝ)-26)) ≤ T := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) htailExp
  have hTailBound : (3:ℝ)^(10*γ)*selectedWaveExactTail (γ/2) (p/2) E 0 ≤ T/1000 := by
    calc
      _ ≤ (3:ℝ)^(10*γ)*((1000/999:ℝ)*
          (3:ℝ)^(2*γ*((E:ℝ)-26))*Real.exp (-xtail)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = ((1000/999:ℝ)*Real.exp (-xtail))*
          ((3:ℝ)^(10*γ)*(3:ℝ)^(2*γ*((E:ℝ)-26))) := by ring
      _ ≤ (1/1000)*T := mul_le_mul hcoef htailPow (by positivity) (by positivity)
      _ = T/1000 := by ring
  unfold assemblySelectedClockBudget
  dsimp only [E,k]
  have hparts : (3:ℝ)^(10*γ)*((3:ℝ)^(2*γ*((E:ℝ)-27))+
      selectedWaveExactTail (γ/2) (p/2) E 0) ≤ T+T/1000 := by
    rw [mul_add]
    exact add_le_add hmain hTailBound
  calc
    _ = (3:ℝ)^(10*γ)*((3:ℝ)^(2*γ*((E:ℝ)-27))+
        selectedWaveExactTail (γ/2) (p/2) E 0) := by rfl
    _ ≤ T+T/1000 := hparts
    _ = (1001/1000:ℝ)*T := by ring

private theorem assembly_inverse_density_moment_small :
    densityMomentBudget (allOrderDensity:ℝ) 2 1324 < 1/10^120 := by
  norm_num [densityMomentBudget,rareMomentPolynomial,allOrderDensity]

private theorem assembly_inverse_baseline_cap :
    assemblyInverseBaseline ≤ (1161/1000:ℝ) := by
  have hmoment := assembly_inverse_density_moment_small
  have hcharge : planarGradientCharge 40+1 < (4*10^41:ℝ) := by
    norm_num [planarGradientCharge]
  have hτ0 : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hτ : resetAllOrderTau ≤ 6*10^15 := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have ht : 0 ≤ 6*resetAllOrderTau := by positivity
  have hsqrt : Real.sqrt ((6*resetAllOrderTau)*(6*resetAllOrderTau+2)) ≤
      6*resetAllOrderTau+1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hresponse : rootResponseEnvelope (6*resetAllOrderTau) ≤ (2*10^17:ℝ) := by
    unfold rootResponseEnvelope
    nlinarith [hτ,hsqrt]
  have hresponse0 : 0 ≤ rootResponseEnvelope (6*resetAllOrderTau) := by
    unfold rootResponseEnvelope
    positivity
  have hcharge0 : 0 ≤ planarGradientCharge 40+1 := by
    unfold planarGradientCharge
    positivity
  have hmoment0 : 0 ≤ densityMomentBudget (allOrderDensity:ℝ) 2 1324 :=
    density_moment_budget_nonneg (allOrderDensity:ℝ) (by norm_num [allOrderDensity])
      2 1324 (by norm_num)
  have hsmall : 3*(planarGradientCharge 40+1)*
      rootResponseEnvelope (6*resetAllOrderTau)*
      densityMomentBudget (allOrderDensity:ℝ) 2 1324 ≤ 1/1000 := le_of_lt (by
    calc
      _ ≤ (3*(4*10^41:ℝ)*(2*10^17))*
          densityMomentBudget (allOrderDensity:ℝ) 2 1324 := by
        gcongr
      _ < 1/1000 := by nlinarith [hmoment])
  unfold assemblyInverseBaseline
  linarith

/-- The inverse deterministic Li coefficient is uniformly below 1.49. -/
theorem assembly_inverse_Li_cap (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ : γ ≤ gammaZero) :
    assemblyInverseLi γ ≤ (149/100:ℝ) := by
  have hsens := assembly_sensitivity_lt
  have hbase := assembly_inverse_baseline_cap
  have hlayer := assembly_root_layer_sum_cap γ hγ0 hγ
  have hlayer0 : 0 ≤ rootLayerSum (2*γ) := by
    unfold rootLayerSum
    apply tsum_nonneg
    intro i
    exact mul_nonneg (bankLayerWeight_nonneg i) (by positivity)
  have hbase0 : 0 ≤ assemblyInverseBaseline := assembly_inverse_baseline_nonneg
  unfold assemblyInverseLi
  calc
    _ ≤ ((127/100:ℝ)*(1161/1000))*rootLayerSum (2*γ) := by
      apply mul_le_mul_of_nonneg_right _ hlayer0
      exact mul_le_mul hsens.le hbase hbase0 (by norm_num)
    _ ≤ (127/100:ℝ)*(1161/1000)*(101/100) := by
      exact mul_le_mul_of_nonneg_left hlayer (by positivity)
    _ ≤ 149/100 := by norm_num

private theorem assembly_inverse_three336_ge_ten30 :
    (10:ℝ)^30 ≤ (3:ℝ)^336 := by
  have hbase : (10:ℝ) ≤ (3:ℝ)^3 := by norm_num
  calc
    _ ≤ ((3:ℝ)^3)^30 := pow_le_pow_left₀ (by norm_num) hbase 30
    _ = (3:ℝ)^(3*30) := by rw [← pow_mul]
    _ ≤ (3:ℝ)^336 :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ)≤3) (by norm_num)

private theorem assembly_inverse_matrix_budget_cap
    (γ p : ℝ) (hγ : γ ≤ gammaZero) (hp : 2 ≤ p) :
    let k := orderBand p
    let E := heightEntrance k
    assemblyMatrixBudget γ p (E+5) ≤ 1/100 := by
  let k := orderBand p
  let E := heightEntrance k
  let C := 344+12*k
  let N := 336+11*k
  have horder := order_band_scale p
  have hroot : Real.sqrt p ≤ 8*(3:ℝ)^k := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hone : 1 ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ)≤3)
      have hstep : (3:ℝ)^k ≤ ((3:ℝ)^k)^2 := by nlinarith
      have horder' : p ≤ 64*(3:ℝ)^k := by simpa using horder
      calc
        p ≤ 64*(3:ℝ)^k := horder'
        _ ≤ 64*((3:ℝ)^k)^2 := by nlinarith [hstep]
        _ = (8*(3:ℝ)^k)^2 := by ring
  have hC : E+5-38=C := by
    dsimp [E,C,heightEntrance]
    omega
  have hN : (N:ℝ)=336+11*(k:ℝ) := by
    dsimp [N]
    push_cast
    ring
  have hreset := assembly_trace_reset_profile_bounds γ hγ k
  have hfactor : (3:ℝ)^(-1:ℝ)*(1/(1-34/100:ℝ))^2 ≤ 1 := by norm_num
  have hraw : densityResetPowerSum (2*γ) 1 C ≤
      (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*(1/(1-34/100:ℝ))^2 := by
    simpa [C,N] using hreset.1
  have hreset' : densityResetPowerSum (2*γ) 1 (E+5-38) ≤
      (3:ℝ)^(-(N:ℝ)) := by
    rw [hC]
    calc
      _ ≤ (3:ℝ)^(-1:ℝ)*(3:ℝ)^(-(N:ℝ))*(1/(1-34/100:ℝ))^2 := hraw
      _ = (3:ℝ)^(-(N:ℝ))*
          ((3:ℝ)^(-1:ℝ)*(1/(1-34/100:ℝ))^2) := by ring
      _ ≤ _ := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hfactor (by positivity))
  have hτ : resetAllOrderTau ≤ 6*10^15 := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hτ0 : 0 ≤ resetAllOrderTau := by
    norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hsqrt : Real.sqrt (resetAllOrderTau*(resetAllOrderTau+2)) ≤ resetAllOrderTau+1 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (resetAllOrderTau+1)]
  have hresp : rootResponseEnvelope resetAllOrderTau ≤ (2*10^16:ℝ) := by
    unfold rootResponseEnvelope
    nlinarith [hsqrt,hτ]
  have hsens := assembly_sensitivity_lt
  have hresp0 : 0 ≤ rootResponseEnvelope resetAllOrderTau := by
    unfold rootResponseEnvelope
    have hτ0 : 0 ≤ resetAllOrderTau := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    positivity
  have hcoef : rootAssemblySensitivity*256*Real.sqrt p*
      rootResponseEnvelope resetAllOrderTau ≤
        (896*10^18:ℝ)*(3:ℝ)^k := by
    calc
      _ ≤ (127/100:ℝ)*256*(8*(3:ℝ)^k)*(2*10^16) := by
        gcongr
      _ = ((127/100:ℝ)*256*8*(2*10^16))*(3:ℝ)^k := by ring
      _ ≤ (896*10^18:ℝ)*(3:ℝ)^k :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hpow : (3:ℝ)^k*(3:ℝ)^(-(N:ℝ)) ≤ (3:ℝ)^(-336:ℝ) := by
    rw [← Real.rpow_natCast (3:ℝ) k,← Real.rpow_add (by norm_num : (0:ℝ)<3),hN]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
    nlinarith [show 0 ≤ (k:ℝ) by positivity]
  have hsmall : (896*10^18:ℝ)*(3:ℝ)^(-336:ℝ) ≤ 1/100 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
    have hrealpow : (10:ℝ)^30 ≤ (3:ℝ)^(336:ℝ) := by
      have hrpow : (3:ℝ)^(336:ℝ)=(3:ℝ)^336 := Real.rpow_natCast _ _
      calc
        _ ≤ (3:ℝ)^336 := assembly_inverse_three336_ge_ten30
        _ = (3:ℝ)^(336:ℝ) := hrpow.symm
    have hden : ((3:ℝ)^(336:ℝ))⁻¹ ≤ ((10:ℝ)^30)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity)
        hrealpow
    calc
      _ ≤ (896*10^18:ℝ)/(10:ℝ)^30 := by
        exact mul_le_mul_of_nonneg_left hden (by positivity)
      _ ≤ 1/100 := by norm_num
  change assemblyMatrixBudget γ p (E+5) ≤ 1/100
  unfold assemblyMatrixBudget
  have hcoef0 : 0 ≤ rootAssemblySensitivity*256*Real.sqrt p*
      rootResponseEnvelope resetAllOrderTau := by
    have hsens0 := root_assembly_sensitivity_pos.le
    have hτ0 : 0 ≤ resetAllOrderTau := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    unfold rootResponseEnvelope
    positivity
  calc
    _ ≤ (rootAssemblySensitivity*256*Real.sqrt p*
        rootResponseEnvelope resetAllOrderTau)*(3:ℝ)^(-(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hreset' hcoef0
    _ ≤ ((896*10^18:ℝ)*(3:ℝ)^k)*(3:ℝ)^(-(N:ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (896*10^18:ℝ)*((3:ℝ)^k*(3:ℝ)^(-(N:ℝ))) := by ring
    _ ≤ (896*10^18:ℝ)*(3:ℝ)^(-336:ℝ) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ 1/100 := hsmall

/-- All positive inverse errors retain their actual matrix and density series;
both are uniformly below one hundredth at the source entrance. -/
theorem assembly_inverse_error_profile_cap
    (γ p : ℝ) (hγ : γ ≤ gammaZero) (hp : 2 ≤ p) :
    let k := orderBand p
    let E := heightEntrance k
    assemblyMatrixBudget γ p (E+5)+assemblyDensityBudget γ k (E+5) ≤ 1/50 := by
  let k := orderBand p
  let E := heightEntrance k
  have hm := assembly_inverse_matrix_budget_cap γ p hγ hp
  have hd := assembly_trace_density_profile_cap γ p hγ hp
  have hsum := add_le_add hm hd
  norm_num at hsum ⊢
  simpa [k,E] using hsum

/-- The complete inverse Lp budget fits even the smaller 1.53 coefficient
throughout the full permitted gamma range. -/
theorem assembly_inverse_profile_budget_cap
    (γ p : ℝ) (hγ : γ ≤ gammaZero) (hγ0 : 0 ≤ γ) (hp : 2 ≤ p) :
    let k := orderBand p
    let E := heightEntrance k
    assemblyInverseLi γ*assemblySelectedClockBudget γ p E+
      assemblyMatrixBudget γ p (E+5)+assemblyDensityBudget γ k (E+5) ≤
        (153/100:ℝ)*(3:ℝ)^(2*γ*((E:ℝ)+20)) := by
  let k := orderBand p
  let E := heightEntrance k
  let T := (3:ℝ)^(2*γ*((E:ℝ)+20))
  have hLi := assembly_inverse_Li_cap γ hγ0 hγ
  have hclock := assembly_selected_clock_inverse_profile_cap γ p hγ hγ0 hp
  have herr := assembly_inverse_error_profile_cap γ p hγ hp
  have hT : 1 ≤ T := by
    dsimp [T]
    apply Real.one_le_rpow (by norm_num : (1:ℝ)≤3)
    positivity
  have hfirst : assemblyInverseLi γ*assemblySelectedClockBudget γ p E ≤
      (149/100:ℝ)*(1001/1000)*T := by
    have hE : 333 ≤ E := by unfold E heightEntrance; omega
    have hLi0 : 0 ≤ assemblyInverseLi γ := by
      unfold assemblyInverseLi
      have hsum0 : 0 ≤ rootLayerSum (2*γ) := by
        unfold rootLayerSum
        apply tsum_nonneg
        intro i
        exact mul_nonneg (bankLayerWeight_nonneg i) (by positivity)
      exact mul_nonneg (mul_nonneg root_assembly_sensitivity_pos.le
        assembly_inverse_baseline_nonneg) hsum0
    have hclock0 : 0 ≤ assemblySelectedClockBudget γ p E := by
      unfold assemblySelectedClockBudget
      have htail0 : 0 ≤ selectedWaveExactTail (γ/2) (p/2) E 0 := by
        unfold selectedWaveExactTail
        apply tsum_nonneg
        intro n
        simp only [Fin.val_zero,pow_zero,one_mul]
        have hz : 0 ≤ selectedFirstClock E+(n:ℝ) := by
          unfold selectedFirstClock
          have hEreal : (333:ℝ)≤(E:ℝ) := by exact_mod_cast hE
          have hn : (0:ℝ)≤(n:ℝ) := Nat.cast_nonneg n
          linarith
        unfold selectedTailProbability
        positivity
      exact mul_nonneg (by positivity) (add_nonneg (by positivity) htail0)
    calc
      _ ≤ (149/100:ℝ)*((1001/1000:ℝ)*T) :=
        mul_le_mul hLi hclock hclock0 (by norm_num)
      _ = _ := by ring
  have herrors : assemblyMatrixBudget γ p (E+5)+
      assemblyDensityBudget γ k (E+5) ≤ (1/50:ℝ)*T := by
    calc
      _ ≤ 1/50 := herr
      _ ≤ (1/50:ℝ)*T := by nlinarith [hT]
  calc
    _ = (assemblyInverseLi γ*assemblySelectedClockBudget γ p E)+
        (assemblyMatrixBudget γ p (E+5)+assemblyDensityBudget γ k (E+5)) := by ring
    _ ≤ ((149/100:ℝ)*(1001/1000))*T+(1/50:ℝ)*T := add_le_add hfirst herrors
    _ = ((149/100:ℝ)*(1001/1000)+1/50)*T := by ring
    _ ≤ (153/100:ℝ)*T := by nlinarith [hT]

/-- The actual inverse estimate holds in every reference frame with the
smaller source coefficient, leaving the stable reset statement untouched. -/
theorem assembly_reference_inverse_profile_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale-342-12*orderBand p → nativeInductionState M h n)
    (N ref : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (protectedOldLabel Q.scale (orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    eLpNorm (rootInverseObservable M Q (protectedOldLabel Q.scale (orderBand p))
      N ref weights) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((153/100:ℝ)*(3:ℝ)^(2*M.gamma*
        ((heightEntrance (orderBand p):ℝ)+20)+
          2*M.gamma*|((ref-Q.scale+1:ℤ):ℝ)|)) := by
  let k := orderBand p
  let E := heightEntrance k
  let f := |((ref-Q.scale+1:ℤ):ℝ)|
  let B := assemblyInverseLi M.gamma*
      assemblySelectedClockBudget M.gamma p E+
        assemblyMatrixBudget M.gamma p (E+5)+assemblyDensityBudget M.gamma k (E+5)
  have hLi0 : 0 ≤ assemblyInverseLi M.gamma := by
    unfold assemblyInverseLi
    have hsum0 : 0 ≤ rootLayerSum (2*M.gamma) := by
      unfold rootLayerSum
      apply tsum_nonneg
      intro i
      exact mul_nonneg (bankLayerWeight_nonneg i) (by positivity)
    exact mul_nonneg (mul_nonneg root_assembly_sensitivity_pos.le
      assembly_inverse_baseline_nonneg)
      hsum0
  have hγ0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hE : 333 ≤ E := by unfold E heightEntrance; omega
  have hclock0 : 0 ≤ assemblySelectedClockBudget M.gamma p E := by
    unfold assemblySelectedClockBudget
    have htail0 : 0 ≤ selectedWaveExactTail (M.gamma/2) (p/2) E 0 := by
      unfold selectedWaveExactTail
      apply tsum_nonneg
      intro n
      have hz : 0 ≤ selectedFirstClock E+(n:ℝ) := by
        unfold selectedFirstClock
        have hEreal : (333:ℝ) ≤ (E:ℝ) := by exact_mod_cast hE
        have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      simp only [Fin.val_zero,pow_zero,one_mul]
      unfold selectedTailProbability
      positivity
    positivity
  have hmatrix0 : 0 ≤ assemblyMatrixBudget M.gamma p (E+5) := by
    rw [← (assembly_matrix_budget_hasSum M.gamma p hγ (E+5)).tsum_eq]
    apply tsum_nonneg
    intro hk
    have hp0 : 0 ≤ p := by linarith
    have hsens0 := root_assembly_sensitivity_pos.le
    have htau0 : 0 ≤ resetAllOrderTau := by
      norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
    have hgamma0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    unfold assemblyMatrixBudgetTerm rootResponseEnvelope
    positivity
  have hdensity0 : 0 ≤ assemblyDensityBudget M.gamma k (E+5) := by
    rw [← (assembly_density_budget_hasSum M.gamma hγ k (E+5)).tsum_eq]
    exact tsum_nonneg (assembly_density_budget_term_nonneg M.gamma k (E+5))
  have herr0 : 0 ≤ assemblyMatrixBudget M.gamma p (E+5)+
      assemblyDensityBudget M.gamma k (E+5) := add_nonneg hmatrix0 hdensity0
  have hprofile := assembly_inverse_profile_budget_cap M.gamma p hγ
    hγ0 hp
  have hsource := assembly_reference_inverse_Lp M h hM hγ Q p hp hpast
    N ref hN weights hw
  have hframe : 0 ≤ (3:ℝ)^(2*M.gamma*|((ref-Q.scale+1:ℤ):ℝ)|) := by positivity
  have hreal : B ≤ (153/100:ℝ)*(3:ℝ)^(2*M.gamma*((E:ℝ)+20)) := by
    simpa [B,k,E] using hprofile
  have hprod : (3:ℝ)^(2*M.gamma*|((ref-Q.scale+1:ℤ):ℝ)|)*B ≤
      (153/100:ℝ)*((3:ℝ)^(2*M.gamma*((E:ℝ)+20))*
        (3:ℝ)^(2*M.gamma*|((ref-Q.scale+1:ℤ):ℝ)|)) := by
    calc
      _ ≤ (3:ℝ)^(2*M.gamma*|((ref-Q.scale+1:ℤ):ℝ)|)*
          ((153/100:ℝ)*(3:ℝ)^(2*M.gamma*((E:ℝ)+20))) :=
        mul_le_mul_of_nonneg_left hreal hframe
      _ = _ := by ring
  have hsourceEq : ENNReal.ofReal ((3:ℝ)^(2*M.gamma*f))*
      (ENNReal.ofReal (assemblyInverseLi M.gamma)*
        ENNReal.ofReal (assemblySelectedClockBudget M.gamma p E)+
          ENNReal.ofReal (assemblyMatrixBudget M.gamma p (E+5)+
            assemblyDensityBudget M.gamma k (E+5))) =
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*f)*B) := by
    rw [(ENNReal.ofReal_mul hLi0).symm]
    rw [← ENNReal.ofReal_add (mul_nonneg hLi0 hclock0) herr0]
    rw [← ENNReal.ofReal_mul hframe]
    congr 1
    dsimp [B,f]
    ring
  have hsource' := hsource.trans (le_of_eq hsourceEq)
  calc
    _ ≤ ENNReal.ofReal ((3:ℝ)^(2*M.gamma*f)*B) := hsource'
    _ ≤ ENNReal.ofReal ((153/100:ℝ)*
        ((3:ℝ)^(2*M.gamma*((E:ℝ)+20))*
          (3:ℝ)^(2*M.gamma*f))) := by
      exact ENNReal.ofReal_le_ofReal hprod
    _ = ENNReal.ofReal ((153/100:ℝ)*(3:ℝ)^(2*M.gamma*
        ((E:ℝ)+20)+2*M.gamma*f)) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]

end
end ASDExplicitGamma.Inverse
