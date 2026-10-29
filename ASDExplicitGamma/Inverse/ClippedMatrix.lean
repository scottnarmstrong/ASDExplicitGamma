module

public import ASDExplicitGamma.Inverse.AllOrderPlanarInterpolation
public import ASDExplicitGamma.Inverse.ClippedMatrixActualConcentration
public import ASDExplicitGamma.Inverse.RootMatrixLayerWeights
public import ASDExplicitGamma.Inverse.RootMatrixDeviation
public import ASDExplicitGamma.Inverse.StoppedUniformFullDensity
public import ASDExplicitGamma.Inverse.StoppedRootAverage
public import ASDExplicitGamma.Inverse.StoppedRootBlockWeights
public import ASDExplicitGamma.Inverse.ResetChronology

/-! All-order clipped matrix fluctuations and actual root-layer density
concentration, at the source's order-dependent Whitney depths. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

private theorem density_cutoff_from_rational_power (q : ℝ) (hq : 0 < q) (n : ℕ)
    (hn : 200/(26*q) < (2718/1000:ℝ)^n) :
    200*Real.exp (-(n:ℝ)) ≤ 26*q := by
  have hpow : (2718/1000:ℝ)^n ≤ Real.exp (n:ℝ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2718/1000)
      Numerics.Inverse.invEuler_real.le n
    simpa only [← Real.exp_nat_mul, Nat.cast_mul, mul_one] using hh
  have hh := (div_le_iff₀ (by positivity : 0 < 26*q)).mp (hn.le.trans hpow)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  simpa only [mul_comm] using hh

/-- The actual rational density has the complete exponential moment cutoff
at the source value 1324. -/
theorem all_order_density_moment_cutoff :
    200*Real.exp (-(1324:ℝ)/4) ≤ 26*(allOrderDensity:ℝ) := by
  have hq : 0 < (allOrderDensity:ℝ) := by
    norm_num [allOrderDensity]
  have hbase : (20000:ℝ) ≤ (2718/1000:ℝ)^10 := by norm_num
  have hpow : (20000:ℝ)^33 ≤ (2718/1000:ℝ)^331 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20000) hbase 33
    calc
      (20000:ℝ)^33 ≤ ((2718/1000:ℝ)^10)^33 := hh
      _ = (2718/1000:ℝ)^330 := by rw [← pow_mul]
      _ ≤ (2718/1000:ℝ)^331 := by gcongr <;> norm_num
  have hc : 200/(26*(allOrderDensity:ℝ)) < (20000:ℝ)^33 := by
    norm_num [allOrderDensity]
  have hc' : 200/(26*(allOrderDensity:ℝ)) < (2718/1000:ℝ)^331 := hc.trans_le hpow
  have hh := density_cutoff_from_rational_power _ hq 331 hc'
  simpa only [show -(1324:ℝ)/4=-(331:ℝ) by norm_num, Nat.cast_ofNat] using hh

/-- All-order spatial density concentration on the actual finite physical
root blocks. The clipped mark label and the spatial resolution are independent
source indices, so the caller may keep the history at the protected layer
label while refining the volume partition. -/
theorem q3_root_spatial_density_uniform_Lp
    (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h) (hg : A.gamma ≤ gammaZero)
    (j : ℤ) (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) (hfloor : Real.exp (-6000) ≤ q)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ j+40, nativeInductionState A h k)
    (T : ℝ) (hT : 0 ≤ T) (hcut : 200*Real.exp (-T/4) ≤ 26*q)
    (Q : TriadicCube 2) (R : ℕ) (m : ℕ) (hm : m=2 ∨ m=4)
    (p : ℝ) (hp : 2 ≤ p) (E : Set (Vec 2)) (hE : MeasurableSet E)
    (hEQ : E ⊆ cubeSet Q) :
    let μ := (Cutoff.cutoffSampleLaw A).toMeasure
    let B := q3PlanarMarks A j τ (waveGateEta t)
    let X := rootDiameterAverage B Q R E m
    let v := (volume E).toReal/(volume (cubeSet Q)).toReal
    eLpNorm (fun ω => X ω-∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityBudget m p (R/6+1) ((1/9:ℝ)^R) v) ∧
    eLpNorm (fun ω => max (X ω-v*densityMomentBudget q m T) 0)
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityBudget m p (R/6+1) ((1/9:ℝ)^R) v) := by
  let μ := (Cutoff.cutoffSampleLaw A).toMeasure
  let B := q3PlanarMarks A j τ (waveGateEta t)
  let X := rootDiameterAverage B Q R E m
  let v := (volume E).toReal/(volume (cubeSet Q)).toReal
  let w := fun z : ↥(rootBlockPopulation Q R) =>
    localizationPartialWeight Q E (physicalBlockSet (rootFineLabel Q R) z.val)
  have hB : PlanarMarkControl μ B q := q3_mark_control A h hA hg j τ hτ t q hraw hpast
  have hmpos : 1 ≤ m := by omega
  have hm1 : m-1+1=m := by omega
  have hMoment (z : ↥(rootBlockPopulation Q R)) :
      Integrable (fun ω => (realDiameterField B z.val ω)^m) μ ∧
        (∫ ω, (realDiameterField B z.val ω)^m ∂μ) ≤ densityMomentBudget q m T := by
    have hh := real_diameter_nat_moment μ B q hB hq0 hq hfloor z.val (m-1) T hT hcut
    simpa only [hm1, densityMomentBudget] using hh
  have hfrac := root_layer_fraction_bounds Q E hEQ
  have hweights : (∑ z : ↥(rootBlockPopulation Q R), w z)=v := by
    dsimp only [w, v]
    exact root_partial_weights_sum Q E hE hEQ R
  have hfull := q3_full_uniform_density_Lp A h hA hg j τ hτ t q hq0 hq hfloor hraw
    hpast T hT hcut (R/6+1) m hm p hp
    (fun z : ↥(rootBlockPopulation Q R) => z.val) Subtype.val_injective
    ((1/9:ℝ)^R) v (by positivity) hfrac.1 w
    (fun z => localization_partial_weight_nonneg Q E
      (physicalBlockSet (rootFineLabel Q R) z.val))
    (fun z => root_partial_weight_le Q E R z.val) hweights
  have he := root_diameter_average_centered_eq μ B Q R E hE hEQ m
    (fun z => (hMoment z).1)
  have ha := root_diameter_average_eq B Q R E hE hEQ m
  constructor
  · change eLpNorm (fun ω => X ω-∫ ζ, X ζ ∂μ) _ μ ≤ _
    rw [he]
    simpa only [X, w] using hfull.1
  · change eLpNorm (fun ω => max (X ω-v*densityMomentBudget q m T) 0) _ μ ≤ _
    change eLpNorm (fun ω => max (rootDiameterAverage B Q R E m ω-
      v*densityMomentBudget q m T) 0) _ μ ≤ _
    rw [ha]
    simpa only [X, w, v] using hfull.2

/-- The actual diameter average on a fixed root Whitney layer. The mark
label is the protected old layer label; `e` changes only the physical volume
resolution, as in the three source localization terms. -/
def resetRootLayerDensityAverage (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (e : Fin 3) (m : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let d := layerDepth H i
  let R := d - 40 - e.val
  let j := Q.scale - (d : ℤ)
  rootDiameterAverage
    (q3PlanarMarks M j resetAllOrderTau (waveGateEta .allOrder)) Q R
    (localizationWhitneyLayer Q H (i-1)) m ω

/-- The positive density excess for one of three retained resolutions. -/
def rootLayerDensityExcess (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (e : Fin 3) (m : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  max (resetRootLayerDensityAverage M Q H i e m ω -
    bankLayerWeight (i-1) *
      densityMomentBudget (allOrderDensity : ℝ) m 1324) 0

/-- The actual root-layer density bounds at all real orders `p ≥ 2` and all
three physical resolutions. The protected old mark label stays fixed while
the localization partition is refined. No `p ≤ 256` restriction is needed. -/
theorem root_layer_density_all_order_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (k : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * k → nativeInductionState M h n)
    (H i : ℕ) (hH : heightEntrance k ≤ H) (hi : 1 ≤ i)
    (e : Fin 3) (m : ℕ) (hm : m=2 ∨ m=4) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let X := resetRootLayerDensityAverage M Q H i e m
    eLpNorm (fun ω => X ω - ∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityBudget m p
        ((layerDepth H i - 40 - e.val)/6+1)
        ((1/9:ℝ)^(layerDepth H i - 40 - e.val))
        (bankLayerWeight (i-1))) ∧
    eLpNorm (rootLayerDensityExcess M Q H i e m)
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityBudget m p
        ((layerDepth H i - 40 - e.val)/6+1)
        ((1/9:ℝ)^(layerDepth H i - 40 - e.val))
        (bankLayerWeight (i-1))) := by
  let d := layerDepth H i
  let R := d - 40 - e.val
  let j : ℤ := Q.scale - (d : ℤ)
  let E := localizationWhitneyLayer Q H (i-1)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := resetRootLayerDensityAverage M Q H i e m
  have hprofile : 2 ≤ layerProfile i := by
    unfold layerProfile
    have hi' : 1 ≤ i := hi
    omega
  have hH' : 377 + 12 * k ≤ H := by
    simpa [heightEntrance] using hH
  have hd : heightEntrance k + 5 ≤ d := by
    dsimp [d]
    unfold heightEntrance layerDepth at *
    omega
  have hR : R = layerDepth H i - 40 - e.val := rfl
  have hE : MeasurableSet E := by
    dsimp [E]
    exact localization_whitney_layer_measurable Q H (i-1)
  have hEQ : E ⊆ cubeSet Q := by
    dsimp [E]
    exact localization_whitney_layer_subset Q H (i-1)
  have hpast' : ∀ n : ℤ, n ≤ j+40 → nativeInductionState M h n := by
    intro n hn
    have hd' : (382:ℤ) + 12 * (k:ℤ) ≤ (d:ℤ) := by
      have hdd : 382 + 12*k ≤ d := by
        unfold heightEntrance layerDepth at *
        omega
      exact_mod_cast hdd
    have hlabel : j+40 ≤ Q.scale-342-12*k := by
      dsimp [j]
      omega
    exact hpast n (hn.trans hlabel)
  have hτ : 0 < resetAllOrderTau := by
    norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau]
  have hq0 : 0 ≤ (allOrderDensity : ℝ) := by
    norm_num [allOrderDensity]
  have hq : (allOrderDensity : ℝ) ≤ 1/10000000000 :=
    all_order_density_small
  have hfloor : Real.exp (-6000) ≤ (allOrderDensity : ℝ) :=
    le_of_lt all_order_density_floor
  have hT : 0 ≤ (1324:ℝ) := by norm_num
  have hcut : 200*Real.exp (-(1324:ℝ)/4) ≤ 26*(allOrderDensity:ℝ) :=
    all_order_density_moment_cutoff
  have hfull := q3_root_spatial_density_uniform_Lp M h hM hγ j
    resetAllOrderTau hτ .allOrder (allOrderDensity:ℝ) hq0 hq hfloor
    all_order_density_covers_raw hpast' 1324 hT hcut Q R
    m hm p hp E hE hEQ
  have hv : (volume E).toReal/(volume (cubeSet Q)).toReal =
      bankLayerWeight (i-1) := by
    dsimp [E]
    exact localization_whitney_layer_volume Q H (i-1)
  change
    eLpNorm (fun ω => X ω - ∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityBudget m p (R/6+1) ((1/9:ℝ)^R)
        (bankLayerWeight (i-1))) ∧
    eLpNorm (rootLayerDensityExcess M Q H i e m)
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityBudget m p (R/6+1) ((1/9:ℝ)^R)
        (bankLayerWeight (i-1)))
  have hfull' := hfull
  dsimp only at hfull'
  rw [hv] at hfull'
  constructor
  · simpa only [resetRootLayerDensityAverage, X, μ, R, d, j, E] using hfull'.1
  · change eLpNorm (fun ω => max (X ω -
        bankLayerWeight (i-1)*densityMomentBudget (allOrderDensity:ℝ) m 1324) 0)
        (ENNReal.ofReal p) μ ≤ _
    simpa only [resetRootLayerDensityAverage, X, μ, R, d, j, E] using hfull'.2

/-- The all-order density budget written as its retained variance and linear
powers plus the exact finite-box localization remainder. -/
def uniformDensityPowerEnvelope (m : ℕ) (p : ℝ) (R : ℕ) : ℝ :=
  4*Real.sqrt (p*63^2*uniformDensityVariance m)*(3:ℝ)^(-(5/6:ℝ)*(R:ℝ))+
  4*p*63^2*12^m*(3:ℝ)^(-((10-(m:ℝ))/6)*(R:ℝ))+
  2*localizationErrorBudget m p (R/6+1)

/-- The source order majorant `P_k=64*3^k`. -/
def bandOrderMajorant (k : ℕ) : ℝ := 64*(3:ℝ)^k

/-- The first density resolution in band `k`. -/
def bandDensityEntrance (k : ℕ) : ℕ := 60+12*k

/-- Exact source coefficient of the all-order QSEP localization tail in band
`k`, including the five-residue allowance. -/
def bandLocalizationCoefficient (m k : ℕ) : ℝ :=
  2*(80*(m:ℝ)*bandOrderMajorant k)^m*
    (12000:ℝ)^(1/(2*bandOrderMajorant k))*
    Real.exp (-((3:ℝ)^(11+2*k))/(6*bandOrderMajorant k))*
    (3:ℝ)^(2*((bandDensityEntrance k+5:ℕ):ℝ))

/-- The exact three-term density envelope at its source band endpoint. -/
def bandDensityPowerEnvelope (m k R : ℕ) : ℝ :=
  4*Real.sqrt (bandOrderMajorant k*63^2*uniformDensityVariance m)*
      (3:ℝ)^(-(5/6:ℝ)*(R:ℝ))+
    4*bandOrderMajorant k*63^2*12^m*
      (3:ℝ)^(-((10-(m:ℝ))/6)*(R:ℝ))+
    bandLocalizationCoefficient m k*(3:ℝ)^(-2*(R:ℝ))

private theorem three_pow_lower (n : ℕ) :
    1+2*(n:ℝ) ≤ (3:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      push_cast
      nlinarith only [ih]

/-- The exact QSEP mismatch term is paid by the source localization power on
every band and every later integer resolution. -/
theorem localization_error_band_power (m k R : ℕ)
    (hR : bandDensityEntrance k ≤ R) :
    2*localizationErrorBudget m (bandOrderMajorant k) (R/6+1) ≤
      bandLocalizationCoefficient m k*(1/9:ℝ)^R := by
  let P := bandOrderMajorant k
  let R0 := bandDensityEntrance k
  let t := (R-R0)/6
  let s := (R-R0)%6
  let N0 := (3:ℝ)^(11+2*k)
  let A := N0/(6*P)
  have hdecomp0 := Nat.div_add_mod (R-R0) 6
  have hdecomp : R = R0+6*t+s := by
    dsimp [t,s] at *
    omega
  have hs : s < 6 := by
    dsimp [s]
    exact Nat.mod_lt _ (by norm_num)
  have hM : R/6+1=11+2*k+t := by
    dsimp [R0,bandDensityEntrance,t] at *
    omega
  have hN : (3:ℝ)^(R/6+1)=N0*(3:ℝ)^t := by
    rw [hM,show 11+2*k+t=(11+2*k)+t by omega,pow_add]
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlog3le : Real.log 3 ≤ 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3)
    norm_num at hh ⊢
    linarith
  have h3k : 1 ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3)
  have hN0lower : (3:ℝ)^11 ≤ (3:ℝ)^(11+k) := by
    rw [pow_add]
    calc
      (3:ℝ)^11 = (3:ℝ)^11*1 := by simp
      _ ≤ (3:ℝ)^11*(3:ℝ)^k := mul_le_mul_of_nonneg_left h3k
        (by norm_num : (0:ℝ) ≤ (3:ℝ)^11)
  have hAeq : (3:ℝ)^(11+2*k)/(6*(64*(3:ℝ)^k)) =
      (3:ℝ)^(11+k)/384 := by
    rw [show 11+2*k=(11+k)+k by omega,pow_add]
    field_simp
    norm_num
  have hAlog : 12*Real.log 3 ≤ 2*A := by
    have hlog : 12*Real.log 3 ≤ 24 := by nlinarith only [hlog3le]
    have hnum : (24:ℝ) ≤ 2*(3:ℝ)^11/384 := by norm_num
    have hnum' : 2*(3:ℝ)^11/384 ≤ 2*(3:ℝ)^(11+k)/384 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hN0lower (by norm_num)) (by norm_num)
    have hAform : A=(3:ℝ)^(11+k)/384 := by
      dsimp [A,N0,P,bandOrderMajorant]
      exact hAeq
    rw [hAform]
    linarith
  have hP : 0 < P := by dsimp [P,bandOrderMajorant]; positivity
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by positivity) (by positivity)
  have ht0 : 0 ≤ (t:ℝ) := by positivity
  have hlinpow : 2*(t:ℝ) ≤ (3:ℝ)^t-1 := by
    have hh := three_pow_lower t
    linarith
  have hmass : 12*(t:ℝ)*Real.log 3 ≤ N0*((3:ℝ)^t-1)/(6*P) := by
    have hcoeffmul := mul_le_mul_of_nonneg_right hAlog ht0
    have hpowmul := mul_le_mul_of_nonneg_left hlinpow hA0
    calc
      12*(t:ℝ)*Real.log 3 ≤ (2*A)*(t:ℝ) := by nlinarith only [hcoeffmul]
      _ ≤ A*((3:ℝ)^t-1) := by nlinarith only [hpowmul]
      _ = N0*((3:ℝ)^t-1)/(6*P) := by dsimp [A]; ring
  have hs5 : (s:ℝ) ≤ 5 := by
    have hh : s ≤ 5 := by omega
    exact_mod_cast hh
  have hdecompR : (R:ℝ)=(R0:ℝ)+6*(t:ℝ)+(s:ℝ) := by exact_mod_cast hdecomp
  have hRgap : (R:ℝ)-(R0:ℝ)-5 ≤ 6*(t:ℝ) := by nlinarith only [hdecompR,hs5]
  have hgap := mul_le_mul_of_nonneg_right hRgap hlog3
  have hdelta : 2*((R:ℝ)-(R0:ℝ)-5)*Real.log 3 ≤
      N0*((3:ℝ)^t-1)/(6*P) := by
    calc
      _ ≤ 12*(t:ℝ)*Real.log 3 := by nlinarith only [hgap]
      _ ≤ _ := hmass
  have harg : -((3:ℝ)^(R/6+1))/(6*P) ≤
      -N0/(6*P)+2*(((R0+5:ℕ):ℝ)-(R:ℝ))*Real.log 3 := by
    rw [hN]
    have hcast : ((R0+5:ℕ):ℝ)=(R0:ℝ)+5 := by norm_num
    rw [hcast]
    have hmass' : 2*((R:ℝ)-(R0:ℝ)-5)*Real.log 3 ≤
        N0*(3:ℝ)^t/(6*P)-N0/(6*P) := by
      calc
        _ ≤ N0*((3:ℝ)^t-1)/(6*P) := hdelta
        _ = _ := by ring
    calc
      -(N0*(3:ℝ)^t)/(6*P) ≤
          -N0/(6*P)-2*((R:ℝ)-(R0:ℝ)-5)*Real.log 3 := by
        linear_combination hmass'
      _ = -N0/(6*P)+2*((R0:ℝ)+5-(R:ℝ))*Real.log 3 := by congr 1 <;> ring
  have hpowExp : (3:ℝ)^(2*(((R0+5:ℕ):ℝ)-(R:ℝ))) =
      Real.exp (2*(((R0+5:ℕ):ℝ)-(R:ℝ))*Real.log 3) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ)<3)]
    ring_nf
  have hexp : Real.exp (-((3:ℝ)^(R/6+1))/(6*P)) ≤
      Real.exp (-N0/(6*P))*(3:ℝ)^(2*(((R0+5:ℕ):ℝ)-(R:ℝ))) := by
    rw [hpowExp,← Real.exp_add]
    exact Real.exp_le_exp.mpr harg
  let F := 2*(80*(m:ℝ)*P)^m*(12000:ℝ)^(1/(2*P))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hscaled := mul_le_mul_of_nonneg_left hexp hF
  have hsplit : (3:ℝ)^(2*(((R0+5:ℕ):ℝ)-(R:ℝ))) =
      (3:ℝ)^(2*((R0+5:ℕ):ℝ))*(1/9:ℝ)^R := by
    rw [density_root_weight_power]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1 <;> ring
  unfold localizationErrorBudget bandLocalizationCoefficient
  change 2*((80*(m:ℝ)*P)^m*(12000:ℝ)^(1/(2*P))*
      Real.exp (-((3:ℝ)^(R/6+1))/(6*P))) ≤
    2*(80*(m:ℝ)*P)^m*(12000:ℝ)^(1/(2*P))*
      Real.exp (-N0/(6*P))*(3:ℝ)^(2*((R0+5:ℕ):ℝ))*(1/9:ℝ)^R
  calc
    _ = F*Real.exp (-((3:ℝ)^(R/6+1))/(6*P)) := by dsimp [F]; ring
    _ ≤ F*(Real.exp (-N0/(6*P))*
        (3:ℝ)^(2*(((R0+5:ℕ):ℝ)-(R:ℝ)))) := hscaled
    _ = _ := by dsimp [F]; rw [hsplit]; ring

theorem uniform_density_budget_source_powers (m : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (R : ℕ) (v : ℝ) (hv1 : v ≤ 1) :
    uniformDensityBudget m p (R/6+1) ((1/9:ℝ)^R) v ≤
      uniformDensityPowerEnvelope m p R := by
  have hβ0 : 0 ≤ uniformDensityVariance m := by
    unfold uniformDensityVariance
    split <;> norm_num
  have hroot : Real.sqrt v ≤ 1 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by simpa only [one_pow] using hv1⟩
  let c := 4*Real.sqrt (p*63^2*uniformDensityVariance m)
  let a := (3:ℝ)^(-(5/6:ℝ)*(R:ℝ))
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hvar := density_variance_power_bound p (uniformDensityVariance m)
    v hp hβ0 R
  have hvar' :
      4*Real.sqrt (p*21^2*uniformDensityVariance m*(3:ℝ)^(2*(R/6+1))*
        (1/9:ℝ)^R*v) ≤ c*a := by
    calc
      _ ≤ c*Real.sqrt v*a := by simpa only [c,a] using hvar
      _ ≤ c*a := by
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hroot hc0) ha0
        simpa only [mul_one, mul_assoc] using hh
  have hlin := density_linear_power_bound p hp m R
  have herr0 := localization_error_budget_nonneg m p hp (R/6+1)
  have herrcoef : 0 ≤ 2*localizationErrorBudget m p (R/6+1) :=
    mul_nonneg (by norm_num) herr0
  have herr : 2*localizationErrorBudget m p (R/6+1)*v ≤
      2*localizationErrorBudget m p (R/6+1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 herrcoef
  unfold uniformDensityBudget uniformDensityPowerEnvelope
  dsimp only [c,a] at hvar'
  calc
    _ ≤ 4*Real.sqrt (p*63^2*uniformDensityVariance m)*(3:ℝ)^(-(5/6:ℝ)*(R:ℝ))+
        4*p*63^2*12^m*(3:ℝ)^(-((10-(m:ℝ))/6)*(R:ℝ))+
        2*localizationErrorBudget m p (R/6+1) := by
      exact add_le_add (add_le_add hvar' hlin) herr
    _ = _ := by ring

/-- The actual layer excess obeys the explicit retained source decay at
every real order; only the localization tail is left in its exact QSEP form. -/
theorem root_layer_density_retained_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (k : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * k → nativeInductionState M h n)
    (H i : ℕ) (hH : heightEntrance k ≤ H) (hi : 1 ≤ i)
    (e : Fin 3) (m : ℕ) (hm : m=2 ∨ m=4) :
    let R := layerDepth H i - 40 - e.val
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let X := resetRootLayerDensityAverage M Q H i e m
    eLpNorm (fun ω => X ω - ∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityPowerEnvelope m p R) ∧
    eLpNorm (rootLayerDensityExcess M Q H i e m)
      (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (uniformDensityPowerEnvelope m p R) := by
  let R := layerDepth H i - 40 - e.val
  let E := localizationWhitneyLayer Q H (i-1)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := resetRootLayerDensityAverage M Q H i e m
  have hEQ : E ⊆ cubeSet Q := by
    dsimp [E]
    exact localization_whitney_layer_subset Q H (i-1)
  have hv := root_layer_fraction_bounds Q E hEQ
  have hvExact : (volume E).toReal/(volume (cubeSet Q)).toReal =
      bankLayerWeight (i-1) := by
    dsimp [E]
    exact localization_whitney_layer_volume Q H (i-1)
  have hv1 : bankLayerWeight (i-1) ≤ 1 := by rw [← hvExact]; exact hv.2
  have hdensity := root_layer_density_all_order_Lp M h hM hγ Q k p hp
    hpast H i hH hi e m hm
  have hp0 : 0 ≤ p := by linarith
  have hbudget := uniform_density_budget_source_powers m p hp0 R
    (bankLayerWeight (i-1)) hv1
  have hresult :
      eLpNorm (fun ω => X ω - ∫ ζ, X ζ ∂μ) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (uniformDensityPowerEnvelope m p R) ∧
      eLpNorm (rootLayerDensityExcess M Q H i e m)
        (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (uniformDensityPowerEnvelope m p R) := by
    constructor
    · exact hdensity.1.trans (ENNReal.ofReal_le_ofReal hbudget)
    · exact hdensity.2.trans (ENNReal.ofReal_le_ofReal hbudget)
  simpa only [R, μ, X] using hresult

/-- The actual centered clipped full-matrix fluctuation on a root layer. -/
def resetRootCenteredLayerMatrix (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (τ : ℝ) (ω : Cutoff.CutoffSample 2) : FullBlockMat 2 :=
  ∑ U ∈ whitneyRootLayer Q H i,
    ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) •
      (clippedCellMatrix M (layerOldCutoff Q.scale H i) U τ ω-
        ∫ ζ, clippedCellMatrix M (layerOldCutoff Q.scale H i) U τ ζ
          ∂(Cutoff.cutoffSampleLaw M).toMeasure)

/-- Positive pure-flux error of the actual clipped matrix layer. -/
def resetRootMatrixPositiveError (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (τ : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  clippedPositiveFluxDeviation (resetRootCenteredLayerMatrix M Q H i τ ω)

/-- The all-real-order clipped matrix estimate at each actual layer.
The exact source layer fraction and the physical depth are retained. -/
theorem root_centered_layer_matrix_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (Q : TriadicCube 2) (H i : ℕ)
    (hi : 1 ≤ i) (τ : ℝ) (hτ : 0 ≤ τ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
      (resetRootCenteredLayerMatrix M Q H i τ ω)‖) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (128*(1+τ+Real.sqrt (τ*(τ+2)))*Real.sqrt p*
        Real.sqrt (bankLayerWeight (i-1))*(1/3:ℝ)^(layerDepth H i)*(3:ℝ)^40) := by
  let j : ℤ := Q.scale-(layerDepth H i:ℤ)
  let I := ↥(whitneyRootLayer Q H i)
  let w : I → ℝ := fun U => (volume (cubeSet U.val)).toReal/(volume (cubeSet Q)).toReal
  have hscale (U : I) : U.val.scale=j := by
    have hs := root_whitney_layer_scale Q H i U.property
    dsimp [j, layerDepth, layerProfile, whitneyProfile] at *
    omega
  have hlabel : layerOldCutoff Q.scale H i=j+40 := by
    unfold layerOldCutoff
    dsimp [j]
  have hh := clipped_actual_cells_matrix_Lp M h hM j τ hτ
    (fun U : I => U.val) hscale Subtype.val_injective w p hp
  have he (ω : Cutoff.CutoffSample 2) :
      (∑ U : I, w U • (clippedCellMatrix M (j+40) U.val τ ω-
        ∫ ζ, clippedCellMatrix M (j+40) U.val τ ζ ∂(Cutoff.cutoffSampleLaw M).toMeasure)) =
        resetRootCenteredLayerMatrix M Q H i τ ω := by
    have hsum := Finset.sum_coe_sort (whitneyRootLayer Q H i)
      (fun U : TriadicCube 2 =>
        ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) •
          (clippedCellMatrix M (layerOldCutoff Q.scale H i) U τ ω-
            ∫ ζ, clippedCellMatrix M (layerOldCutoff Q.scale H i) U τ ζ
              ∂(Cutoff.cutoffSampleLaw M).toMeasure))
    simpa only [resetRootCenteredLayerMatrix, w, hlabel] using hsum
  have hefun :
      (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (∑ U : I, w U • (clippedCellMatrix M (j+40) U.val τ ω-
          ∫ ζ, clippedCellMatrix M (j+40) U.val τ ζ ∂(Cutoff.cutoffSampleLaw M).toMeasure))‖) =
      fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (resetRootCenteredLayerMatrix M Q H i τ ω)‖ := by
    funext ω
    exact congrArg (fun A : FullBlockMat 2 =>
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖) (he ω)
  dsimp only at hh
  rw [hefun] at hh
  have hweight :
      (∑ U : I, (w U)^2) =
        bankLayerWeight (i-1)*(1/9:ℝ)^(layerDepth H i) := by
    have hn : i-1+1=i := Nat.sub_add_cancel hi
    have hsum := root_matrix_layer_squared_weights Q H (i-1)
    have hsum' :
        (∑ U ∈ whitneyRootLayer Q H i,
          ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)^2) =
        bankLayerWeight (i-1)*(1/9:ℝ)^(i+whitneyProfile H i) := by
      simpa only [hn] using hsum
    have hcoe := Finset.sum_coe_sort (whitneyRootLayer Q H i)
      (fun U : TriadicCube 2 =>
        ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)^2)
    have hcoe' :
        (∑ U : I, (w U)^2) =
          ∑ U ∈ whitneyRootLayer Q H i,
            ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)^2 := by
      simpa only [I, w] using hcoe
    have hbase := hcoe'.trans hsum'
    have hd : i+whitneyProfile H i = layerDepth H i := by
      rw [layer_depth_eq_compatible_mesh]
      rfl
    rw [hd] at hbase
    exact hbase
  have hweight0 : 0 ≤ bankLayerWeight (i-1) := bankLayerWeight_nonneg _
  have hroot : Real.sqrt ((1/9:ℝ)^(layerDepth H i)) =
      (1/3:ℝ)^(layerDepth H i) := by
    have hpw : (1/9:ℝ)^(layerDepth H i) =
        ((1/3:ℝ)^(layerDepth H i))^2 := by
      rw [← pow_mul, Nat.mul_comm (layerDepth H i) 2, pow_mul]
      norm_num
    rw [hpw, Real.sqrt_sq (by positivity)]
  apply hh.trans_eq
  congr 1
  rw [hweight, Real.sqrt_mul hweight0, hroot]
  ring

theorem reset_root_matrix_positive_error_measurable (M : ABKModel 2)
    (Q : TriadicCube 2) (H i : ℕ) (τ : ℝ) :
    Measurable (resetRootMatrixPositiveError M Q H i τ) :=
  clipped_positive_flux_deviation_continuous.measurable.comp <| by
    apply Measurable.of_eval_matrix
    intro a b
    simp only [resetRootCenteredLayerMatrix, Matrix.sum_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul]
    apply Finset.measurable_sum
    intro U _
    exact (((measurable_pi_apply b).comp ((measurable_pi_apply a).comp
      (clipped_cell_matrix_measurable M (layerOldCutoff Q.scale H i) U τ))).sub_const _).const_mul _

/-- The positive directional error is controlled by the all-order actual
clipped-matrix estimate, with the source's factor 256 retained. -/
theorem reset_root_matrix_positive_error_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (Q : TriadicCube 2) (H i : ℕ)
    (hi : 1 ≤ i) (τ : ℝ) (hτ : 0 ≤ τ) (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (resetRootMatrixPositiveError M Q H i τ) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (256*Real.sqrt p*(1+τ+Real.sqrt (τ*(τ+2))) *
        Real.sqrt (bankLayerWeight (i-1))*(1/3:ℝ)^(layerDepth H i)*(3:ℝ)^40) := by
  have hh := root_centered_layer_matrix_Lp M h hM Q H i hi τ hτ p hp
  have hm := reset_root_matrix_positive_error_measurable M Q H i τ
  have hn : eLpNorm (resetRootMatrixPositiveError M Q H i τ) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      eLpNorm (fun ω => ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
        (resetRootCenteredLayerMatrix M Q H i τ ω)‖) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply eLpNorm_mono_real hm.aestronglyMeasurable
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ resetRootMatrixPositiveError M Q H i τ ω from le_max_left 0 _)]
    exact clipped_positive_flux_deviation_le _
  apply (hn.trans hh).trans
  apply ENNReal.ofReal_le_ofReal
  have hτ' : 0 ≤ 1+τ+Real.sqrt (τ*(τ+2)) := by
    have hrad : 0 ≤ τ*(τ+2) := mul_nonneg hτ (by linarith)
    positivity
  have hbase : 0 ≤ Real.sqrt p*Real.sqrt (bankLayerWeight (i-1))*
      (1/3:ℝ)^(layerDepth H i)*(3:ℝ)^40 := by positivity
  nlinarith only [hτ', hbase]

end
end ASDExplicitGamma.Inverse
