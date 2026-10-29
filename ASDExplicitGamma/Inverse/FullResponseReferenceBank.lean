module

public import ASDExplicitGamma.Inverse.FullResponseAffineProfile
public import ASDExplicitGamma.Inverse.FullResponseProfile

/-! Complete certified full-response norm profiles in the root reference frame. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Every literal order-64 endpoint component is nonnegative. -/
theorem full_response_endpoint_row64_nonneg (γ D : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hD : 0 ≤ D) :
    (∀ a, 0 ≤ fullResponseLeadingRow64 γ D a) ∧ (∀ b, 0 ≤ fullResponseErrorRow64 γ D b) := by
  constructor
  · intro a
    exact (full_response_leading_budget_nonneg γ 64 D hγ hg (by norm_num) hD a).trans
      (full_response_leading_row64_le γ D hγ hg hD a)
  · intro b
    exact (full_response_error_budget_nonneg γ 64 D hγ hg (by norm_num) hD b).trans
      (full_response_error_row64_le γ D hγ hg hD b)

/-- The literal source baseline of the order-64 profile is nonnegative. -/
theorem full_response_Bt64_nonneg : (0:ℝ) ≤ (invFull64Bt:ℝ) := by
  have hs := full_response_endpoint_row64_nonneg 0 0 (by norm_num) (by norm_num [gammaZero]) (by norm_num)
  have hh := add_nonneg (Finset.sum_nonneg (s := Finset.univ) (fun a _ => hs.1 a)) (Finset.sum_nonneg (s := Finset.univ) (fun b _ => hs.2 b))
  rw [full_response_endpoint_sum64] at hh
  simpa only [zero_mul,zero_add,add_zero] using hh

/-- The complete source component budget fits the certified affine order-64 row. -/
theorem full_response_extended_budget64_le (γ D : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hD : 0 ≤ D) :
    fullResponseTraceExtendedBudget γ 64 D ≤ ENNReal.ofReal
      (((invFull64Bt:ℝ)+γ*((invFull64KD:ℝ)*D+(invFull64K0:ℝ)))*(3:ℝ)^(2*γ*D)) := by
  have hs := full_response_endpoint_row64_nonneg γ D hγ hg hD
  have hlead := Finset.sum_le_sum (s := Finset.univ) (fun a _ => ENNReal.ofReal_le_ofReal
    (full_response_leading_row64_le γ D hγ hg hD a))
  have herr := Finset.sum_le_sum (s := Finset.univ) (fun b _ => ENNReal.ofReal_le_ofReal
    (full_response_error_row64_le γ D hγ hg hD b))
  have hnorm := add_le_add hlead herr
  change fullResponseTraceExtendedBudget γ 64 D ≤
    (∑ a : Fin 3, ENNReal.ofReal (fullResponseLeadingRow64 γ D a))+
      ∑ b : Fin 4, ENNReal.ofReal (fullResponseErrorRow64 γ D b) at hnorm
  apply hnorm.trans
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hs.1 a),
    ← ENNReal.ofReal_sum_of_nonneg (fun b _ => hs.2 b),
    ← ENNReal.ofReal_add (Finset.sum_nonneg (s := Finset.univ) (fun a _ => hs.1 a)) (Finset.sum_nonneg (s := Finset.univ) (fun b _ => hs.2 b)),
    full_response_endpoint_sum64]
  apply ENNReal.ofReal_le_ofReal
  have hz : 1 ≤ (3:ℝ)^(2*γ*D) := Real.one_le_rpow (by norm_num) (by positivity)
  have hb := mul_le_mul_of_nonneg_right hz full_response_Bt64_nonneg
  nlinarith only [hb]

/-- Actual order-64 full-response reset in sigmaBar_(l-1), with every source
input discharged and the literal certified Bt/KD/K0 profile. -/
theorem full_response_reference64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => rootTraceObservable M Q (Q.scale-342) N (Q.scale-1) weights ω/4)
      (ENNReal.ofReal 64) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        (((invFull64Bt:ℝ)+M.gamma*((invFull64KD:ℝ)*D+(invFull64K0:ℝ)))*(3:ℝ)^(2*M.gamma*D)) := by
  have hD : (0:ℝ) ≤ (N:ℝ)-(Q.scale:ℝ)+1 := by exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  exact (full_response_trace_Lp M h hM hg Q hpast N hN weights hw 64 (by norm_num) (by norm_num)).trans
    (full_response_extended_budget64_le M.gamma _ M.shellPrefix.gamma_pos.le hg hD)

/-- Every literal order-128 endpoint component is nonnegative. -/
theorem full_response_endpoint_row128_nonneg (γ D : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hD : 0 ≤ D) :
    (∀ a, 0 ≤ fullResponseLeadingRow128 γ D a) ∧ (∀ b, 0 ≤ fullResponseErrorRow128 γ D b) := by
  constructor
  · intro a
    exact (full_response_leading_budget_nonneg γ 128 D hγ hg (by norm_num) hD a).trans
      (full_response_leading_row128_le γ D hγ hg hD a)
  · intro b
    exact (full_response_error_budget_nonneg γ 128 D hγ hg (by norm_num) hD b).trans
      (full_response_error_row128_le γ D hγ hg hD b)

/-- The literal source baseline of the order-128 profile is nonnegative. -/
theorem full_response_Bt128_nonneg : (0:ℝ) ≤ (invFull128Bt:ℝ) := by
  have hs := full_response_endpoint_row128_nonneg 0 0 (by norm_num) (by norm_num [gammaZero]) (by norm_num)
  have hh := add_nonneg (Finset.sum_nonneg (s := Finset.univ) (fun a _ => hs.1 a)) (Finset.sum_nonneg (s := Finset.univ) (fun b _ => hs.2 b))
  rw [full_response_endpoint_sum128] at hh
  simpa only [zero_mul,zero_add,add_zero] using hh

/-- The complete source component budget fits the certified affine order-128 row. -/
theorem full_response_extended_budget128_le (γ D : ℝ) (hγ : 0 ≤ γ)
    (hg : γ ≤ gammaZero) (hD : 0 ≤ D) :
    fullResponseTraceExtendedBudget γ 128 D ≤ ENNReal.ofReal
      (((invFull128Bt:ℝ)+γ*((invFull128KD:ℝ)*D+(invFull128K0:ℝ)))*(3:ℝ)^(2*γ*D)) := by
  have hs := full_response_endpoint_row128_nonneg γ D hγ hg hD
  have hlead := Finset.sum_le_sum (s := Finset.univ) (fun a _ => ENNReal.ofReal_le_ofReal
    (full_response_leading_row128_le γ D hγ hg hD a))
  have herr := Finset.sum_le_sum (s := Finset.univ) (fun b _ => ENNReal.ofReal_le_ofReal
    (full_response_error_row128_le γ D hγ hg hD b))
  have hnorm := add_le_add hlead herr
  change fullResponseTraceExtendedBudget γ 128 D ≤
    (∑ a : Fin 3, ENNReal.ofReal (fullResponseLeadingRow128 γ D a))+
      ∑ b : Fin 4, ENNReal.ofReal (fullResponseErrorRow128 γ D b) at hnorm
  apply hnorm.trans
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hs.1 a),
    ← ENNReal.ofReal_sum_of_nonneg (fun b _ => hs.2 b),
    ← ENNReal.ofReal_add (Finset.sum_nonneg (s := Finset.univ) (fun a _ => hs.1 a)) (Finset.sum_nonneg (s := Finset.univ) (fun b _ => hs.2 b)),
    full_response_endpoint_sum128]
  apply ENNReal.ofReal_le_ofReal
  have hz : 1 ≤ (3:ℝ)^(2*γ*D) := Real.one_le_rpow (by norm_num) (by positivity)
  have hb := mul_le_mul_of_nonneg_right hz full_response_Bt128_nonneg
  nlinarith only [hb]

/-- Actual order-128 full-response reset in sigmaBar_(l-1), with every source
input discharged and the literal certified Bt/KD/K0 profile. -/
theorem full_response_reference128
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    eLpNorm (fun ω => rootTraceObservable M Q (Q.scale-342) N (Q.scale-1) weights ω/4)
      (ENNReal.ofReal 128) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        (((invFull128Bt:ℝ)+M.gamma*((invFull128KD:ℝ)*D+(invFull128K0:ℝ)))*(3:ℝ)^(2*M.gamma*D)) := by
  have hD : (0:ℝ) ≤ (N:ℝ)-(Q.scale:ℝ)+1 := by exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  exact (full_response_trace_Lp M h hM hg Q hpast N hN weights hw 128 (by norm_num) (by norm_num)).trans
    (full_response_extended_budget128_le M.gamma _ M.shellPrefix.gamma_pos.le hg hD)

end
end ASDExplicitGamma.Inverse
