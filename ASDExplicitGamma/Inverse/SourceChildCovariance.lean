module

public import ASDExplicitGamma.Inverse.PureFluxCovarianceTailSeries
public import ASDExplicitGamma.Numerics.Inverse.Covariance1

/-! The literal unweighted pure-flux covariance sum used in the one-pass estimate. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Numerics.Inverse

noncomputable def sourceChildCovarianceRowA (i : ℕ) : ℚ :=
  invCov1Ar*(1/3:ℚ)^(i+2)+invCov1BA*min (1/243:ℚ) ((1/3:ℚ)^(i+2))+
    invCov1CA*(min (1/243:ℚ) ((1/3:ℚ)^(i+2)))^2

noncomputable def sourceChildCovarianceRowB (i : ℕ) : ℚ :=
  invCov1Ar*(1/3:ℚ)^(i+2)+invCov1BB*min (1/243:ℚ) ((1/3:ℚ)^(i+2))+
    invCov1CB*(min (1/243:ℚ) ((1/3:ℚ)^(i+2)))^2

noncomputable def sourceChildCovarianceMuCap : Fin 16 → ℚ := ![invCov1Mu1,invCov1Mu2,invCov1Mu3,invCov1Mu4,invCov1Mu5,invCov1Mu6,invCov1Mu7,invCov1Mu8,invCov1Mu9,invCov1Mu10,invCov1Mu11,invCov1Mu12,invCov1Mu13,invCov1Mu14,invCov1Mu15,invCov1Mu16]

private theorem source_child_covariance_coefficient_caps :
    pureFluxCovarianceAr ≤ (invCov1Ar:ℝ) ∧ pureFluxCovarianceBA ≤ (invCov1BA:ℝ) ∧
    pureFluxCovarianceBB ≤ (invCov1BB:ℝ) ∧ pureFluxCovarianceCA ≤ (invCov1CA:ℝ) ∧
    pureFluxCovarianceCB ≤ (invCov1CB:ℝ) :=
  pureFlux_covariance_coefficient_caps

theorem source_child_covariance_rows_cap (i : ℕ) :
    pureFluxCovarianceA 1 i ≤ (sourceChildCovarianceRowA i:ℝ) ∧
      pureFluxCovarianceB 1 i ≤ (sourceChildCovarianceRowB i:ℝ) := by
  have hc := source_child_covariance_coefficient_caps
  have hr := (pureFlux_covariance_rho_pos 1 i).le
  have hd := (pureFlux_covariance_delta_bounds 1 i).1
  have hA := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hc.1 hr)
    (mul_le_mul_of_nonneg_right hc.2.1 hd))
    (mul_le_mul_of_nonneg_right hc.2.2.2.1 (sq_nonneg (pureFluxCovarianceDelta 1 i)))
  have hB := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hc.1 hr)
    (mul_le_mul_of_nonneg_right hc.2.2.1 hd))
    (mul_le_mul_of_nonneg_right hc.2.2.2.2 (sq_nonneg (pureFluxCovarianceDelta 1 i)))
  constructor
  · simpa only [pureFluxCovarianceA,pureFluxCovarianceRho,pureFluxCovarianceDelta,
      sourceChildCovarianceRowA,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_min,
      Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,show ∀ i : ℕ, 1+i+1=i+2 from fun i => by omega] using hA
  · simpa only [pureFluxCovarianceB,pureFluxCovarianceRho,pureFluxCovarianceDelta,
      sourceChildCovarianceRowB,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_min,
      Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,show ∀ i : ℕ, 1+i+1=i+2 from fun i => by omega] using hB

private theorem source_child_covariance_rational_certificate (A B C : ℚ)
    (h : 0 < C ∧ 0 ≤ 2*C-A^2 ∧
      A^4+4*(63/50:ℚ)^2*A^2*B^2 < (2*C-A^2)^2) :
    pureFluxCovarianceMu (A:ℝ) (B:ℝ) ≤ (C:ℝ) := by
  apply pureFlux_covariance_mu_le_of_certificate
  · exact_mod_cast h.2.1
  · have hh := (Rat.cast_le (K := ℝ)).mpr h.2.2.le
    norm_num only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
      Rat.cast_sub,Rat.cast_ofNat] at hh
    norm_num only [show (4:ℝ)*(63/50)^2=3969/625 by norm_num]
    exact hh

private theorem source_child_covariance_finite_numeric (i : Fin 16) :
    pureFluxCovarianceMu (sourceChildCovarianceRowA i:ℝ) (sourceChildCovarianceRowB i:ℝ) ≤
      (sourceChildCovarianceMuCap i:ℝ) := by
  fin_cases i
  · convert source_child_covariance_rational_certificate invCov1A1 invCov1B1 invCov1Mu1
      invCov1Mu1_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A1,invCov1B1,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A2 invCov1B2 invCov1Mu2
      invCov1Mu2_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A2,invCov1B2,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A3 invCov1B3 invCov1Mu3
      invCov1Mu3_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A3,invCov1B3,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A4 invCov1B4 invCov1Mu4
      invCov1Mu4_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A4,invCov1B4,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A5 invCov1B5 invCov1Mu5
      invCov1Mu5_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A5,invCov1B5,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A6 invCov1B6 invCov1Mu6
      invCov1Mu6_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A6,invCov1B6,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A7 invCov1B7 invCov1Mu7
      invCov1Mu7_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A7,invCov1B7,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A8 invCov1B8 invCov1Mu8
      invCov1Mu8_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A8,invCov1B8,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A9 invCov1B9 invCov1Mu9
      invCov1Mu9_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A9,invCov1B9,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A10 invCov1B10 invCov1Mu10
      invCov1Mu10_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A10,invCov1B10,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A11 invCov1B11 invCov1Mu11
      invCov1Mu11_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A11,invCov1B11,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A12 invCov1B12 invCov1Mu12
      invCov1Mu12_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A12,invCov1B12,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A13 invCov1B13 invCov1Mu13
      invCov1Mu13_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A13,invCov1B13,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A14 invCov1B14 invCov1Mu14
      invCov1Mu14_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A14,invCov1B14,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A15 invCov1B15 invCov1Mu15
      invCov1Mu15_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A15,invCov1B15,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert source_child_covariance_rational_certificate invCov1A16 invCov1B16 invCov1Mu16
      invCov1Mu16_root using 1 <;>
      norm_num [sourceChildCovarianceRowA,sourceChildCovarianceRowB,sourceChildCovarianceMuCap,
        invCov1A16,invCov1B16,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]

theorem source_child_covariance_finite_cap (i : Fin 16) :
    pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i) ≤
      (sourceChildCovarianceMuCap i:ℝ) := by
  have hrows := pureFlux_covariance_rows_order 1 i
  have hc := source_child_covariance_rows_cap i
  exact (pureFlux_covariance_mu_mono _ _ _ _ (hrows.1.trans hrows.2) hrows.1 hc.1 hc.2).trans
    (source_child_covariance_finite_numeric i)

/-- The real source coefficients, without shell-growth weights, obey the
certified plain sum. The entire infinite tail is included. -/
theorem source_child_covariance_plain_sum :
    Summable (fun i : ℕ => pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i)) ∧
      (∑' i : ℕ, pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i)) < 259713047/10^9 := by
  let f := fun i : ℕ => pureFluxCovarianceMu (pureFluxCovarianceA 1 i) (pureFluxCovarianceB 1 i)
  have hs : Summable f := by
    simpa only [Nat.zero_add] using (pureFlux_covariance_mu_tail_summable 1 0).1
  have htail : (∑' i : ℕ, f (i+16)) ≤ pureFluxCovarianceMuTailBudget 1 16 := by
    simpa only [Nat.add_comm] using (pureFlux_covariance_mu_tail_summable 1 16).2
  have hfinite : (∑ i ∈ Finset.range 16, f i) ≤ ∑ i : Fin 16, (sourceChildCovarianceMuCap i:ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum fun i _ => source_child_covariance_finite_cap i
  have hbudget : (∑ i : Fin 16, (sourceChildCovarianceMuCap i:ℝ))+
      pureFluxCovarianceMuTailBudget 1 16 = (invCov1PlainM:ℝ) := by
    simp only [pureFluxCovarianceMuTailBudget,
      show invCov0Ar=invCov1Ar from rfl, show invCov0BA=invCov1BA from rfl,
      show invCov0CA=invCov1CA from rfl]
    norm_num [Fin.sum_univ_succ, sourceChildCovarianceMuCap,
      invCov1PlainM,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
    ring
  have hnum : (invCov1PlainM:ℝ) < 259713047/10^9 := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr invCov1_plain_caps.2.1
    norm_num only [Rat.cast_ofScientific] at hh
    linarith only [hh]
  refine ⟨hs,?_⟩
  calc
    _ = (∑ i ∈ Finset.range 16, f i)+(∑' i : ℕ, f (i+16)) :=
      (hs.sum_add_tsum_nat_add 16).symm
    _ ≤ (∑ i : Fin 16, (sourceChildCovarianceMuCap i:ℝ))+pureFluxCovarianceMuTailBudget 1 16 :=
      add_le_add hfinite htail
    _ = (invCov1PlainM:ℝ) := hbudget
    _ < 259713047/10^9 := hnum

end ASDExplicitGamma.Inverse
