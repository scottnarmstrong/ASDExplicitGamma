module

public import ASDExplicitGamma.Inverse.PureFluxCovarianceTailSeries

/-! The literal unweighted pure-flux covariance sum used in the one-pass estimate. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open ASDExplicitGamma.Numerics.Inverse

noncomputable def bankCovarianceRowA (i : ℕ) : ℚ :=
  invCov0Ar*(1/3:ℚ)^(i+1)+invCov0BA*min (1/243:ℚ) ((1/3:ℚ)^(i+1))+
    invCov0CA*(min (1/243:ℚ) ((1/3:ℚ)^(i+1)))^2

noncomputable def bankCovarianceRowB (i : ℕ) : ℚ :=
  invCov0Ar*(1/3:ℚ)^(i+1)+invCov0BB*min (1/243:ℚ) ((1/3:ℚ)^(i+1))+
    invCov0CB*(min (1/243:ℚ) ((1/3:ℚ)^(i+1)))^2

noncomputable def bankCovarianceMuCap : Fin 16 → ℚ := ![invCov0Mu1,invCov0Mu2,invCov0Mu3,invCov0Mu4,invCov0Mu5,invCov0Mu6,invCov0Mu7,invCov0Mu8,invCov0Mu9,invCov0Mu10,invCov0Mu11,invCov0Mu12,invCov0Mu13,invCov0Mu14,invCov0Mu15,invCov0Mu16]

theorem bank_covariance_rows_cap (i : ℕ) :
    pureFluxCovarianceA 0 i ≤ (bankCovarianceRowA i:ℝ) ∧
      pureFluxCovarianceB 0 i ≤ (bankCovarianceRowB i:ℝ) := by
  have hc := pureFlux_covariance_coefficient_caps
  have hr := (pureFlux_covariance_rho_pos 0 i).le
  have hd := (pureFlux_covariance_delta_bounds 0 i).1
  have hA := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hc.1 hr)
    (mul_le_mul_of_nonneg_right hc.2.1 hd))
    (mul_le_mul_of_nonneg_right hc.2.2.2.1 (sq_nonneg (pureFluxCovarianceDelta 0 i)))
  have hB := add_le_add (add_le_add (mul_le_mul_of_nonneg_right hc.1 hr)
    (mul_le_mul_of_nonneg_right hc.2.2.1 hd))
    (mul_le_mul_of_nonneg_right hc.2.2.2.2 (sq_nonneg (pureFluxCovarianceDelta 0 i)))
  constructor
  · simpa only [pureFluxCovarianceA,pureFluxCovarianceRho,pureFluxCovarianceDelta,
      bankCovarianceRowA,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_min,
      Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,zero_add] using hA
  · simpa only [pureFluxCovarianceB,pureFluxCovarianceRho,pureFluxCovarianceDelta,
      bankCovarianceRowB,Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_min,
      Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,zero_add] using hB

private theorem bank_covariance_rational_certificate (A B C : ℚ)
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

private theorem bank_covariance_finite_numeric (i : Fin 16) :
    pureFluxCovarianceMu (bankCovarianceRowA i:ℝ) (bankCovarianceRowB i:ℝ) ≤
      (bankCovarianceMuCap i:ℝ) := by
  fin_cases i
  · convert bank_covariance_rational_certificate invCov0A1 invCov0B1 invCov0Mu1
      invCov0Mu1_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A1,invCov0B1,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A2 invCov0B2 invCov0Mu2
      invCov0Mu2_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A2,invCov0B2,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A3 invCov0B3 invCov0Mu3
      invCov0Mu3_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A3,invCov0B3,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A4 invCov0B4 invCov0Mu4
      invCov0Mu4_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A4,invCov0B4,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A5 invCov0B5 invCov0Mu5
      invCov0Mu5_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A5,invCov0B5,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A6 invCov0B6 invCov0Mu6
      invCov0Mu6_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A6,invCov0B6,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A7 invCov0B7 invCov0Mu7
      invCov0Mu7_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A7,invCov0B7,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A8 invCov0B8 invCov0Mu8
      invCov0Mu8_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A8,invCov0B8,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A9 invCov0B9 invCov0Mu9
      invCov0Mu9_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A9,invCov0B9,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A10 invCov0B10 invCov0Mu10
      invCov0Mu10_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A10,invCov0B10,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A11 invCov0B11 invCov0Mu11
      invCov0Mu11_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A11,invCov0B11,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A12 invCov0B12 invCov0Mu12
      invCov0Mu12_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A12,invCov0B12,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A13 invCov0B13 invCov0Mu13
      invCov0Mu13_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A13,invCov0B13,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A14 invCov0B14 invCov0Mu14
      invCov0Mu14_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A14,invCov0B14,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A15 invCov0B15 invCov0Mu15
      invCov0Mu15_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A15,invCov0B15,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  · convert bank_covariance_rational_certificate invCov0A16 invCov0B16 invCov0Mu16
      invCov0Mu16_root using 1 <;>
      norm_num [bankCovarianceRowA,bankCovarianceRowB,bankCovarianceMuCap,
        invCov0A16,invCov0B16,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]

theorem bank_covariance_finite_cap (i : Fin 16) :
    pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i) ≤
      (bankCovarianceMuCap i:ℝ) := by
  have hrows := pureFlux_covariance_rows_order 0 i
  have hc := bank_covariance_rows_cap i
  exact (pureFlux_covariance_mu_mono _ _ _ _ (hrows.1.trans hrows.2) hrows.1 hc.1 hc.2).trans
    (bank_covariance_finite_numeric i)


/-- The real source coefficients, without shell-growth weights, obey the
certified plain sum. The entire infinite tail is included. -/
theorem bank_covariance_plain_sum :
    Summable (fun i : ℕ => pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)) ∧
      (∑' i : ℕ, pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)) < 79/40 := by
  let f := fun i : ℕ => pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)
  have hs : Summable f := by
    simpa only [Nat.zero_add] using (pureFlux_covariance_mu_tail_summable 0 0).1
  have htail : (∑' i : ℕ, f (i+16)) ≤ pureFluxCovarianceMuTailBudget 0 16 := by
    simpa only [Nat.add_comm] using (pureFlux_covariance_mu_tail_summable 0 16).2
  have hfinite : (∑ i ∈ Finset.range 16, f i) ≤ ∑ i : Fin 16, (bankCovarianceMuCap i:ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_le_sum fun i _ => bank_covariance_finite_cap i
  have hbudget : (∑ i : Fin 16, (bankCovarianceMuCap i:ℝ))+
      pureFluxCovarianceMuTailBudget 0 16 = (invCov0PlainM:ℝ) := by
    norm_num [Fin.sum_univ_succ, bankCovarianceMuCap,pureFluxCovarianceMuTailBudget,
      invCov0PlainM,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
    ring
  have hnum : (invCov0PlainM:ℝ) < 79/40 := by
    have hh := (Rat.cast_lt (K:=ℝ)).mpr invCov0_plain_caps.2.1
    norm_num only [Rat.cast_ofScientific] at hh
    linarith only [hh]
  refine ⟨hs,?_⟩
  calc
    _ = (∑ i ∈ Finset.range 16, f i)+(∑' i : ℕ, f (i+16)) :=
      (hs.sum_add_tsum_nat_add 16).symm
    _ ≤ (∑ i : Fin 16, (bankCovarianceMuCap i:ℝ))+pureFluxCovarianceMuTailBudget 0 16 :=
      add_le_add hfinite htail
    _ = (invCov0PlainM:ℝ) := hbudget
    _ < 79/40 := hnum

/-- Every finite insertion band is bounded by the same unweighted coefficient sum. -/
theorem bank_covariance_plain_partial_sum (s : Finset ℕ) :
    (∑ i ∈ s, pureFluxCovarianceMu (pureFluxCovarianceA 0 i) (pureFluxCovarianceB 0 i)) ≤ 79/40 := by
  exact (bank_covariance_plain_sum.1.sum_le_tsum s
    (fun i _ => (pureFlux_covariance_mu_lower _ _).1)).trans bank_covariance_plain_sum.2.le

end ASDExplicitGamma.Inverse
