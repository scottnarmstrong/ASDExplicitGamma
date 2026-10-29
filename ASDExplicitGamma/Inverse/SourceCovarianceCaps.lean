module

public import ASDExplicitGamma.Inverse.BankCovarianceSum
public import ASDExplicitGamma.Variational.LemmaVH2Constants

/-! Complete sharp covariance sums for the source generator. The finite
prefix uses small rational outward coefficients; the entire tail is retained. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Variational
noncomputable section

private def sourceKMajorant (i : ℕ) : ℝ :=
  3.9 * (pureFluxCovarianceRho 0 i)^2 +
  15.885 * pureFluxCovarianceRho 0 i * pureFluxCovarianceDelta 0 i +
  6.288 * (pureFluxCovarianceDelta 0 i)^2

private def sourceBMajorant (i : ℕ) : ℝ :=
  2.792849 * pureFluxCovarianceRho 0 i +
  5.687545 * pureFluxCovarianceDelta 0 i +
  8.690211 * (pureFluxCovarianceDelta 0 i)^2

private theorem source_k_coefficients :
    lemmaVH2C1 * (lemmaVH2R1 / Real.sqrt 2) ≤ 15.885 ∧
    lemmaVH2C2 * lemmaVH2R1 * Real.sqrt 2 ≤ 6.288 := by
  have hl : (1.4142:ℝ) ≤ Real.sqrt 2 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
  have hu : Real.sqrt 2 ≤ (1.414214:ℝ) :=
    (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩
  constructor
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2))).2
    norm_num [lemmaVH2C1, lemmaVH2R1]
    linarith only [hl]
  · norm_num [lemmaVH2C2, lemmaVH2R1]
    linarith only [hu]

private theorem source_k_majorant (i : ℕ) :
    lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i) ≤
      sourceKMajorant i := by
  have hρ := (pureFlux_covariance_rho_pos 0 i).le
  have hδ := (pureFlux_covariance_delta_bounds 0 i).1
  have hc := source_k_coefficients
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc.1 hρ) hδ
  have h2 := mul_le_mul_of_nonneg_right hc.2 (sq_nonneg (pureFluxCovarianceDelta 0 i))
  dsimp only [lemmaVH2R1] at h1 h2
  unfold lemmaVH2kn sourceKMajorant lemmaVH2R1
  linarith only [h1,h2]

/-- The common-center remainder coefficient is exactly the source reciprocal row. -/
theorem source_lemmaV_B_eq_covariance_B (i : ℕ) :
    lemmaVH2Bn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i) =
      pureFluxCovarianceB 0 i := by
  simp only [lemmaVH2Bn, pureFluxCovarianceB, pureFluxCovarianceAr, pureFluxCovarianceBB,
    pureFluxCovarianceCB, lemmaVH2R1, lemmaVH2C1, lemmaVH2C2, lemmaVH2A2]

private theorem source_b_majorant (i : ℕ) :
    pureFluxCovarianceB 0 i ≤ sourceBMajorant i := by
  have hc := pureFlux_covariance_coefficient_caps
  have ha : pureFluxCovarianceAr ≤ (2.792849:ℝ) := hc.1.trans (by
    norm_num [Numerics.Inverse.invCov0Ar])
  have hb : pureFluxCovarianceBB ≤ (5.687545:ℝ) := hc.2.2.1.trans (by
    norm_num [Numerics.Inverse.invCov0BB])
  have hd : pureFluxCovarianceCB ≤ (8.690211:ℝ) := hc.2.2.2.2.trans (by
    norm_num [Numerics.Inverse.invCov0CB])
  have hρ := (pureFlux_covariance_rho_pos 0 i).le
  have hδ := (pureFlux_covariance_delta_bounds 0 i).1
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right ha hρ)
    (mul_le_mul_of_nonneg_right hb hδ))
    (mul_le_mul_of_nonneg_right hd (sq_nonneg _))

private theorem source_majorant_tail (i : ℕ) :
    0 ≤ sourceKMajorant i ∧ sourceKMajorant i ≤ 27*(pureFluxCovarianceRho 0 i)^2 ∧
    0 ≤ sourceBMajorant i ∧ (sourceBMajorant i)^2 ≤ 324*(pureFluxCovarianceRho 0 i)^2 := by
  have hρ := (pureFlux_covariance_rho_pos 0 i).le
  have hρ1 : pureFluxCovarianceRho 0 i ≤ 1 := by
    unfold pureFluxCovarianceRho
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hd := pureFlux_covariance_delta_bounds 0 i
  have hδ := hd.1
  have hcross := mul_le_mul_of_nonneg_left hd.2 hρ
  have hsq := pow_le_pow_left₀ hd.1 hd.2 2
  have hrhosq : (pureFluxCovarianceRho 0 i)^2 ≤ pureFluxCovarianceRho 0 i := by
    nlinarith only [hρ,hρ1]
  have hB : sourceBMajorant i ≤ 18*pureFluxCovarianceRho 0 i := by
    unfold sourceBMajorant
    nlinarith only [hd.2,hsq,hrhosq,hρ]
  have hB0 : 0 ≤ sourceBMajorant i := by unfold sourceBMajorant; positivity
  refine ⟨by unfold sourceKMajorant; positivity, ?_, hB0, ?_⟩
  · unfold sourceKMajorant
    nlinarith only [hcross,hsq,sq_nonneg (pureFluxCovarianceRho 0 i)]
  · have hh := pow_le_pow_left₀ hB0 hB 2
    nlinarith only [hh]

private theorem source_majorant_sum_bound
    (f : ℕ → ℝ) (C U : ℝ)
    (h0 : ∀ i, 0 ≤ f i) (hbound : ∀ i, f i ≤ C*(pureFluxCovarianceRho 0 i)^2)
    (hfinite : (∑ i ∈ Finset.range 8, f i)+C*(1/3:ℝ)^18/(1-(1/3:ℝ)^2) < U) :
    Summable f ∧ (∑' i, f i) < U := by
  have hsum := (pureFlux_covariance_rho_power_hasSum 0 0 2 (by norm_num)).summable.mul_left C
  simp only [zero_add] at hsum
  have hs := hsum.of_nonneg_of_le h0 hbound
  have htail := (pureFlux_covariance_rho_power_hasSum 0 8 2 (by norm_num)).mul_left C
  have hts := htail.summable.of_nonneg_of_le (fun i => h0 (8+i)) (fun i => hbound (8+i))
  have hle := hts.tsum_le_tsum (fun i => hbound (8+i)) htail.summable
  have htailBound : (∑' i, f (i+8)) ≤ C*(1/3:ℝ)^18/(1-(1/3:ℝ)^2) := by
    have hh := hle.trans_eq htail.tsum_eq
    simpa only [Nat.add_comm, mul_div_assoc] using hh
  refine ⟨hs, ?_⟩
  calc
    _ = (∑ i ∈ Finset.range 8, f i)+(∑' i : ℕ, f (i+8)) :=
      (hs.sum_add_tsum_nat_add 8).symm
    _ ≤ (∑ i ∈ Finset.range 8, f i)+C*(1/3:ℝ)^18/(1-(1/3:ℝ)^2) :=
      add_le_add (le_refl _) htailBound
    _ < U := hfinite

/-- Complete unweighted single-direction sum in the source generator, including all future shells. -/
theorem source_covariance_k_sum :
    Summable (fun i => lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i)) ∧
    (∑' i, lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i)) < 0.521 := by
  have hmajor := source_majorant_sum_bound sourceKMajorant 27 0.521
    (fun i => (source_majorant_tail i).1) (fun i => (source_majorant_tail i).2.1) (by
      norm_num [sourceKMajorant,pureFluxCovarianceRho,pureFluxCovarianceDelta,Finset.sum_range_succ])
  have h0 (i : ℕ) : 0 ≤ lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i) := by
    have hρ := (pureFlux_covariance_rho_pos 0 i).le
    have hδ := (pureFlux_covariance_delta_bounds 0 i).1
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  have hs := hmajor.1.of_nonneg_of_le h0 source_k_majorant
  exact ⟨hs,(hs.tsum_le_tsum source_k_majorant hmajor.1).trans_lt hmajor.2⟩

/-- Complete sum of the two bracket coefficients in the source generator. -/
theorem source_covariance_q_sum :
    Summable (fun i => (pureFluxCovarianceB 0 i)^2 +
      lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i)) ∧
    (∑' i : ℕ, ((pureFluxCovarianceB 0 i)^2 +
      lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i))) < 1.565 := by
  let f := fun i => (sourceBMajorant i)^2+sourceKMajorant i
  have hmajor := source_majorant_sum_bound f 351 1.565
    (fun i => add_nonneg (sq_nonneg _) (source_majorant_tail i).1)
    (fun i => by have hh := source_majorant_tail i; dsimp [f]; linarith only [hh.2.1,hh.2.2.2]) (by
      norm_num [f,sourceBMajorant,sourceKMajorant,pureFluxCovarianceRho,pureFluxCovarianceDelta,Finset.sum_range_succ])
  have hbound (i : ℕ) : (pureFluxCovarianceB 0 i)^2+
      lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i) ≤ f i :=
    add_le_add (pow_le_pow_left₀ (pureFlux_covariance_rows_order 0 i).1 (source_b_majorant i) 2)
      (source_k_majorant i)
  have h0 (i : ℕ) : 0 ≤ (pureFluxCovarianceB 0 i)^2+
      lemmaVH2kn (pureFluxCovarianceRho 0 i) (pureFluxCovarianceDelta 0 i) := by
    have hρ := (pureFlux_covariance_rho_pos 0 i).le
    have hδ := (pureFlux_covariance_delta_bounds 0 i).1
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  have hs := hmajor.1.of_nonneg_of_le h0 hbound
  exact ⟨hs,(hs.tsum_le_tsum hbound hmajor.1).trans_lt hmajor.2⟩

end
end ASDExplicitGamma.Inverse
