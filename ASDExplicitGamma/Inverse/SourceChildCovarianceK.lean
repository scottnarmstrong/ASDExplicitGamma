module

public import ASDExplicitGamma.Inverse.SourceChildCovariance
public import ASDExplicitGamma.Variational.LemmaVH2Constants

/-! The complete shifted deterministic covariance sum of the source generator. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Inverse
noncomputable section

/-- The reciprocal Lemma V row is the actual covariance row at every protected shift. -/
theorem source_shifted_lemmaV_B_eq_covariance_B (q i : ℕ) :
    lemmaVH2Bn (pureFluxCovarianceRho q i) (pureFluxCovarianceDelta q i) =
      pureFluxCovarianceB q i := by
  simp only [lemmaVH2Bn,pureFluxCovarianceB,pureFluxCovarianceAr,pureFluxCovarianceBB,
    pureFluxCovarianceCB,lemmaVH2R1,lemmaVH2C1,lemmaVH2C2,lemmaVH2A2]

/-- The exact rational majorant of a shifted single-shell deterministic
covariance coefficient. Its radicals are the existing source certificates. -/
def sourceChildCovarianceKMajorant (i : ℕ) : ℝ :=
  (invCov1K0:ℝ)*(pureFluxCovarianceRho 1 i)^2+
  (invCov1K1:ℝ)*pureFluxCovarianceRho 1 i*pureFluxCovarianceDelta 1 i+
  (invCov1K2:ℝ)*(pureFluxCovarianceDelta 1 i)^2

private theorem source_child_k_coefficient_caps :
    lemmaVH2C1*(lemmaVH2R1/Real.sqrt 2) ≤ (invCov1K1:ℝ) ∧
    lemmaVH2C2*lemmaVH2R1*Real.sqrt 2 ≤ (invCov1K2:ℝ) := by
  have hc := invCov1_mixed_roots
  constructor
  · have hh := Numerics.Inverse.inv_sqrt_upper hc.1.le hc.2.1
    have he : Real.sqrt (((1.440*(78/5))^2/2:ℚ):ℝ) =
        lemmaVH2C1*(lemmaVH2R1/Real.sqrt 2) := by
      push_cast
      rw [Real.sqrt_div (by positivity),Real.sqrt_sq_eq_abs]
      norm_num [lemmaVH2C1,lemmaVH2R1]
      ring
    rw [he] at hh
    exact hh
  · have hh := pureFlux_scaled_sqrt_cap ((57/200)*(78/5)) 2 invCov1K2
      (by norm_num) hc.2.2.1.le (by convert hc.2.2.2 using 1; norm_num)
    simpa only [Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat,lemmaVH2C2,lemmaVH2R1] using hh

/-- The literal deterministic coefficient is bounded by its certified
rational shifted row, at every depth including the unbounded tail. -/
theorem source_child_k_le_majorant (i : ℕ) :
    lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i) ≤
      sourceChildCovarianceKMajorant i := by
  have hr := (pureFlux_covariance_rho_pos 1 i).le
  have hd := (pureFlux_covariance_delta_bounds 1 i).1
  have hc := source_child_k_coefficient_caps
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc.1 hr) hd
  have h2 := mul_le_mul_of_nonneg_right hc.2 (sq_nonneg (pureFluxCovarianceDelta 1 i))
  unfold lemmaVH2kn sourceChildCovarianceKMajorant
  have h0 : lemmaVH2R1/4=(invCov1K0:ℝ) := by norm_num [lemmaVH2R1,invCov1K0]
  rw [h0]
  exact add_le_add (add_le_add le_rfl h1) h2

private theorem source_child_k_tail_bound (i : ℕ) :
    0 ≤ sourceChildCovarianceKMajorant i ∧
      sourceChildCovarianceKMajorant i ≤
        ((invCov1K0+invCov1K1+invCov1K2:ℚ):ℝ)*(pureFluxCovarianceRho 1 i)^2 := by
  have hr := (pureFlux_covariance_rho_pos 1 i).le
  have hd := pureFlux_covariance_delta_bounds 1 i
  have hK0 : (0:ℝ) ≤ invCov1K0 := by norm_num [invCov1K0]
  have hK1 : (0:ℝ) ≤ invCov1K1 := by norm_num [invCov1K1]
  have hK2 : (0:ℝ) ≤ invCov1K2 := by norm_num [invCov1K2]
  refine ⟨?_,?_⟩
  · exact add_nonneg (add_nonneg (mul_nonneg hK0 (sq_nonneg _))
      (mul_nonneg (mul_nonneg hK1 hr) hd.1)) (mul_nonneg hK2 (sq_nonneg _))
  have h1 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd.2 hr) hK1
  have h2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd.1 hd.2 2) hK2
  dsimp only [sourceChildCovarianceKMajorant]
  push_cast
  have he : (invCov1K1:ℝ)*pureFluxCovarianceRho 1 i*pureFluxCovarianceDelta 1 i =
      (invCov1K1:ℝ)*(pureFluxCovarianceRho 1 i*pureFluxCovarianceDelta 1 i) := by ring
  rw [he]
  nlinarith only [h1,h2]

/-- Exact finite-prefix identity with the source's complete geometric tail.
The numerical certificate already includes that tail. -/
theorem source_child_k_majorant_budget :
    (∑ i ∈ Finset.range 16, sourceChildCovarianceKMajorant i)+
      ((invCov1K0+invCov1K1+invCov1K2:ℚ):ℝ)*
        (1/3:ℝ)^36/(1-(1/3:ℝ)^2) = (invCov1PlainK:ℝ) := by
  norm_num [sourceChildCovarianceKMajorant,pureFluxCovarianceRho,pureFluxCovarianceDelta,
    Finset.sum_range_succ,invCov1PlainK,
    invCov1RowK1,invCov1RowK2,invCov1RowK3,invCov1RowK4,
    invCov1RowK5,invCov1RowK6,invCov1RowK7,invCov1RowK8,
    invCov1RowK9,invCov1RowK10,invCov1RowK11,invCov1RowK12,
    invCov1RowK13,invCov1RowK14,invCov1RowK15,invCov1RowK16,
    Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow]
  ring

/-- The complete actual shifted covariance sum is below the exact refined
K coefficient `0.065399707`; no finite-tail hypothesis is retained. -/
theorem source_child_covariance_k_sum :
    Summable (fun i => lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i)) ∧
      (∑' i, lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i)) <
        65399707/10^9 := by
  let f := sourceChildCovarianceKMajorant
  let C : ℝ := (invCov1K0+invCov1K1+invCov1K2:ℚ)
  have hmajor := (pureFlux_covariance_rho_power_hasSum 1 0 2 (by norm_num)).summable.mul_left C
  simp only [zero_add] at hmajor
  have hs : Summable f := hmajor.of_nonneg_of_le
    (fun i => (source_child_k_tail_bound i).1) (fun i => (source_child_k_tail_bound i).2)
  have htail := (pureFlux_covariance_rho_power_hasSum 1 16 2 (by norm_num)).mul_left C
  have hts : Summable (fun i => f (16+i)) := htail.summable.of_nonneg_of_le
    (fun i => (source_child_k_tail_bound (16+i)).1)
    (fun i => (source_child_k_tail_bound (16+i)).2)
  have htailcap := (hts.tsum_le_tsum
    (fun i => (source_child_k_tail_bound (16+i)).2) htail.summable).trans_eq htail.tsum_eq
  have hsum : (∑' i, f i) ≤ (invCov1PlainK:ℝ) := by
    rw [←source_child_k_majorant_budget]
    rw [←hs.sum_add_tsum_nat_add 16]
    have hcap : (∑' i, f (i+16)) ≤ C*(1/3:ℝ)^36/(1-(1/3:ℝ)^2) := by
      simpa only [Nat.add_comm,mul_div_assoc] using htailcap
    exact add_le_add le_rfl hcap
  have h0 (i : ℕ) : 0 ≤ lemmaVH2kn (pureFluxCovarianceRho 1 i) (pureFluxCovarianceDelta 1 i) := by
    have hr := (pureFlux_covariance_rho_pos 1 i).le
    have hd := (pureFlux_covariance_delta_bounds 1 i).1
    unfold lemmaVH2kn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
    positivity
  have hactual := hs.of_nonneg_of_le h0 source_child_k_le_majorant
  refine ⟨hactual,(hactual.tsum_le_tsum source_child_k_le_majorant hs).trans_lt ?_⟩
  apply hsum.trans_lt
  have hnum := (Rat.cast_lt (K := ℝ)).mpr invCov1_plain_caps.1
  norm_num only [Rat.cast_ofScientific] at hnum
  simpa only [show (10:ℝ)^9=1000000000 by norm_num] using hnum

end
end ASDExplicitGamma.Inverse
