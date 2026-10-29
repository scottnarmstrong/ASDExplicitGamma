module

public import ASDExplicitGamma.Native.ParentRowCovarianceRoots
public import ASDExplicitGamma.Native.OldSignedQ1MultiplierCaps
public import ASDExplicitGamma.Native.OldSignedDerivativeRowMembership
public import ASDExplicitGamma.Native.OldSignedFiniteMinkowski

/-! Sharp derivative multiplier aggregation for the complete parent band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The two physical covariance eigenvalues retain their joint sqrt(2)
gain before shell aggregation. -/
theorem parent_row_derivative_multiplier_pointwise (r b L : ℝ) (hr : 0≤r) :
    Real.sqrt 2*oldSignedDerivativeKappa r b L≤
      (637/1000:ℝ)*Real.sqrt ((156/5:ℝ)*r^2*b^2/L^2)+
      (418/3125:ℝ)*Real.sqrt ((46488/25:ℝ)*r^4*b^2/L^4) := by
  have he1 : Real.sqrt 2*(r*Real.sqrt ((78/5:ℝ)*b^2/L^2))=
      Real.sqrt ((156/5:ℝ)*r^2*b^2/L^2) := by
    rw [old_signed_radius_sqrt r _ hr,←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have he2 : Real.sqrt 2*(r^2*Real.sqrt ((23244/25:ℝ)*b^2/L^4))=
      Real.sqrt ((46488/25:ℝ)*r^4*b^2/L^4) := by
    rw [old_signed_radius_sqrt (r^2) _ (sq_nonneg _),←Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have hc : planarC0*planarC1≤(418/3125:ℝ) := by
    have hh := mul_le_mul old_signed_q1_planarC0_le native_boundary_planarC1_le
      (Real.sqrt_nonneg _) (by norm_num : (0:ℝ)≤11/25)
    exact hh.trans_eq (by norm_num)
  calc
    _ = (2/Real.pi)*Real.sqrt ((156/5:ℝ)*r^2*b^2/L^2)+
        (planarC0*planarC1)*Real.sqrt ((46488/25:ℝ)*r^4*b^2/L^4) := by
      rw [←he1,←he2]
      unfold oldSignedDerivativeKappa
      ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right old_signed_q1_two_div_pi_le (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _))

/-- Finite Euclidean aggregation of all physical derivative rows preserves
the sharp covariance factor and a single sqrt(theta). -/
theorem parent_row_band_derivative_multiplier
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (height : ℕ) :
    Real.sqrt (∑ i : Fin height,(Real.sqrt 2*oldSignedDerivativeKappa
      (cubeScaleFactor (originCube 2 n)/3^5)
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)^2)≤
    Real.sqrt (theta M)*
      ((637/1000:ℝ)*Real.sqrt ((156/5:ℝ)*parentRowWeightedClock parentRowA2Weight height)+
        (418/3125:ℝ)*Real.sqrt ((46488/25:ℝ)*parentRowWeightedClock parentRowA4Weight height)) := by
  let r := cubeScaleFactor (originCube 2 n)/3^5
  let b := fun i : Fin height => q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)
  let L := fun i : Fin height => (q3ModelLength (n+((i.val+1:ℕ):ℤ))).val
  let E := fun i => (156/5:ℝ)*r^2*b i^2/L i^2
  let G := fun i => (46488/25:ℝ)*r^4*b i^2/L i^4
  have hr : 0≤r := div_nonneg (Triadic.cubeScaleFactor_pos' _).le (by positivity)
  have hm := old_signed_finite_sqrt_energy_bound E G
    (fun i => Real.sqrt 2*oldSignedDerivativeKappa r (b i) (L i))
    (by norm_num : (0:ℝ)≤637/1000) (by norm_num : (0:ℝ)≤418/3125)
    (fun i => by dsimp only [E]; positivity) (fun i => by dsimp only [G]; positivity)
    (fun i => mul_nonneg (Real.sqrt_nonneg _) (old_signed_derivative_kappa_nonneg hr _ _))
    (fun i => parent_row_derivative_multiplier_pointwise r (b i) (L i) hr)
  have hE : Real.sqrt (∑ i,E i)≤Real.sqrt (theta M)*
      Real.sqrt ((156/5:ℝ)*parentRowWeightedClock parentRowA2Weight height) := by
    have hh := parent_row_band_covariance_root M h hg n hstate height 1 (156/5) (by norm_num)
    change _≤Real.sqrt (theta M)*Real.sqrt ((156/5:ℝ)*
      parentRowWeightedClock (fun k => (1/9)^(k+6)) height)
    simpa only [Nat.mul_one,Nat.one_mul] using hh
  have hG : Real.sqrt (∑ i,G i)≤Real.sqrt (theta M)*
      Real.sqrt ((46488/25:ℝ)*parentRowWeightedClock parentRowA4Weight height) :=
    parent_row_band_covariance_root M h hg n hstate height 2 (46488/25) (by norm_num)
  exact hm.trans ((add_le_add
    (mul_le_mul_of_nonneg_left hE (by norm_num : (0:ℝ)≤637/1000))
    (mul_le_mul_of_nonneg_left hG (by norm_num : (0:ℝ)≤418/3125))).trans_eq (by ring))

end
end ASDExplicitGamma.Native
