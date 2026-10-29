module

public import ASDExplicitGamma.Native.OldSignedResidualReciprocalEnergy
public import ASDExplicitGamma.Native.OldSignedPureSecondPairing

/-! Pure-second OLD sources pay inverse-history oscillation energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Haar duality against the reciprocal residual and inverse coercivity
give the sharp B coefficient for the actual pure-second source energy. -/
theorem old_signed_pure_second_source_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hzero : ∀ x,(F x).1=0)
    (hP₁ : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (F x).1 i))))
    (hP₂ : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (F x).2 i)))) :
    oldSignedEnergyPairing Q nu sigma k
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF))
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF)) ≤
      oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        oldSignedBlockPositiveNorm Q F ^ 2 := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let H := toHilbertBlockL2OfBlockField hF
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let J : Vec 2 → BlockVec 2 := scalarCoefficientFlux a Z
  let E := cubeAverage Q (fun x => blockVecDot (Z x) (J x))
  let P := oldSignedBlockPositiveNorm Q F
  let W := vectorWeakHaarNorm Q (fun x => (J x).2)
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hE : 0 ≤ E := by
    dsimp [E]
    rw [cube_average_eq_volume_average_open]
    exact scalar_coefficient_energy_average_nonneg Q a hEll Z
  have hPnonneg : 0 ≤ P := Real.sqrt_nonneg _
  have hWnonneg : 0 ≤ W := Real.sqrt_nonneg _
  have hMnonneg : 0 ≤ oldSignedInverseHistory Q a :=
    lemmaVInverseHistory_nonneg Q a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hWeak : W^2≤oldSignedInverseHistory Q a*E := by
    rw [show W^2=vectorWeakHaarEnergy Q (fun x => (J x).2) from Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)]
    have hh := old_signed_residual_reciprocal_weak_energy Q nu sigma hnu hsigma k H
    dsimp only [E]
    rw [cube_average_eq_volume_average_open Q]
    exact hh
  have hPair := old_signed_pure_second_pairing_bound Q hF
    (scalar_coefficient_flux_memL2 Q a hEll
      (Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k H))) hzero hP₁ hP₂
  have hEpair : E = volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (J x)) := by
    dsimp [E, J, a, Z, H]
    exact old_signed_residual_source_pairing Q nu sigma hnu hsigma k hF
  have hEupper : E ≤ P * W := by
    rw [← hEpair] at hPair
    exact (le_abs_self E).trans hPair
  have hPWnonneg : 0 ≤ P * W := mul_nonneg hPnonneg hWnonneg
  have hEsq : E ^ 2 ≤ oldSignedInverseHistory Q a * P ^ 2 * E := by
    have hmulSq : E ^ 2 ≤ (P * W) ^ 2 :=
      (sq_le_sq₀ hE (hPWnonneg)).2 hEupper
    calc
      E ^ 2 ≤ (P * W) ^ 2 := hmulSq
      _ = P ^ 2 * W ^ 2 := by ring
      _ ≤ P ^ 2 * (oldSignedInverseHistory Q a * E) :=
        mul_le_mul_of_nonneg_left hWeak (sq_nonneg P)
      _ = oldSignedInverseHistory Q a * P ^ 2 * E := by ring
  have hEnergy : E ≤ oldSignedInverseHistory Q a * P ^ 2 := by
    by_cases hzero : E = 0
    · rw [hzero]
      exact mul_nonneg hMnonneg (sq_nonneg P)
    · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
      have hcancel : E * E ≤ (oldSignedInverseHistory Q a * P ^ 2) * E := by
        calc
          E * E = E ^ 2 := by ring
          _ ≤ oldSignedInverseHistory Q a * P ^ 2 * E := hEsq
          _ = (oldSignedInverseHistory Q a * P ^ 2) * E := by ring
      exact le_of_mul_le_mul_right hcancel hEpos
  change oldSignedEnergyPairing Q nu sigma k Z Z ≤ _
  change volumeAverage (openCubeSet Q) (fun x => blockVecDot (Z x) (J x)) ≤ _
  rw [← cube_average_eq_volume_average_open Q (fun x => blockVecDot (Z x) (J x))]
  simpa [P, E, a] using hEnergy

end
end ASDExplicitGamma.Native
