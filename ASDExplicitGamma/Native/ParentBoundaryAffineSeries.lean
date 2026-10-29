module

public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral
public import ASDExplicitGamma.Native.OldSignedDirectionalIntegral

/-! Complete affine covariance series under a scalar expected matrix.
Positivity is used before summation, not on the identity-subtracted matrix. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory
noncomputable section

/-- A complete deterministic square-summable load family commutes with the
actual integrable positive matrix expectation, retaining its scalar coefficient. -/
theorem parent_boundary_affine_family_integral
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (A : Ω → Mat 2)
    (hint : ∀ i j,Integrable (fun omega => A omega i j) μ)
    (hpos : ∀ omega e,0≤vecDot e (matVecMul (A omega) e))
    (c : ℝ) (hmean : ∀ i j,(∫ omega,A omega i j ∂μ)=if i=j then c else 0)
    (E : I → Vec 2) (hE : Summable (fun i => vecNormSq (E i))) :
    Integrable (fun omega => ∑' i,vecDot (E i) (matVecMul (A omega) (E i))) μ ∧
    (∫ omega,∑' i,vecDot (E i) (matVecMul (A omega) (E i)) ∂μ)=
      c*∑' i,vecNormSq (E i) := by
  let q := fun i omega => vecDot (E i) (matVecMul (A omega) (E i))
  have hq (i) : Integrable (q i) μ := old_signed_quadratic_integrable μ A hint (E i)
  have hm (i) : (∫ omega,q i omega ∂μ)=c*vecNormSq (E i) :=
    old_signed_integral_scalar_quadratic μ A hint c hmean (E i)
  have hs (omega) : Summable (fun i => q i omega) := by
    have hsq (e : Vec 2) : 0≤vecNormSq e := vecNormSq_nonneg e
    have hbound (i) : q i omega≤Matrix.trace (A omega)*vecNormSq (E i) :=
      old_signed_nonnegative_quadratic_le_trace (A omega) (hpos omega) (E i)
    exact Summable.of_nonneg_of_le (fun i => hpos omega (E i)) hbound
      (hE.mul_left (Matrix.trace (A omega)))
  have hh := old_signed_nonnegative_series_integral μ q (fun i => c*vecNormSq (E i)) hq
    (fun i omega => hpos omega (E i)) hs (hE.mul_left c) (fun i => (hm i).le)
  refine ⟨hh.1,?_⟩
  have hn : Summable (fun i => ∫ omega,‖q i omega‖ ∂μ) := by
    apply (hE.mul_left c).congr
    intro i
    rw [←hm i]
    apply integral_congr_ae
    filter_upwards [] with omega
    exact (Real.norm_of_nonneg (hpos omega (E i))).symm
  rw [←integral_tsum_of_summable_integral_norm hq hn]
  simp_rw [hm]
  exact tsum_mul_left

/-- Subtracting the deterministic load norm preserves integrability and
subtracts it AFTER the complete positive covariance expectation. -/
theorem parent_boundary_affine_deviation_family_integral
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Mat 2)
    (hint : ∀ i j,Integrable (fun omega => A omega i j) μ)
    (hpos : ∀ omega e,0≤vecDot e (matVecMul (A omega) e))
    (c : ℝ) (hmean : ∀ i j,(∫ omega,A omega i j ∂μ)=if i=j then c else 0)
    (E : I → Vec 2) (hE : Summable (fun i => vecNormSq (E i))) :
    Integrable (fun omega => (∑' i,vecDot (E i) (matVecMul (A omega) (E i)))-
      ∑' i,vecNormSq (E i)) μ ∧
    (∫ omega,(∑' i,vecDot (E i) (matVecMul (A omega) (E i)))-∑' i,vecNormSq (E i) ∂μ)=
      (c-1)*∑' i,vecNormSq (E i) := by
  have hh := parent_boundary_affine_family_integral μ A hint hpos c hmean E hE
  refine ⟨hh.1.sub (integrable_const _),?_⟩
  rw [integral_sub hh.1 (integrable_const _),hh.2]
  simp only [integral_const,probReal_univ,one_smul]
  ring

/-- The literal signed mode series has the same complete expectation.
Its convergence is proved from the positive form before subtracting identity. -/
theorem parent_boundary_signed_affine_family_integral
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → Mat 2)
    (hint : ∀ i j,Integrable (fun omega => A omega i j) μ)
    (hpos : ∀ omega e,0≤vecDot e (matVecMul (A omega) e))
    (c : ℝ) (hmean : ∀ i j,(∫ omega,A omega i j ∂μ)=if i=j then c else 0)
    (E : I → Vec 2) (hE : Summable (fun i => vecNormSq (E i))) :
    Integrable (fun omega => ∑' i,(vecDot (E i) (matVecMul (A omega) (E i))-vecNormSq (E i))) μ ∧
    (∫ omega,∑' i,(vecDot (E i) (matVecMul (A omega) (E i))-vecNormSq (E i)) ∂μ)=
      (c-1)*∑' i,vecNormSq (E i) := by
  have hs (omega) : Summable (fun i => vecDot (E i) (matVecMul (A omega) (E i))) :=
    Summable.of_nonneg_of_le (fun i => hpos omega (E i))
      (fun i => old_signed_nonnegative_quadratic_le_trace (A omega) (hpos omega) (E i))
      (hE.mul_left (Matrix.trace (A omega)))
  have he (omega) : (∑' i,(vecDot (E i) (matVecMul (A omega) (E i))-vecNormSq (E i)))=
      (∑' i,vecDot (E i) (matVecMul (A omega) (E i)))-∑' i,vecNormSq (E i) :=
    (hs omega).tsum_sub hE
  simp_rw [he]
  exact parent_boundary_affine_deviation_family_integral μ A hint hpos c hmean E hE

end
end ASDExplicitGamma.Native
