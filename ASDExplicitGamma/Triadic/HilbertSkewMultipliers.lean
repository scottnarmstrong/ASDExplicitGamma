module

public import ASDExplicitGamma.Triadic.PlanarSobolev
public import ASDExplicitGamma.Response.FrameAlgebra
public import Homogenization.Sobolev.L2Ambient
public import Mathlib.MeasureTheory.Function.Holder

/-! Euclidean quarter turn and bounded L2 multiplication by actual L-infinity fields. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section

 def hilbertPlanarJ : HilbertVec 2 →ₗᵢ[ℝ] HilbertVec 2 where
  toFun x := HilbertVec.ofVec (matVecMul responsePlanarJ x.toVec)
  map_add' x y := by
    ext i
    fin_cases i <;> simp [matVecMul, responsePlanarJ, Fin.sum_univ_two, HilbertVec.toVec]
    ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [matVecMul, responsePlanarJ, Fin.sum_univ_two]
  norm_map' x := by
    have hs : ‖HilbertVec.ofVec (matVecMul responsePlanarJ x.toVec)‖^2=‖x‖^2 := by
      simp [HilbertVec.norm_sq_eq_sum_sq, matVecMul, responsePlanarJ, Fin.sum_univ_two, HilbertVec.toVec]
      ring
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hs

 def lpScalarMultiplication {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Lp ℝ ⊤ μ →L[ℝ] Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ⊤ 2 2

 theorem lpScalarMultiplication_norm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Lp ℝ ⊤ μ) :
    ‖lpScalarMultiplication (E := E) μ a‖ ≤ ‖a‖ := by
  have hB : ‖ContinuousLinearMap.lsmul ℝ ℝ (E := E)‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
  have hh := ContinuousLinearMap.norm_holderL_le (μ := μ) (p := ⊤) (q := 2) (r := 2)
    (ContinuousLinearMap.lsmul ℝ ℝ (E := E))
  have he := (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).holderL μ ⊤ 2 2 |>.le_opNorm a
  exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_right (hh.trans hB) (norm_nonneg a)])

 def lpVectorMultiplication {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Lp E ⊤ μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip.holderL μ ⊤ 2 2

 theorem lpVectorMultiplication_norm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Lp E ⊤ μ) :
    ‖lpVectorMultiplication μ a‖ ≤ ‖a‖ := by
  have hB : ‖(ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip‖ ≤ 1 := by
    rw [ContinuousLinearMap.opNorm_flip]
    exact ContinuousLinearMap.opNorm_lsmul_le
  have hh := ContinuousLinearMap.norm_holderL_le (μ := μ) (p := ⊤) (q := 2) (r := 2)
    (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip
  have he := (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip.holderL μ ⊤ 2 2 |>.le_opNorm a
  exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_right (hh.trans hB) (norm_nonneg a)])

 theorem lpScalarMultiplication_apply_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Lp ℝ ⊤ μ) (f : Lp E 2 μ) :
    lpScalarMultiplication μ a f =ᵐ[μ] fun x => a x • f x :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).coeFn_holder a f

 theorem lpVectorMultiplication_apply_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Lp E ⊤ μ) (f : Lp ℝ 2 μ) :
    lpVectorMultiplication μ a f =ᵐ[μ] fun x => f x • a x :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip.coeFn_holder a f

end
end ASDExplicitGamma.Triadic
