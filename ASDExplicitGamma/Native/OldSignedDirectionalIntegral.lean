module

public import ASDExplicitGamma.Main.AffineBlockTraceMeans
public import ASDExplicitGamma.Native.OldSignedDirectionalDepthTraceBound

/-! Finite-dimensional expectation identities used to turn actual square
symmetry into a directional half-trace payment. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory
noncomputable section

/-- A genuine integrable matrix quadratic form commutes with expectation. -/
theorem old_signed_integral_quadratic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Mat 2)
    (hA : ∀ i j,Integrable (fun ω => A ω i j) μ) (e : Vec 2) :
    (∫ ω,vecDot e (matVecMul (A ω) e) ∂μ)=
      vecDot e (matVecMul (fun i j => ∫ ω,A ω i j ∂μ) e) := by
  simp only [vecDot,matVecMul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    ((hA i j).mul_const (e j)).const_mul (e i)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum _ (fun j _ => ((hA i j).mul_const (e j)).const_mul (e i))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,integral_mul_const]

/-- Integrability of the quadratic form follows from its finitely many
actual matrix entries. -/
theorem old_signed_quadratic_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Mat 2)
    (hA : ∀ i j,Integrable (fun ω => A ω i j) μ) (e : Vec 2) :
    Integrable (fun ω => vecDot e (matVecMul (A ω) e)) μ := by
  simp only [vecDot,matVecMul,Finset.mul_sum]
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
    ((hA i j).mul_const (e j)).const_mul (e i)))

/-- A scalar expected matrix has exactly its scalar mean times the load
norm squared; this is an expectation identity, not a pathwise half bound. -/
theorem old_signed_integral_scalar_quadratic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Ω → Mat 2)
    (hA : ∀ i j,Integrable (fun ω => A ω i j) μ) (c : ℝ)
    (hmean : ∀ i j,(∫ ω,A ω i j ∂μ)=if i=j then c else 0) (e : Vec 2) :
    (∫ ω,vecDot e (matVecMul (A ω) e) ∂μ)=c*vecNormSq e := by
  rw [old_signed_integral_quadratic μ A hA e]
  simp only [hmean,vecDot,matVecMul,vecNormSq,Fin.sum_univ_two]
  norm_num
  ring

end
end ASDExplicitGamma.Native
