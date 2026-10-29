module

public import ASDExplicitGamma.Numerics.Joint.LocalCaps
public import Mathlib.Data.Matrix.Mul

/-! Largest real eigenvalue of the source symmetric 2×2 generator matrix.
The trace is a and determinant is -b², so the larger characteristic root is
(a+sqrt(a²+4b²))/2. The eigenvector and maximality are proved below. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics

noncomputable def generatorMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;b,0]
noncomputable def generatorLambdaMax (a b : ℝ) : ℝ := (a+Real.sqrt (a^2+4*b^2))/2

def IsLargestRealEigenvalue (A : Matrix (Fin 2) (Fin 2) ℝ) (mu : ℝ) : Prop :=
  (∃ v : Fin 2 → ℝ, v ≠ 0 ∧ A.mulVec v = mu • v) ∧
    ∀ e : ℝ, ∀ v : Fin 2 → ℝ, v ≠ 0 → A.mulVec v = e • v → e ≤ mu

theorem generator_characteristic_root (a b : ℝ) :
    (generatorLambdaMax a b)^2-a*generatorLambdaMax a b-b^2 = 0 := by
  have hs := Real.sq_sqrt (by positivity : (0:ℝ) ≤ a^2+4*b^2)
  unfold generatorLambdaMax
  nlinarith only [hs]

/-- An explicit nonzero eigenvector and domination of every real eigenvalue. -/
theorem generator_lambdaMax_is_largest (a b : ℝ) (hb : 0 < b) :
    IsLargestRealEigenvalue (generatorMatrix a b) (generatorLambdaMax a b) := by
  have hroot := generator_characteristic_root a b
  constructor
  · refine ⟨![generatorLambdaMax a b,b],?_,?_⟩
    · intro h
      have hh := congrFun h 1
      simp only [Matrix.cons_val_one,Matrix.cons_val_zero,Pi.zero_apply] at hh
      exact hb.ne' hh
    · ext i
      fin_cases i <;> simp [generatorMatrix,Matrix.mulVec]
      · linarith only [hroot]
      · ring
  · intro e v hv he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    simp only [generatorMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Pi.smul_apply,smul_eq_mul,zero_mul,add_zero] at h0 h1
    have hx : v 0 ≠ 0 := by
      intro hz
      have hy : v 1 = 0 := by
        have hby : b*v 1 = 0 := by simpa only [hz,mul_zero,zero_add] using h0
        exact (mul_eq_zero.mp hby).resolve_left hb.ne'
      apply hv
      ext i
      fin_cases i
      · exact hz
      · exact hy
    have hp : (e^2-a*e-b^2)*v 0 = 0 := by
      calc
        _ = e*(e*v 0-a*v 0-b*v 1)+b*(e*v 1-b*v 0) := by ring
        _ = 0 := by rw [← h0,← h1]; ring
    have hr := (mul_eq_zero.mp hp).resolve_right hx
    have hd : (2*e-a)^2 ≤ a^2+4*b^2 := by nlinarith only [hr]
    have hs := Real.le_sqrt_of_sq_le hd
    unfold generatorLambdaMax
    linarith only [hs]

end ASDExplicitGamma.Numerics
