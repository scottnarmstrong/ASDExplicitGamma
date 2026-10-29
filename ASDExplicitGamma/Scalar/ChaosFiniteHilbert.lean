module

public import ASDExplicitGamma.Scalar.ChaosEnvelopeNorm
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! A finite Gaussian quadratic may take values in an arbitrary real Hilbert space. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] {n : ℕ}

/-- Actual centered quadratic Gaussian polynomial with Hilbert-valued coefficients. -/
noncomputable def finiteHilbertGaussianQuadratic (B : Fin n → Fin n → W)
    (x : EuclideanSpace ℝ (Fin n)) : W :=
  ∑ i,∑ j,(x i*x j-(if i=j then 1 else 0:ℝ)) • B i j

/-- The finite-dimensional span includes the deterministic mean and all quadratic coefficients. -/
def finiteHilbertChaosGenerators (m : W) (B : Fin n → Fin n → W) : Option (Fin n × Fin n) → W
  | none => m
  | some ij => B ij.1 ij.2

/-- This is a genuine finite span inside the ambient Hilbert space. -/
def finiteHilbertChaosSpan (m : W) (B : Fin n → Fin n → W) : Submodule ℝ W :=
  Submodule.span ℝ (Set.range (finiteHilbertChaosGenerators m B))

noncomputable instance instFiniteDimensionalHilbertChaosSpan (m : W) (B : Fin n → Fin n → W) :
    FiniteDimensional ℝ (finiteHilbertChaosSpan m B) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- The deterministic mean belongs to this span. -/
theorem mean_mem_finite_hilbert_chaos_span (m : W) (B : Fin n → Fin n → W) :
    m∈finiteHilbertChaosSpan m B := Submodule.subset_span ⟨none,rfl⟩

/-- Every quadratic coefficient belongs to this span. -/
theorem coefficient_mem_finite_hilbert_chaos_span (m : W) (B : Fin n → Fin n → W) (i j : Fin n) :
    B i j∈finiteHilbertChaosSpan m B := Submodule.subset_span ⟨some (i,j),rfl⟩

/-- The whole affine quadratic polynomial belongs to the finite span pointwise. -/
theorem affine_quadratic_mem_finite_hilbert_chaos_span (m : W) (B : Fin n → Fin n → W)
    (x : EuclideanSpace ℝ (Fin n)) : m+finiteHilbertGaussianQuadratic B x∈finiteHilbertChaosSpan m B := by
  apply (finiteHilbertChaosSpan m B).add_mem (mean_mem_finite_hilbert_chaos_span m B)
  exact (finiteHilbertChaosSpan m B).sum_mem (fun i _ =>
    (finiteHilbertChaosSpan m B).sum_mem (fun j _ =>
      (finiteHilbertChaosSpan m B).smul_mem _ (coefficient_mem_finite_hilbert_chaos_span m B i j)))

/-- Canonical orthonormal coordinates on the actual finite coefficient span. -/
noncomputable def finiteHilbertChaosBasis (m : W) (B : Fin n → Fin n → W) :
    OrthonormalBasis (Fin (Module.finrank ℝ (finiteHilbertChaosSpan m B))) ℝ (finiteHilbertChaosSpan m B) :=
  stdOrthonormalBasis ℝ (finiteHilbertChaosSpan m B)

/-- Scalar symmetric coefficient matrix in one output Hilbert coordinate. -/
noncomputable def finiteHilbertChaosMatrix (m : W) (B : Fin n → Fin n → W)
    (k : Fin (Module.finrank ℝ (finiteHilbertChaosSpan m B))) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ ((finiteHilbertChaosBasis m B k : finiteHilbertChaosSpan m B) : W) (B i j)

/-- The deterministic mean in the same output coordinates. -/
noncomputable def finiteHilbertChaosMean (m : W) (B : Fin n → Fin n → W)
    (k : Fin (Module.finrank ℝ (finiteHilbertChaosSpan m B))) : ℝ :=
  inner ℝ ((finiteHilbertChaosBasis m B k : finiteHilbertChaosSpan m B) : W) m

/-- Symmetric Hilbert coefficients produce exactly symmetric scalar quadratic matrices. -/
theorem finite_hilbert_chaos_matrix_hermitian (m : W) (B : Fin n → Fin n → W)
    (hB : ∀ i j,B i j=B j i) (k) : (finiteHilbertChaosMatrix m B k).IsHermitian := by
  ext i j
  simp [finiteHilbertChaosMatrix,Matrix.conjTranspose_apply,hB i j]

end ASDExplicitGamma.Scalar
