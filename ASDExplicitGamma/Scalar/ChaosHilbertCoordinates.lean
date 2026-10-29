module

public import ASDExplicitGamma.Scalar.ChaosFiniteHilbert

/-! Exact scalar coordinates of the genuine Hilbert-valued quadratic Gaussian envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-- Expanded entries of the actual centered Gaussian quadratic form. -/
theorem centered_gaussian_quadratic_entries {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : centeredGaussianQuadratic A x=
      ∑ i,∑ j,(x i*x j-(if i=j then 1 else 0:ℝ))*A i j := by
  unfold centeredGaussianQuadratic
  rw [Matrix.inner_toEuclideanCLM]
  change (∑ i,x i*(∑ j,A i j*x j))-(∑ i,A i i)=_
  simp only [Finset.mul_sum,sub_mul,Finset.sum_sub_distrib,ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] {n : ℕ}

/-- Taking a Hilbert coordinate gives the actual centered scalar quadratic matrix. -/
theorem inner_finite_hilbert_gaussian_quadratic (w : W) (B : Fin n → Fin n → W)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ w (finiteHilbertGaussianQuadratic B x)=
      centeredGaussianQuadratic (Matrix.of (fun i j => inner ℝ w (B i j))) x := by
  rw [centered_gaussian_quadratic_entries]
  simp only [finiteHilbertGaussianQuadratic,inner_sum,real_inner_smul_right,Matrix.of_apply]

/-- The source Hilbert envelope is exactly the previously proved finite scalar-coordinate envelope. -/
theorem finite_hilbert_gaussian_envelope_coordinates (m : W) (B : Fin n → Fin n → W)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖m+finiteHilbertGaussianQuadratic B x‖^2=
      finiteGaussianEnvelope (finiteHilbertChaosMean m B) (finiteHilbertChaosMatrix m B) x := by
  let z : finiteHilbertChaosSpan m B :=
    ⟨m+finiteHilbertGaussianQuadratic B x,affine_quadratic_mem_finite_hilbert_chaos_span m B x⟩
  have h := (finiteHilbertChaosBasis m B).sum_sq_inner_right z
  unfold finiteGaussianEnvelope
  calc
    _ = ∑ k, (inner ℝ ((finiteHilbertChaosBasis m B k : finiteHilbertChaosSpan m B) : W)
        (m+finiteHilbertGaussianQuadratic B x))^2 := by
      simpa only [Submodule.coe_inner,← Submodule.norm_coe,z] using h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      rw [inner_add_right,inner_finite_hilbert_gaussian_quadratic]
      rfl

end ASDExplicitGamma.Scalar
