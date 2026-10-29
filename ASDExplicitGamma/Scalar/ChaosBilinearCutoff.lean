module

public import ASDExplicitGamma.Scalar.ChaosBilinearSeries

/-! The continuous bilinear cutoffs are the genuine finite Gaussian quadratic envelopes already bounded. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The Hermite centering is exactly the finite diagonal trace. -/
theorem finite_hilbert_gaussian_quadratic_raw {n : ℕ} (B : Fin n → Fin n → W)
    (x : EuclideanSpace ℝ (Fin n)) :
    finiteHilbertGaussianQuadratic B x=(∑ i,∑ j,(x i*x j) • B i j)-∑ i,B i i := by
  simp only [finiteHilbertGaussianQuadratic,sub_smul,ite_smul,one_smul,zero_smul,
    Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

/-- Finite Hilbert Gaussian series have the exact finite-vector coordinate presentation. -/
theorem gaussian_partial_sum_fin (v : ℕ → V) (n : ℕ) (omega : ℕ → ℝ) :
    Gaussian.gaussianPartialSum v n omega=∑ i : Fin n,omega i • v i := by
  unfold Gaussian.gaussianPartialSum
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => omega i • v i) n).symm

/-- No artificial moment premise is introduced when passing to actual continuous bilinear cutoffs. -/
theorem gaussian_bilinear_partial_eq_finite (B : V →L[ℝ] V →L[ℝ] W) (v : ℕ → V)
    (n : ℕ) (omega : ℕ → ℝ) :
    gaussianBilinearPartial B v n omega=
      finiteHilbertGaussianQuadratic (fun i j : Fin n => B (v i) (v j)) (gaussianFirstCoordinates n omega) := by
  rw [finite_hilbert_gaussian_quadratic_raw]
  unfold gaussianBilinearPartial
  rw [gaussian_partial_sum_fin]
  have ht : (∑ i ∈ Finset.range n,B (v i) (v i))=∑ i : Fin n,B (v i) (v i) :=
    (Fin.sum_univ_eq_sum_range (fun i : ℕ => B (v i) (v i)) n).symm
  rw [ht]
  simp only [map_sum,map_smul,sum_apply,smul_apply,
    Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  change omega j*omega i=omega i*omega j
  ring

/-- The source finite-cutoff norm envelope is exactly the pullback of the standard finite law. -/
theorem gaussian_bilinear_partial_envelope_eq (m : W) (B : V →L[ℝ] V →L[ℝ] W)
    (v : ℕ → V) (n : ℕ) :
    (fun omega => ‖m+gaussianBilinearPartial B v n omega‖^2)=
      (finiteHilbertGaussianEnvelope m (fun i j : Fin n => B (v i) (v j))) ∘ gaussianFirstCoordinates n := by
  funext omega
  rw [gaussian_bilinear_partial_eq_finite]
  rfl

end ASDExplicitGamma.Scalar
