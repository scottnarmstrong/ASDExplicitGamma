module

public import ASDExplicitGamma.Native.ParentBoundaryCovarianceMeans
public import ASDExplicitGamma.Native.ParentBoundaryFeedback
public import ASDExplicitGamma.Native.OldSignedFlatRemovedEnergy

/-! The actual complete parent Dirichlet energy and signed inverse bulk. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- The own-native coefficient Y is the actual complete two-load parent
Dirichlet energy, rather than the fresh point variance. -/
def parentBoundaryDirichletEnergy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) : ℝ :=
  ∑' n,oldSignedFlatDirichletModeEnergy Q b L n

/-- The physical parent energy is exactly the trace of its complete Gram
matrix, including the actual source normalization. -/
theorem parent_boundary_dirichlet_energy_gram_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    parentBoundaryDirichletEnergy Q b L =
      ∑ i : Fin 2,parentBoundaryDirichletGram Q b L i i := by
  have hnorm (i : Fin 2) (n : whiteBasisIndex) :
      (∑ k : Fin 2,energy Q (fun x =>
        (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x k)) =
      (cubeVolume Q)⁻¹ * ‖parentBoundaryDirichletLoadOperator Q b L (basisVec i) (whiteBasis n)‖^2 := by
    rw [parent_boundary_dirichlet_load_basis]
    exact (old_signed_vector_energy_normalization Q
      (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad_memVectorL2).symm
  have hs := hasSum_sum (s := Finset.univ) (fun i _ =>
    (parent_boundary_dirichlet_load_trace_summable whiteBasis Q b L (basisVec i)).hasSum.mul_left
      ((cubeVolume Q)⁻¹))
  have hh : HasSum (oldSignedFlatDirichletModeEnergy Q b L)
      (∑ i : Fin 2,(cubeVolume Q)⁻¹ *
        ∑' n,‖parentBoundaryDirichletLoadOperator Q b L (basisVec i) (whiteBasis n)‖^2) := by
    apply hs.congr_fun
    intro n
    rw [old_signed_q3_parent_two_load_energy]
    exact Finset.sum_congr rfl (fun i _ => hnorm i n)
  simpa only [parentBoundaryDirichletEnergy,parentBoundaryDirichletGram,
    real_inner_self_eq_norm_sq] using hh.tsum_eq

/-- On the native square, scalarity identifies each diagonal with Y/2. -/
theorem parent_boundary_dirichlet_energy_scalar (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    parentBoundaryDirichletEnergy (originCube 2 m) b L =
      2*parentBoundaryDirichletGram (originCube 2 m) b L 0 0 := by
  rw [parent_boundary_dirichlet_energy_gram_trace,Fin.sum_univ_two,
    ←parent_boundary_dirichlet_gram_diagonal]
  ring

/-- Y is nonnegative and at most the actual fresh point variance. -/
theorem parent_boundary_dirichlet_energy_bounds (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    0≤parentBoundaryDirichletEnergy Q b L ∧ parentBoundaryDirichletEnergy Q b L≤b^2 := by
  have hy : 0≤parentBoundaryDirichletEnergy Q b L := tsum_nonneg
    (fun n => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => energy_nonneg Q _)))
  have hr := (old_signed_flat_minus_remainder_energy_bounds Q b L).1
  rw [(old_signed_flat_minus_complete_energy Q b L).2.2.tsum_eq] at hr
  exact ⟨hy,sub_nonneg.mp hr⟩

/-- The full deterministic minus covariance has exactly the own-native
mean -(Y/2)I. It is identified BEFORE bounding any covariance pairing. -/
theorem parent_boundary_minus_mean_energy (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    parentBoundaryFlatMean (originCube 2 m) b L false i k =
      -(parentBoundaryDirichletEnergy (originCube 2 m) b L/2)*
        (if k=i then 1 else 0) := by
  rw [parent_boundary_minus_mean_scalar,parent_boundary_dirichlet_energy_scalar]
  ring

/-- The deterministic parent mean contributes exactly the favorable signed
inverse term -Y*(tr D_Q-2), for every actual old coefficient realization. -/
theorem parent_boundary_signed_inverse_bulk (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : CoeffField 2) :
    (2*∑ i : Fin 2,∑ k : Fin 2,parentBoundaryFlatMean (originCube 2 m) b L false i k *
      ((coarseBlockMatrix (openCubeSet (originCube 2 m)) a).lowerRight k i-basisVec i k)) =
      -parentBoundaryDirichletEnergy (originCube 2 m) b L *
        (Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 m)) a).lowerRight-2) := by
  simp only [parent_boundary_minus_mean_energy,Fin.sum_univ_two,
    basisVec,Pi.single_apply,Matrix.trace,Matrix.diag]
  norm_num
  ring

end
end ASDExplicitGamma.Native
