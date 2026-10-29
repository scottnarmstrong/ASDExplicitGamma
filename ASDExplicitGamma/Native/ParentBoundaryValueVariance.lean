module

public import ASDExplicitGamma.Native.ParentBoundaryFullCovariance

/-! The exact centering gain in the physical full-minus covariance value
energy, retaining its complete same-noise Dirichlet kernel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- The complete full covariance field has precisely the previously proved
actual deterministic parent mean. -/
theorem parent_boundary_full_covariance_mean (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    (∫ x,parentBoundaryMinusFullCovariance Q b L i x k ∂normalizedCubeMeasure Q) =
      parentBoundaryFlatMean Q b L false i k := by
  rw [integral_congr_ae (parent_boundary_full_covariance_eq_bulk_remainder Q b L i k),
    integral_add (integrable_const _)
      ((old_signed_covariance_cell_membership Q Q (Set.Subset.refl _) b L false i k).1.integrable one_le_two),
    integral_const]
  simp only [Measure.real_def,normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul,
    parentBoundaryFlatMean]

/-- The old centered covariance is exactly the centered FULL physical
contraction, almost everywhere; the whole-plane bulk cancels literally. -/
theorem parent_boundary_centered_eq_full (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    (fun x => parentBoundaryCenteredCovariance Q b L false i x k) =ᵐ[normalizedCubeMeasure Q]
      fun x => parentBoundaryMinusFullCovariance Q b L i x k-parentBoundaryFlatMean Q b L false i k := by
  filter_upwards [parent_boundary_full_covariance_eq_bulk_remainder Q b L i k] with x hx
  rw [hx]
  unfold parentBoundaryCenteredCovariance parentBoundaryFlatMean
  ring

/-- Exact covariance value-energy decomposition after parent centering. -/
theorem parent_boundary_centered_coordinate_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i k : Fin 2) :
    energy Q (fun x => parentBoundaryCenteredCovariance Q b L false i x k) =
      energy Q (fun x => parentBoundaryMinusFullCovariance Q b L i x k) -
        (parentBoundaryFlatMean Q b L false i k)^2 := by
  have hF : MemLp (fun x => parentBoundaryMinusFullCovariance Q b L i x k) 2
      (normalizedCubeMeasure Q) := by
    rw [←parent_boundary_full_covariance_h1_toFun]
    exact (parentBoundaryMinusFullCovarianceH1 Q b L i k).memL2_normalizedCubeMeasure
  have he : energy Q (fun x => parentBoundaryCenteredCovariance Q b L false i x k) =
      energy Q (fun x => parentBoundaryMinusFullCovariance Q b L i x k-
        parentBoundaryFlatMean Q b L false i k) := by
    rw [energy_eq_integral_sq,energy_eq_integral_sq]
    apply integral_congr_ae
    filter_upwards [parent_boundary_centered_eq_full Q b L i k] with x hx
    rw [hx]
  rw [he,energy_sub Q hF (memLp_const _),pairing_const_right,energy_const,
    cubeAverage_eq_integral_normalizedCubeMeasure,parent_boundary_full_covariance_mean]
  ring

/-- Pointwise Cauchy-Schwarz controls the same actual full covariance
coordinate by its complete physical white kernel energy. -/
theorem parent_boundary_minus_scalar_value_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (a : Fin 2 × Fin 2) :
    energy Q (parentBoundaryMinusCovarianceH1 Q b L a).toFun ≤
      b^2*hilbertEnergy Q (parentBoundaryMinusKernel Q b L a).toFun := by
  rw [energy_eq_integral_sq,hilbertEnergy,←integral_const_mul]
  apply integral_mono_ae (parentBoundaryMinusCovarianceH1 Q b L a).memL2_normalizedCubeMeasure.integrable_sq
    (((parentBoundaryMinusKernel Q b L a).memL2_normalized Q).integrable_norm_pow (by norm_num) |>.const_mul _)
  filter_upwards with x
  have hh := (sq_le_sq₀ (abs_nonneg (inner ℝ (q3Section b L h3Zero x)
    ((parentBoundaryMinusKernel Q b L a).toFun x)))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (abs_real_inner_le_norm _ _)
  simp only [sq_abs,mul_pow,old_signed_raw_white_norm_sq] at hh
  exact hh

/-- Rotating the output changes neither the complete coordinate value
energy nor the physical complete-mode normalization. -/
theorem parent_boundary_minus_full_value_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => parentBoundaryMinusFullCovariance Q b L i x k)) ≤
      b^2*parentBoundaryDirichletEnergy Q b L := by
  have hrot (i : Fin 2) : (∑ k : Fin 2,energy Q (fun x => parentBoundaryMinusFullCovariance Q b L i x k))=
      ∑ k : Fin 2,energy Q (parentBoundaryMinusCovarianceH1 Q b L (i,k)).toFun := by
    simp [Fin.sum_univ_two,parentBoundaryMinusFullCovariance,planarQuarterTurn,energy_neg,add_comm]
  simp_rw [hrot]
  rw [←parent_boundary_minus_kernel_energy,Finset.mul_sum,Fintype.sum_prod_type]
  exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun k _ =>
    parent_boundary_minus_scalar_value_energy Q b L (i,k)))

/-- The source signed value variance b²Y-Y²/2 is proved for the SAME
actual centered covariance field on the native parent square. -/
theorem parent_boundary_centered_value_variance (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    (∑ i : Fin 2,∑ k : Fin 2,energy (originCube 2 m)
      (fun x => parentBoundaryCenteredCovariance (originCube 2 m) b L false i x k)) ≤
      b^2*parentBoundaryDirichletEnergy (originCube 2 m) b L -
        (parentBoundaryDirichletEnergy (originCube 2 m) b L)^2/2 := by
  simp_rw [parent_boundary_centered_coordinate_energy,Finset.sum_sub_distrib]
  have hm : (∑ i : Fin 2,∑ k : Fin 2,(parentBoundaryFlatMean (originCube 2 m) b L false i k)^2)=
      (parentBoundaryDirichletEnergy (originCube 2 m) b L)^2/2 := by
    simp [parent_boundary_minus_mean_energy]
    ring
  rw [hm]
  exact sub_le_sub_right (parent_boundary_minus_full_value_energy (originCube 2 m) b L) _

end
end ASDExplicitGamma.Native
