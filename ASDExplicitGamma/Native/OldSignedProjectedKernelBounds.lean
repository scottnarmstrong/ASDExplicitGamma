module

public import ASDExplicitGamma.Native.OldSignedProjectedEnergy
public import ASDExplicitGamma.Native.OldSignedPhysicalPotential

/-! Pointwise norm bounds and continuity for the actual physical kernels,
used as domination in complete covariance sums. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
noncomputable section

/-- The projected physical kernel is continuous in the dimensionless spatial
coordinate under the actual spectral-to-white map. -/
theorem old_signed_projected_white_continuous (b : ℝ) (L : {l : ℝ // 0 < l}) (i j : Fin 2) :
    Continuous (fun x => oldSignedProjectedWhiteKernel b L x i j) :=
  (oldSignedPotentialWhiteMap b L).continuous.comp (old_signed_projected_character_continuous b i j)

/-- Every matrix entry of the actual physical projected kernel is bounded
by the shell amplitude, uniformly in space and shell length. -/
theorem old_signed_projected_white_norm_le (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) : ‖oldSignedProjectedWhiteKernel b L x i j‖ ≤ |b| := by
  have ht := old_signed_projected_white_total_energy b L x
  have hle : ‖oldSignedProjectedWhiteKernel b L x i j‖^2 ≤ b^2 := by
    rw [←ht]
    calc
      _ ≤ ∑ k : Fin 2,‖oldSignedProjectedWhiteKernel b L x i k‖^2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum
        (f := fun k : Fin 2 => ∑ a : Fin 2,‖oldSignedProjectedWhiteKernel b L x k a‖^2)
        (fun k _ => Finset.sum_nonneg (fun a _ => sq_nonneg _)) (Finset.mem_univ i)
  nlinarith only [hle,sq_abs b,norm_nonneg (oldSignedProjectedWhiteKernel b L x i j),abs_nonneg b]

/-- The signed two-quarter-turn kernel remains continuous. -/
theorem old_signed_rotated_white_continuous (b : ℝ) (L : {l : ℝ // 0 < l}) (i j : Fin 2) :
    Continuous (fun x => oldSignedRotatedWhiteKernel b L x i j) := by
  change Continuous (fun x => ∑ a : Fin 2,∑ c : Fin 2,
    (responsePlanarJ i a*responsePlanarJ c j) • oldSignedProjectedWhiteKernel b L x a c)
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro c _
  exact (old_signed_projected_white_continuous b L a c).const_smul (responsePlanarJ i a*responsePlanarJ c j)

/-- The two source quarter turns preserve the entrywise amplitude bound. -/
theorem old_signed_rotated_white_norm_le (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) : ‖oldSignedRotatedWhiteKernel b L x i j‖ ≤ |b| := by
  fin_cases i <;> fin_cases j
  · simpa [oldSignedRotatedWhiteKernel,responsePlanarJ,Fin.sum_univ_two] using
      old_signed_projected_white_norm_le b L x 1 1
  · simpa [oldSignedRotatedWhiteKernel,responsePlanarJ,Fin.sum_univ_two] using
      old_signed_projected_white_norm_le b L x 1 0
  · simpa [oldSignedRotatedWhiteKernel,responsePlanarJ,Fin.sum_univ_two] using
      old_signed_projected_white_norm_le b L x 0 1
  · simpa [oldSignedRotatedWhiteKernel,responsePlanarJ,Fin.sum_univ_two] using
      old_signed_projected_white_norm_le b L x 0 0

/-- The actual unprojected white section has exactly its shell variance. -/
theorem old_signed_raw_white_norm_sq (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    ‖q3Section b L h3Zero x‖^2=b^2 := by
  rw [←real_inner_self_eq_norm_sq,q3Section_covariance]
  simp only [sub_self,zero_div,q3Cov_zero_eq_one,mul_one]

end
end ASDExplicitGamma.Native
