module

public import ASDExplicitGamma.Native.OldSignedProjectedKernelBounds

/-! The complete whole-plane solenoidal kernel is the complementary
Helmholtz multiplier on the actual physical q3 white realization. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- The actual complementary whole-plane kernel, with no new realization. -/
def oldSignedComplementaryWhiteKernel (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) : WhiteNoise :=
  (if i=j then q3Section b L h3Zero (L.1 • x) else 0)-
    oldSignedProjectedWhiteKernel b L x i j

/-- The complementary physical kernel is continuous in space. -/
theorem old_signed_complementary_white_continuous (b : ℝ) (L : {l : ℝ // 0 < l}) (i j : Fin 2) :
    Continuous (fun x => oldSignedComplementaryWhiteKernel b L x i j) := by
  unfold oldSignedComplementaryWhiteKernel
  split_ifs
  · exact ((q3Section_continuous b L h3Zero).comp
      (continuous_id.const_smul L.1)).sub (old_signed_projected_white_continuous b L i j)
  · exact continuous_const.sub (old_signed_projected_white_continuous b L i j)

/-- Each actual complementary kernel has a uniform finite amplitude bound. -/
theorem old_signed_complementary_white_norm_le (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) : ‖oldSignedComplementaryWhiteKernel b L x i j‖≤2*|b| := by
  have ha : ‖q3Section b L h3Zero (L.1 • x)‖≤|b| := by
    apply (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
    rw [old_signed_raw_white_norm_sq,sq_abs]
  have hh : ‖(if i=j then q3Section b L h3Zero (L.1 • x) else 0)‖≤|b| := by
    split_ifs
    · exact ha
    · simpa only [norm_zero] using abs_nonneg b
  exact (norm_sub_le _ _).trans ((add_le_add hh (old_signed_projected_white_norm_le b L x i j)).trans_eq (by ring))

/-- Both complementary loads together have exactly one shell variance of
white covariance energy. The source/projection cross term is contracted first. -/
theorem old_signed_complementary_white_total_energy (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) : (∑ i : Fin 2,∑ j : Fin 2,‖oldSignedComplementaryWhiteKernel b L x i j‖^2)=b^2 := by
  have ht := old_signed_projected_white_total_energy b L x
  simp only [Fin.sum_univ_two] at ht ⊢
  norm_num [oldSignedComplementaryWhiteKernel]
  rw [norm_sub_sq_real,norm_sub_sq_real,old_signed_raw_white_norm_sq,
    old_signed_projected_white_point_covariance,old_signed_projected_white_point_covariance]
  norm_num
  linarith only [ht]

end
end ASDExplicitGamma.Native
