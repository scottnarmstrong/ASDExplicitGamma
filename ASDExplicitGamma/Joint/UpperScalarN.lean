module

public import ASDExplicitGamma.Joint.UpperScalarCoordinate
public import ASDExplicitGamma.Scalar.UpperLongblockTrial

/-! JO-UPPER-SCALAR-N: the fixed-target upper scalar coordinate with the
long-block trial supplied from the accepted scalar cell-energy chain. -/
@[expose] public section
namespace ASDExplicitGamma.Joint
open Homogenization Algsuperdiff.Section3
noncomputable section

/-- The source-expression long-block conclusion required by the joint helper,
proved from strict-past states and the actual physical error certificate. -/
theorem native_longblock_trial_conclusion
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k<N, nativeInductionState M h k) :
    NativeLongBlockTrialConclusion M h N := by
  let n : ℤ := N-⌊(17/50:ℝ)/M.gamma⌋
  have hL : 0 < ⌊(17/50:ℝ)/M.gamma⌋ := by
    have hh := Scalar.upper_cell_source_height_pos M hg
    omega
  have hn : n<N := by dsimp only [n]; omega
  have ht := Scalar.scalar_upper_longblock_trial M h hM hg N hpast n hn
  have he := (Scalar.upper_cell_physical_error_certificate M hg).1
  have hc := ht.2.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) he)
    (Annealed.sigmaBar M n).property.le)
  have hcast : (⌊(17/50:ℝ)/M.gamma⌋.toNat:ℤ) = ⌊(17/50:ℝ)/M.gamma⌋ :=
    Int.toNat_of_nonneg hL.le
  unfold NativeLongBlockTrialConclusion
  simpa only [n,hcast,sub_add_cancel] using hc

/-- Component eight at one target N, with all source and long-block estimates
proved internally from the standing model and completed states k<N. -/
theorem upper_scalar_n
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k<N, nativeInductionState M h k) :
    (Annealed.sigmaBar M N:ℝ)^2 ≤ M.nu^2+(13/8:ℝ)*shellVarianceSum h M.gamma N :=
  upper_scalar_n_of_longblock_trial M h hM hg N hpast
    (native_longblock_trial_conclusion M h hM hg N hpast)

end
end ASDExplicitGamma.Joint
