module

public import ASDExplicitGamma.Model.ShellScaling
public import Algsuperdiff.Section3.Cutoff.Scaling
public import Mathlib.Probability.Independence.InfinitePi

/-! The exact scale-shift action on the genuine bi-infinite shell sequence. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

/-- The genuine shell scaling actions form an integer group action. -/
theorem shell_triadic_scale_add {d : ℕ} (γ : ℝ) (m n : ℤ) (j : ShellField d) :
    ShellField.triadicScale γ m (ShellField.triadicScale γ n j)=ShellField.triadicScale γ (m+n) j := by
  apply ShellField.ext
  intro x
  simp only [ShellField.triadicScale_apply,smul_smul]
  have hp : Real.rpow 3 (γ*(m:ℝ))*Real.rpow 3 (γ*(n:ℝ))=Real.rpow 3 (γ*((m+n:ℤ):ℝ)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    push_cast
    ring
  have hx : ((3:ℝ)^n)⁻¹ * ((3:ℝ)^m)⁻¹=((3:ℝ)^(m+n))⁻¹ := by
    rw [zpow_add₀ (by norm_num : (3:ℝ)≠0),mul_inv_rev]
  rw [hp,hx]

/-- Moving the cutoff by m and restoring the unit shell law. -/
noncomputable def shellScaleShift {d : ℕ} (γ : ℝ) (m : ℤ) (ω : ℤ → ShellField d) : ℤ → ShellField d :=
  fun k => ShellField.triadicScale γ (-m) (ω (k+m))

/-- The exact scale shift is measurable on the honest shell-sequence carrier. -/
theorem measurable_shell_scale_shift {d : ℕ} (γ : ℝ) (m : ℤ) :
    Measurable (shellScaleShift (d:=d) γ m) := by
  apply Measurable.of_eval
  intro k
  exact (ShellField.measurable_triadicScale γ (-m)).comp (measurable_pi_apply (k+m))

/-- The scale shift preserves every genuine lower-tail-good realization. -/
theorem shell_scale_shift_lower_tail_good {d : ℕ} (γ : ℝ) (m : ℤ)
    (ω : Cutoff.CutoffSample d) : Cutoff.LowerTailGood (shellScaleShift γ m ω.1) := by
  intro ell k
  have hs := (Cutoff.lowerTailGood_summable ω.2 (ell+m) (k+m)).mul_left
    (Real.rpow 3 (γ*((-m:ℤ):ℝ)))
  have he : (fun r : ℕ => Cutoff.localCubeControl ell (shellScaleShift γ m ω.1 (k-(r:ℤ))))=
      (fun r : ℕ => Real.rpow 3 (γ*((-m:ℤ):ℝ))*Cutoff.localCubeControl (ell+m) (ω.1 (k+m-(r:ℤ)))) := by
    funext r
    unfold shellScaleShift
    rw [Cutoff.localCubeControl_triadicScale]
    simp only [sub_neg_eq_add]
    rw [show k-(r:ℤ)+m=k+m-(r:ℤ) by omega]
  rw [← he] at hs
  obtain ⟨N,hN⟩ := exists_nat_ge (∑' r : ℕ,Cutoff.localCubeControl ell (shellScaleShift γ m ω.1 (k-(r:ℤ))))
  refine ⟨N,fun q => ?_⟩
  exact (hs.sum_le_tsum (Finset.range q) (fun r _ => Cutoff.localCubeControl_nonneg ell _)).trans hN

end ASDExplicitGamma.Scalar
