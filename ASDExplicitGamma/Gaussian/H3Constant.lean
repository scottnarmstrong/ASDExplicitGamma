module

public import ASDExplicitGamma.Gaussian.H3Space
public import ASDExplicitGamma.Gaussian.HilbertKernel

/-! # Constant fields in ordinary weak H³ -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable (U : Set (Vec 2)) [IsFiniteMeasure (volume.restrict U)]

/-- The constant field has only its zeroth L² coordinate. -/
noncomputable def h3ConstantJet : ℝ →L[ℝ] H3Jet U :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : H3Index => Lp ℝ 2 (volume.restrict U))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a => by
      classical
      exact if a = h3Zero then Lp.constL 2 (volume.restrict U) ℝ else 0)

theorem h3ConstantJet_ae (v : ℝ) (a : H3Index) :
    h3ConstantJet U v a =ᵐ[volume.restrict U] fun _ => if a = h3Zero then v else 0 := by
  classical
  have he : h3ConstantJet U v a =
      if a = h3Zero then Lp.const 2 (volume.restrict U) v else 0 := by
    change (if a = h3Zero then Lp.constL 2 (volume.restrict U) ℝ else 0) v = _
    split_ifs <;> rfl
  rw [he]
  split_ifs
  · exact Lp.coeFn_const 2 (volume.restrict U) v
  · exact Lp.coeFn_zero ℝ 2 (volume.restrict U)

/-- Constants have zero weak derivatives on every source domain of finite volume. -/
theorem h3ConstantJet_mem (v : ℝ) : h3ConstantJet U v ∈ h3Space U := by
  classical
  rw [mem_h3Space_iff]
  intro a i ha φ hφ hcomp hsupp
  have hn : h3Next a i ha ≠ h3Zero := by
    intro he
    have he' := congrArg (fun j : H3Index => j.1.1.val + j.1.2.val) he
    simp only [h3Next, h3Zero] at he'
    split_ifs at he' <;> dsimp at he' <;> omega
  have hh := HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
    (f := fun _ : Vec 2 => if a = h3Zero then v else 0) contDiff_const φ hφ hcomp hsupp
  simp only [fderiv_const_apply, zero_apply, zero_mul, integral_zero, neg_zero] at hh
  change (∫ x in U, h3ConstantJet U v a x * fderiv ℝ φ x (basisVec i)) =
    -(∫ x in U, h3ConstantJet U v (h3Next a i ha) x * φ x)
  rw [show (∫ x in U, h3ConstantJet U v a x * fderiv ℝ φ x (basisVec i)) = 0 from by
    calc
      _ = ∫ x in U, (if a = h3Zero then v else 0) * fderiv ℝ φ x (basisVec i) := by
        apply integral_congr_ae
        filter_upwards [h3ConstantJet_ae U v a] with x hx
        rw [hx]
      _ = 0 := hh]
  have he : (∫ x in U, h3ConstantJet U v (h3Next a i ha) x * φ x) = 0 := by
    calc
      _ = ∫ _x in U, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [h3ConstantJet_ae U v (h3Next a i ha)] with x hx
        simp only [hn, ite_eq_right, not_false_eq_true] at hx
        rw [hx, zero_mul]
      _ = 0 := by simp only [integral_zero]
  rw [he, neg_zero]

noncomputable def h3Constant : ℝ →L[ℝ] h3Space U :=
  (h3ConstantJet U).codRestrict (h3Space U) (h3ConstantJet_mem U)

end
end ASDExplicitGamma.Gaussian
