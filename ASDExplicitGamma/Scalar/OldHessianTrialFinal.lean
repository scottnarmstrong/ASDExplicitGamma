module

public import ASDExplicitGamma.Scalar.OldHessianTrialUnitIsotropy
public import ASDExplicitGamma.Gaussian.ShellFrameClock

/-! The unit-direction OLD-Hessian generator bound, in `v_m`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- The frozen shell variance increment is the squared q3 model amplitude. -/
theorem old_hessian_shell_variance_increment (M : ABKModel 2) (h : ℝ) (m : ℤ) :
    shellVarianceSum h M.gamma (m+1)-shellVarianceSum h M.gamma m =
      (q3ModelAmplitude M h (m+1))^2 := by
  have hγ := M.shellPrefix.gamma_pos
  rw [q3ModelAmplitude_sq]
  unfold shellVarianceSum
  set u : ℝ := (3:ℝ)^(2*M.gamma) with hu
  have hu1 : 1<u := Real.one_lt_rpow (by norm_num) (by positivity)
  have hneg : (3:ℝ)^(-(2*M.gamma))=u⁻¹ := Real.rpow_neg (by norm_num) _
  have hx : (3:ℝ)^(2*M.gamma*(((m+1:ℤ):ℝ)))=(3:ℝ)^(2*M.gamma*(m:ℝ))*u := by
    rw [hu,← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    push_cast
    ring
  have hx' : (3:ℝ)^(2*M.gamma*(((m+1:ℤ):ℝ)))=(3:ℝ)^(2*M.gamma*(m:ℝ))*u := hx
  rw [hneg,hx']
  have hd : 1-u⁻¹≠0 := by
    have : u⁻¹<1 := inv_lt_one_of_one_lt₀ hu1
    linarith
  have hu0 : u≠0 := by linarith
  have hne : -1+u≠0 := by linarith
  field_simp
  have hinv := mul_inv_cancel₀ hne
  linear_combination h^2*hinv

/-- The ten-term OLD-Hessian generator bound for a unit direction `e`:
`E L_C F_e(a_m) ≤ -v_m * base` with `F_e(a) = e . D_{Q_{m+129}}(a/sigmaBar_m) e` and
`v_m = (B_{m+1}-B_m)/sigmaBar_m^2`. -/
theorem old_hessian_trial_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (e : Vec 2) (he : vecDot e e=1) :
    (1/2:ℝ)*modelHeatTraceAverage (closure (cubeSet (originCube 2 (m+129)))) M m
      (oldHessianUnitObservable (m+129) M.nu (Annealed.sigmaBar M m : ℝ) e)
      (pureFluxMainCubeQ3Directions (m+129) (q3ModelAmplitude M h (m+1)) (q3ModelLength (m+1))) 0 ≤
    -((shellVarianceSum h M.gamma (m+1)-shellVarianceSum h M.gamma m)/(Annealed.sigmaBar M m : ℝ)^2)*
      evalReal scalarRealEnv lowerBaseExpr := by
  have he' : e 0^2+e 1^2=1 := by
    simpa [vecDot,Fin.sum_univ_two,sq] using he
  rw [old_hessian_unit_generator_half_trace M h hM (m+129) m e he',
    old_hessian_shell_variance_increment]
  have ht := old_hessian_trial_ten_term_bound M h hM hg N hpast m hm
  rw [div_pow] at ht
  linarith [ht]

end
end ASDExplicitGamma.Scalar
