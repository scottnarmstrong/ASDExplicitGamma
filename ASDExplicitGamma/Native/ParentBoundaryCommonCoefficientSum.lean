module

public import ASDExplicitGamma.Native.ParentBoundaryCommonSpatialClock

/-! Exact normalized finite-shell coefficient sum, with no shell population loss. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Algsuperdiff.Section3
noncomputable section

/-- The actual finite physical shell sum separates into the squared
normalized A-column and B-column covariance norms. All frame factors are
kept exactly, before inserting native shell clock bounds. -/
theorem parent_boundary_common_shell_coefficient_sum
    (M : ABKModel 2) (h : ℝ) (P Q : TriadicCube 2) (n : ℤ) (height : ℕ) :
    (∑ i : Fin height,parentBoundaryCommonShellCoefficient M h P Q n height i)=
      ((Annealed.sigmaBar M n:ℝ)/(Annealed.sigmaBar M Q.scale:ℝ))^2*
        ((232/125:ℝ)*(∑ i : Fin height,(parentBoundaryCommonRowCoefficient P Q
          (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
          (q3ModelLength (n+((i.val+1:ℕ):ℤ))) 0)^2)+
          38*(∑ i : Fin height,((q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))*
            lemmaVH2Bn (cubeScaleFactor P/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)
              (diagMeshRadius Q 0/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val))^2)) := by
  let sigma : ℝ := Annealed.sigmaBar M n
  let R := sigma/(Annealed.sigmaBar M Q.scale:ℝ)
  let A := fun i : Fin height => parentBoundaryCommonRowCoefficient P Q
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/sigma) (q3ModelLength (n+((i.val+1:ℕ):ℤ))) 0
  let B := fun i : Fin height => (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/sigma)*
    lemmaVH2Bn (cubeScaleFactor P/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)
      (diagMeshRadius Q 0/(q3ModelLength (n+((i.val+1:ℕ):ℤ))).val)
  have hsigma : 0 < sigma := (Annealed.sigmaBar_characterization M n).1
  have he (i : Fin height) : parentBoundaryCommonShellCoefficient M h P Q n height i=
      R^2*((232/125:ℝ)*A i^2+38*B i^2) := by
    dsimp only [parentBoundaryCommonShellCoefficient,A,B,R]
    rw [parent_boundary_common_row_coefficient_div P Q _ sigma hsigma]
    dsimp only [sigma]
    field_simp
  simp_rw [he]
  rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]

/-- The complete B-column finite shell norm has the exact lower source
trace constants, with no factor depending on the number of shells. -/
theorem parent_boundary_common_band_bracket_norm_bound
    {I : Type*} [Fintype I] (P Q : TriadicCube 2) (b : I → ℝ) (L : I → {l : ℝ // 0 < l}) :
    Real.sqrt (∑ i,(|b i| *lemmaVH2Bn (cubeScaleFactor P/(L i).val) (diagMeshRadius Q 0/(L i).val))^2) ≤
      (Real.sqrt (39/5:ℝ)+(36/25:ℝ)*Real.sqrt (78/5:ℝ)*(cubeScaleFactor Q/cubeScaleFactor P))*
        Real.sqrt (∑ i,(b i)^2*(cubeScaleFactor P/(L i).val)^2)+
      ((57/200:ℝ)*Real.sqrt (23244/25:ℝ)*(cubeScaleFactor Q/cubeScaleFactor P)^2)*
        Real.sqrt (∑ i,(b i)^2*(cubeScaleFactor P/(L i).val)^4) := by
  let z := cubeScaleFactor Q/cubeScaleFactor P
  let E := fun i => (b i)^2*(cubeScaleFactor P/(L i).val)^2
  let F := fun i => (b i)^2*(cubeScaleFactor P/(L i).val)^4
  have hP : 0 < cubeScaleFactor P := zpow_pos (by norm_num : (0:ℝ)<3) _
  have hQ : 0 < cubeScaleFactor Q := zpow_pos (by norm_num : (0:ℝ)<3) _
  have hz : 0 ≤ z := div_nonneg hQ.le hP.le
  apply old_signed_finite_sqrt_energy_bound E F _ (by positivity) (by positivity)
    (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (fun _ => mul_nonneg (sq_nonneg _) (pow_nonneg (div_nonneg hP.le (L _).property.le) _))
  · intro i
    have hr := div_nonneg hP.le (L i).property.le
    have hm := div_nonneg (diagMeshRadius_pos Q 0).le (L i).property.le
    dsimp only [lemmaVH2Bn,lemmaVH2R1,lemmaVH2A2,lemmaVH2C1,lemmaVH2C2]
    positivity
  · intro i
    have hr : 0 ≤ cubeScaleFactor P/(L i).val := div_nonneg hP.le (L i).property.le
    have hE : Real.sqrt (E i)=|b i| *(cubeScaleFactor P/(L i).val) := by
      dsimp only [E]
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,Real.sqrt_sq hr]
    have hF : Real.sqrt (F i)=|b i| *(cubeScaleFactor P/(L i).val)^2 := by
      dsimp only [F]
      rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
        show (cubeScaleFactor P/(L i).val)^4=((cubeScaleFactor P/(L i).val)^2)^2 by ring,
        Real.sqrt_sq (sq_nonneg _)]
    have hmesh : cubeScaleFactor Q/(L i).val=z*(cubeScaleFactor P/(L i).val) := by
      dsimp only [z]
      field_simp [hP.ne']
    rw [parent_boundary_common_bracket_coefficient_shape,hE,hF,hmesh]
    exact le_of_eq (by ring)

end
end ASDExplicitGamma.Native
