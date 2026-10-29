module

public import ASDExplicitGamma.Native.ParentRowWeightedFields
public import ASDExplicitGamma.Native.ParentRowMeanSlopeExpr

/-! Exact mesh moments for every shell of the simultaneous parent band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The fine mesh has its exact ratio to each physical shell length. -/
theorem parent_row_mesh_length_ratio (n : ℤ) (k : ℕ) :
    (cubeScaleFactor (originCube 2 n)/3^5)/(q3ModelLength (n+((k+1:ℕ):ℤ))).val=
      (1/3:ℝ)^(k+6) := by
  have hh := parent_boundary_model_length_ratio n (k+1)
  calc
    _ = (cubeScaleFactor (originCube 2 n)/(q3ModelLength (n+((k+1:ℕ):ℤ))).val)/3^5 := by ring
    _ = (1/3:ℝ)^(k+1)/3^5 := by rw [hh]
    _ = (1/3:ℝ)^(k+1)*(1/3:ℝ)^5 := by norm_num; ring
    _ = _ := by rw [←pow_add]

/-- Every even physical mesh moment retains its exact shell weight. -/
theorem parent_row_mesh_even_moment (n : ℤ) (k p : ℕ) (b : ℝ) :
    (cubeScaleFactor (originCube 2 n)/3^5)^(2*p)*b^2/
      (q3ModelLength (n+((k+1:ℕ):ℤ))).val^(2*p)=
      b^2*(1/9:ℝ)^(p*(k+6)) := by
  calc
    _ = ((cubeScaleFactor (originCube 2 n)/3^5)/
      (q3ModelLength (n+((k+1:ℕ):ℤ))).val)^(2*p)*b^2 := by
        have hx (x y z : ℝ) (m : ℕ) : x^m*z^2/y^m=(x/y)^m*z^2 := by
          rw [div_pow]
          ring
        exact hx _ _ _ _
    _ = _ := by
      rw [parent_row_mesh_length_ratio,←pow_mul,
        show (k+6)*(2*p)=2*(p*(k+6)) by ring,pow_mul]
      norm_num
      ring

/-- The actual finite band mesh moment, with all shells in their true frame. -/
def parentRowMeshMoment (M : ABKModel 2) (h : ℝ) (n : ℤ) (height p : ℕ) : ℝ :=
  ∑ i : Fin height,(cubeScaleFactor (originCube 2 n)/3^5)^(2*p)*
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))^2/
      (q3ModelLength (n+((i.val+1:ℕ):ℤ))).val^(2*p)

/-- The exact weighted source clock bounds the complete physical mesh moment,
retaining theta for arbitrary even order. -/
theorem parent_row_mesh_moment_bound
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (height p : ℕ) :
    parentRowMeshMoment M h n height p≤
      theta M*parentRowWeightedClock (fun k => (1/9)^(p*(k+6))) height := by
  unfold parentRowMeshMoment
  simp_rw [parent_row_mesh_even_moment]
  have hh := parent_row_weighted_actual_variance M h hg n height hstate
    (fun k => (1/9)^(p*(k+6))) (fun _ => by positivity)
  simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh

/-- The complete physical second mesh moment fits the stored A2 coefficient. -/
theorem parent_row_mesh_second_bound
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) :
    parentRowMeshMoment M h n (j.val+1) 1≤theta M*(parentRowFields j).getD 1 0 := by
  rw [parent_row_a2_eq]
  change _≤theta M*parentRowWeightedClock (fun k => (1/9)^(k+6)) (j.val+1)
  simpa only [Nat.one_mul] using
    parent_row_mesh_moment_bound M h hg n hstate (j.val+1) 1

end
end ASDExplicitGamma.Native
