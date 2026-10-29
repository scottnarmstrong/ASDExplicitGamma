module

public import ASDExplicitGamma.Triadic.DiagInterpolant

/-! Continuity, face values and mesh nodal values of the concrete DIAG operator. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

local instance diagGeometryFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem diagPhysicalHat_continuous (c : Vec 2) (r : ℝ) : Continuous (diagPhysicalHat c r) := by
  unfold diagPhysicalHat tensorMultiplier
  exact continuous_finsetProd _ fun i _ => diagHat_continuous.comp (by fun_prop)

theorem diagInterpolant_continuous (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) : Continuous (diagInterpolant Q j v).toFun := by
  have heq : (diagInterpolant Q j v).toFun = fun x =>
      (∑ i, diagMeanGradientLinear Q v i * x i) +
      ∑ z, diagNodalValuesLinear Q j v z *
        diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x :=
    funext (diagInterpolant_toFun Q j v)
  rw [heq]
  apply Continuous.add (by fun_prop)
  exact continuous_finsetSum _ fun z _ => continuous_const.mul (diagPhysicalHat_continuous _ _)

theorem diagPhysicalHat_face_zero (Q : TriadicCube 2) (c : Vec 2) {r : ℝ} (hr : 0 < r)
    (hc : ∀ i, cubeCorner Q i ≤ c i - r ∧ c i + r ≤ cubeCorner Q i + cubeScaleFactor Q)
    (x : Vec 2) (i : Fin 2)
    (hx : x i = cubeCorner Q i ∨ x i = cubeCorner Q i + cubeScaleFactor Q) :
    diagPhysicalHat c r x = 0 := by
  unfold diagPhysicalHat tensorMultiplier
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply diagHat_eq_zero
  rw [abs_div, abs_of_pos hr]
  apply (le_div_iff₀ hr).2
  rw [one_mul]
  rcases hx with hx | hx
  · have := (hc i).1
    have h := neg_le_abs (x i - c i)
    linarith only [this, h, hx]
  · have := (hc i).2
    have h := le_abs_self (x i - c i)
    linarith only [this, h, hx]

/-- The interpolant equals its affine part on every whole parent face. -/
theorem diagInterpolant_face (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (x : Vec 2) (i : Fin 2)
    (hx : x i = cubeCorner Q i ∨ x i = cubeCorner Q i + cubeScaleFactor Q) :
    (diagInterpolant Q j v).toFun x = ∑ k, diagMeanGradientLinear Q v k * x k := by
  rw [diagInterpolant_toFun]
  have hz : (∑ z, diagNodalValuesLinear Q j v z *
      diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x) = 0 := by
    apply Finset.sum_eq_zero
    intro z _
    rw [diagPhysicalHat_face_zero Q _ (diagMeshRadius_pos Q j)
      (diagInteriorVertex_support Q j z) x i hx, mul_zero]
  rw [hz, add_zero]

/-- On affine data the boundary value is precisely the source load `p·x`. -/
theorem diagInterpolant_affine_face (Q : TriadicCube 2) (j : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) (x : Vec 2) (i : Fin 2)
    (hx : x i = cubeCorner Q i ∨ x i = cubeCorner Q i + cubeScaleFactor Q) :
    (diagInterpolant Q j (ASDExplicitGamma.Variational.lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun x = ∑ k, p k * x k := by
  rw [diagInterpolant_face Q j _ x i hx, diagMeanGradient_affinePotential]

/-- Distinct integer vertices are separated by at least one hat radius. -/
theorem diagHat_int (k : ℤ) : diagHat (k : ℝ) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst k
    simpa only [Int.cast_zero] using diagHat_zero
  · apply diagHat_eq_zero
    exact_mod_cast Int.one_le_abs hk

/-- Cardinal property of the tensor hat basis at all interior vertices. -/
theorem diagPhysicalHat_at_vertex (Q : TriadicCube 2) (j : ℕ)
    (z w : Fin 2 → Fin (3 ^ j - 1)) :
    diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j)
      (diagInteriorVertex Q j w) = if z = w then 1 else 0 := by
  classical
  have heq (i : Fin 2) :
      (diagInteriorVertex Q j w i - diagInteriorVertex Q j z i) / diagMeshRadius Q j =
        (((w i).val : ℤ) - (z i).val : ℤ) := by
    unfold diagInteriorVertex
    push_cast
    field_simp [(diagMeshRadius_pos Q j).ne']
    ring
  unfold diagPhysicalHat tensorMultiplier
  simp only [heq, diagHat_int]
  by_cases hzw : z = w
  · subst w
    simp
  · rw [ite_eq_right hzw]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hzw
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hv : ((w i).val : ℤ) - (z i).val ≠ 0 := by
      intro h
      apply hi
      apply Fin.ext
      omega
    rw [ite_eq_right hv]

/-- At each interior mesh vertex the value is its affine part plus the
average of the four neighboring cell means of the affine residual. -/
theorem diagInterpolant_at_vertex (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (w : Fin 2 → Fin (3 ^ j - 1)) :
    (diagInterpolant Q j v).toFun (diagInteriorVertex Q j w) =
      (∑ i, diagMeanGradientLinear Q v i * diagInteriorVertex Q j w i) +
        diagOddNodalMean (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j)
          (cubeProjection Q j (diagResidualLinear Q v).toFun) (diagInteriorVertexIndex j w) := by
  classical
  rw [diagInterpolant_toFun]
  simp only [diagPhysicalHat_at_vertex]
  rw [Finset.sum_eq_single w]
  · simp only [ite_true, mul_one]
    congr 1
    change diagOddNodalMean _ _ _ (diagProjectionLinear Q j (diagResidualLinear Q v)) _ = _
    congr 1
    funext x
    exact diagProjectionLinear_apply Q j _ x
  · intro z _ hzw
    rw [ite_eq_right hzw, mul_zero]
  · intro hw
    exact (hw (Finset.mem_univ w)).elim

end

end ASDExplicitGamma.Triadic
