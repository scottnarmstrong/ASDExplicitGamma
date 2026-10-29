module

public import ASDExplicitGamma.Triadic.DiagNodes

/-! DIAG's cell-mean nodal interpolant as a linear map on the actual H¹ carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

local instance diagParentFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Side of one depth-`j` cell. -/
def diagMeshRadius (Q : TriadicCube 2) (j : ℕ) : ℝ := cubeScaleFactor Q / (3 : ℝ) ^ j

theorem diagMeshRadius_pos (Q : TriadicCube 2) (j : ℕ) : 0 < diagMeshRadius Q j :=
  div_pos (cubeScaleFactor_pos' Q) (pow_pos (by norm_num) j)

/-- Interior mesh vertices, numbered from one in each coordinate. -/
def diagInteriorVertex (Q : TriadicCube 2) (j : ℕ)
    (z : Fin 2 → Fin (3 ^ j - 1)) : Vec 2 :=
  fun i => cubeCorner Q i + ((z i).val + 1) * diagMeshRadius Q j

/-- Embedding the interior vertices in the full vertex grid. -/
def diagInteriorVertexIndex (j : ℕ) (z : Fin 2 → Fin (3 ^ j - 1)) :
    Fin 2 → Fin (3 ^ j + 1) :=
  fun i => ⟨(z i).val + 1, by have := (z i).isLt; omega⟩

theorem diagInteriorVertex_support (Q : TriadicCube 2) (j : ℕ)
    (z : Fin 2 → Fin (3 ^ j - 1)) (i : Fin 2) :
    cubeCorner Q i ≤ diagInteriorVertex Q j z i - diagMeshRadius Q j ∧
      diagInteriorVertex Q j z i + diagMeshRadius Q j ≤
        cubeCorner Q i + cubeScaleFactor Q := by
  have hr := diagMeshRadius_pos Q j
  have hz : (z i).val + 2 ≤ 3 ^ j := by have := (z i).isLt; omega
  have hz' : ((z i).val : ℝ) + 2 ≤ (3 : ℝ) ^ j := by exact_mod_cast hz
  have hside : (3 : ℝ) ^ j * diagMeshRadius Q j = cubeScaleFactor Q := by
    unfold diagMeshRadius
    field_simp
  unfold diagInteriorVertex
  constructor
  · nlinarith only [hr, Nat.cast_nonneg (α := ℝ) (z i).val]
  · nlinarith only [hz', hr, hside]

/-- Synthesis from the fixed, genuine H¹ tensor-hat basis. -/
def diagSynthesisH1Linear (Q : TriadicCube 2) (j : ℕ) :
    ((Fin 2 → Fin (3 ^ j - 1)) → ℝ) →ₗ[ℝ] H1Function (openCubeSet Q) where
  toFun b := ∑ z, b z • diagPhysicalHatH1 Q (diagInteriorVertex Q j z)
    (diagMeshRadius Q j) (diagMeshRadius_pos Q j)
  map_add' b c := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c b := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum]

/-- The source nodal values of the odd-reflected affine residual. -/
def diagNodalValuesLinear (Q : TriadicCube 2) (j : ℕ) :
    H1Function (openCubeSet Q) →ₗ[ℝ] ((Fin 2 → Fin (3 ^ j - 1)) → ℝ) :=
  LinearMap.pi fun z =>
    ((diagOddNodalMeanLinear (cubeCorner Q) (diagMeshRadius Q j) (3 ^ j)
      (diagInteriorVertexIndex j z)).comp (diagProjectionLinear Q j)).comp
        (diagResidualLinear Q)

/-- The actual DIAG operator: keep the mean-gradient affine part, average
four neighboring cell means of its residual, and interpolate bilinearly. -/
def diagInterpolant (Q : TriadicCube 2) (j : ℕ) :
    H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q) :=
  (diagAffineLinear Q).comp (diagMeanGradientLinear Q) +
    (diagSynthesisH1Linear Q j).comp (diagNodalValuesLinear Q j)

theorem diagSynthesisH1Linear_toFun (Q : TriadicCube 2) (j : ℕ)
    (b : (Fin 2 → Fin (3 ^ j - 1)) → ℝ) (x : Vec 2) :
    (diagSynthesisH1Linear Q j b).toFun x =
      ∑ z, b z * diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x := by
  have h (s : Finset (Fin 2 → Fin (3 ^ j - 1))) :
      (∑ z ∈ s, b z • diagPhysicalHatH1 Q (diagInteriorVertex Q j z)
        (diagMeshRadius Q j) (diagMeshRadius_pos Q j)).toFun x =
      ∑ z ∈ s, b z * diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; rfl
    | @insert z s hz ih =>
        simp only [Finset.sum_insert hz, H1Function.add_toFun, H1Function.smul_toFun,
          diagPhysicalHatH1_toFun, ih]
  exact h Finset.univ

theorem diagInterpolant_toFun (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (x : Vec 2) :
    (diagInterpolant Q j v).toFun x =
      (∑ i, diagMeanGradientLinear Q v i * x i) +
      ∑ z, diagNodalValuesLinear Q j v z *
        diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x := by
  simp only [diagInterpolant, LinearMap.add_apply, LinearMap.comp_apply, H1Function.add_toFun,
    diagAffineLinear, LinearMap.coe_mk, AddHom.coe_mk,
    H1Function.affineOnIsSobolevRegularDomain_apply, diagSynthesisH1Linear_toFun]

/-- Every interpolated residual is in H¹₀, even for a general H¹ input. -/
theorem diagSynthesis_memH10 (Q : TriadicCube 2) (j : ℕ)
    (b : (Fin 2 → Fin (3 ^ j - 1)) → ℝ) :
    MemH10 (openCubeSet Q) (diagSynthesisH1Linear Q j b).toFun := by
  have hs (s : Finset (Fin 2 → Fin (3 ^ j - 1))) :
      MemH10 (openCubeSet Q) (fun x => ∑ z ∈ s,
        b z * diagPhysicalHat (diagInteriorVertex Q j z) (diagMeshRadius Q j) x) := by
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨0, ?_⟩
        funext x
        simp only [Finset.sum_empty]
        rfl
    | @insert z s hz ih =>
        simpa only [Finset.sum_insert hz] using memH10_add
          (memH10_smul (b z) (diagPhysicalHat_memH10 Q _
            (diagMeshRadius_pos Q j) (diagInteriorVertex_support Q j z))) ih
  have h := hs Finset.univ
  convert h using 1
  funext x
  exact diagSynthesisH1Linear_toFun Q j b x

/-- The exact residual premise required by `lemmaV_of_interpolant`.
No boundary or zero-trace conclusion is assumed. -/
theorem diagInterpolant_affine_residual_memH10 (Q : TriadicCube 2) (j : ℕ)
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    MemH10 (openCubeSet Q)
      (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r -
        diagInterpolant Q j (ASDExplicitGamma.Variational.lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun := by
  let v := ASDExplicitGamma.Variational.lemmaVAffinePotential
    (isOpenBoundedConvexDomain_openCubeSet Q) p r
  have hp := diagMeanGradient_affinePotential Q p r
  have h := memH10_sub r.memH10 (diagSynthesis_memH10 Q j (diagNodalValuesLinear Q j v))
  convert h using 1
  funext x
  simp only [H1Function.sub_toFun]
  change v.toFun x - (diagInterpolant Q j v).toFun x =
    r.toH1Function.toFun x - (diagSynthesisH1Linear Q j (diagNodalValuesLinear Q j v)).toFun x
  rw [diagInterpolant_toFun, hp, diagSynthesisH1Linear_toFun]
  change ((∑ i, p i * x i) + r.toH1Function.toFun x) - _ = _
  ring

end

end ASDExplicitGamma.Triadic
