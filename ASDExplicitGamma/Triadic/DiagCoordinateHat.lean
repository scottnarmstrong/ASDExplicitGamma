module

public import ASDExplicitGamma.Triadic.DiagLinear
public import ASDExplicitGamma.Triadic.DiagWeakIBP
public import Homogenization.Sobolev.Truncation.Basic

/-! One-coordinate tent tests for the sharp source cell-difference identity. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

local instance diagTentFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- A one-coordinate positive part, built by the proved Sobolev truncation API. -/
def diagRampH1 (Q : TriadicCube 2) (i : Fin 2) (c : ℝ) : H1Function (openCubeSet Q) :=
  Classical.choose (exists_h1_max_sub_const (isOpenBoundedConvexDomain_openCubeSet Q)
    (diagAffineLinear Q (basisVec i)) c)

theorem diagRampH1_toFun (Q : TriadicCube 2) (i : Fin 2) (c : ℝ) :
    (diagRampH1 Q i c).toFun = fun x => max (x i - c) 0 := by
  have h := (Classical.choose_spec (exists_h1_max_sub_const
    (isOpenBoundedConvexDomain_openCubeSet Q) (diagAffineLinear Q (basisVec i)) c)).1
  have hv (x : Vec 2) : (diagAffineLinear Q (basisVec i)).toFun x = x i := by
    change (∑ k, basisVec i k * x k) = x i
    exact vecDot_basisVec_left i x
  simpa only [diagRampH1, hv] using h

theorem diagRampH1_grad_ae (Q : TriadicCube 2) (i : Fin 2) (c : ℝ) :
    (diagRampH1 Q i c).grad =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => (if c < x i then (1 : ℝ) else 0) • basisVec i := by
  have h := (Classical.choose_spec (exists_h1_max_sub_const
    (isOpenBoundedConvexDomain_openCubeSet Q) (diagAffineLinear Q (basisVec i)) c)).2
  have hv (x : Vec 2) : (diagAffineLinear Q (basisVec i)).toFun x = x i := by
    change (∑ k, basisVec i k * x k) = x i
    exact vecDot_basisVec_left i x
  have hD (x : Vec 2) : (diagAffineLinear Q (basisVec i)).grad x = basisVec i := by
    exact H1Function.affineOnIsSobolevRegularDomain_grad
      (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain (basisVec i) x
  filter_upwards [h] with x hx
  change (diagRampH1 Q i c).grad x = _ at hx
  rw [hx]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, hv, hD]
  split_ifs <;> simp

/-- A coordinate tent; no boundary condition is required on a test function. -/
def diagCoordinateHatH1 (Q : TriadicCube 2) (i : Fin 2) (c r : ℝ) :
    H1Function (openCubeSet Q) :=
  r⁻¹ • (diagRampH1 Q i (c - r) - (2 : ℝ) • diagRampH1 Q i c + diagRampH1 Q i (c + r))

theorem diagCoordinateHatH1_toFun (Q : TriadicCube 2) (i : Fin 2) (c : ℝ)
    {r : ℝ} (hr : 0 < r) :
    (diagCoordinateHatH1 Q i c r).toFun = fun x => diagHat ((x i - c) / r) := by
  funext x
  simp only [diagCoordinateHatH1, H1Function.smul_toFun, H1Function.add_toFun,
    H1Function.sub_toFun, diagRampH1_toFun]
  rw [diagHat_eq_positiveParts hr]
  have heq : x i - (c - r) = x i - c + r := by ring
  have heq' : x i - (c + r) = x i - c - r := by ring
  simp only [heq, heq']
  change r⁻¹ * (_ - (2 : ℝ) * _ + _) = _
  ring

theorem diagCoordinateHatH1_grad_ae (Q : TriadicCube 2) (i : Fin 2) (c r : ℝ) :
    (diagCoordinateHatH1 Q i c r).grad =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => diagHatSlope r (x i - c) • basisVec i := by
  filter_upwards [diagRampH1_grad_ae Q i (c - r), diagRampH1_grad_ae Q i c,
    diagRampH1_grad_ae Q i (c + r)] with x hl hm hu
  simp only [diagCoordinateHatH1, H1Function.smul_grad, H1Function.add_grad,
    H1Function.sub_grad, hl, hm, hu]
  have h1 : (c - r < x i) ↔ (-r < x i - c) := by constructor <;> intro h <;> linarith only [h]
  have h2 : (c < x i) ↔ (0 < x i - c) := by constructor <;> intro h <;> linarith only [h]
  have h3 : (c + r < x i) ↔ (r < x i - c) := by constructor <;> intro h <;> linarith only [h]
  simp only [h1, h2, h3]
  funext k
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, diagHatSlope]
  ring

/-- Every continuous scalar function on the closed cube is bounded in L∞
on its open representative. -/
theorem diagContinuous_memLp_top (Q : TriadicCube 2) {f : Vec 2 → ℝ} (hf : Continuous f) :
    MemLp f ⊤ (volume.restrict (openCubeSet Q)) := by
  obtain ⟨C, hC⟩ := (isBounded_cubeSet Q).isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  exact hC x (subset_closure (openCubeSet_subset_cubeSet Q hx))

/-- Smooth scalar multipliers on a bounded cube act on H¹. -/
def diagMulSmooth (Q : TriadicCube 2) (u : H1Function (openCubeSet Q))
    (φ : Vec 2 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : H1Function (openCubeSet Q) :=
  u.mulContDiffMemLpTop hφ (diagContinuous_memLp_top Q hφ.continuous)
    (fun i => diagContinuous_memLp_top Q
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const))

end

end ASDExplicitGamma.Triadic
