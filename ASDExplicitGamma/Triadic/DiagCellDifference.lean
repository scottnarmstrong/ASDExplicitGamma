module

public import ASDExplicitGamma.Triadic.DiagStripIBP
public import ASDExplicitGamma.Triadic.DiagNeighbors

/-! Exact neighboring-cell mean difference from the source H¹₀ potential. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Set

noncomputable section

local instance diagDifferenceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem diag_integrable_mul_continuous (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) (g : Vec 2 → ℝ) (hg : Continuous g) :
    Integrable (fun x => f x * g x) (volume.restrict (openCubeSet Q)) := by
  simpa only [mul_comm] using ((diagContinuous_memLp_top Q hg).fun_mul hf).integrable one_le_two

theorem diag_integral_cell_indicator (Q : TriadicCube 2) (j : ℕ) (R : TriadicCube 2)
    (hR : R ∈ descendantsAtDepth Q j) (f g : Vec 2 → ℝ) :
    (∫ x in openCubeSet Q, f x * (openCubeSet R).indicator g x) =
      ∫ x in openCubeSet R, f x * g x := by
  have heq : (fun x => f x * (openCubeSet R).indicator g x) =
      (openCubeSet R).indicator (fun x => f x * g x) := by
    funext x
    by_cases hx : x ∈ openCubeSet R <;> simp [hx]
  rw [heq, integral_indicator (measurableSet_openCubeSet R),
    Measure.restrict_restrict_of_subset (openCubeSet_subset_of_mem_descendantsAtDepth hR)]

/-- Splitting an actual two-cell kernel introduces no measure or overlap factor. -/
theorem diag_integral_two_cell_kernel (Q : TriadicCube 2) (j : ℕ) (R S : TriadicCube 2)
    (hR : R ∈ descendantsAtDepth Q j) (hS : S ∈ descendantsAtDepth Q j)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (volume.restrict (openCubeSet Q)))
    (K gR gS : Vec 2 → ℝ) (hgR : Continuous gR) (hgS : Continuous gS)
    (hK : K =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => (openCubeSet R).indicator gR x + (openCubeSet S).indicator gS x) :
    (∫ x in openCubeSet Q, f x * K x) =
      (∫ x in openCubeSet R, f x * gR x) + ∫ x in openCubeSet S, f x * gS x := by
  have hIR : Integrable (fun x => f x * (openCubeSet R).indicator gR x)
      (volume.restrict (openCubeSet Q)) := by
    have h := (diag_integrable_mul_continuous Q hf gR hgR).indicator (measurableSet_openCubeSet R)
    convert h using 1
    funext x
    by_cases hx : x ∈ openCubeSet R <;> simp [hx]
  have hIS : Integrable (fun x => f x * (openCubeSet S).indicator gS x)
      (volume.restrict (openCubeSet Q)) := by
    have h := (diag_integrable_mul_continuous Q hf gS hgS).indicator (measurableSet_openCubeSet S)
    convert h using 1
    funext x
    by_cases hx : x ∈ openCubeSet S <;> simp [hx]
  have hpoint : (fun x => f x * K x) =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => f x * (openCubeSet R).indicator gR x + f x * (openCubeSet S).indicator gS x := by
    filter_upwards [hK] with x hx
    rw [hx, mul_add]
  rw [integral_congr_ae hpoint, integral_add hIR hIS,
    diag_integral_cell_indicator Q j R hR, diag_integral_cell_indicator Q j S hS]

/-- The raw two-cell tent identity for neighboring source cells. -/
theorem diagH10_twoCell_integral_identity (Q : TriadicCube 2) (j : ℕ) (R : TriadicCube 2)
    (i s : Fin 2) (his : i ≠ s) (hR : R ∈ descendantsAtDepth Q j)
    (hS : diagCellNeighbor R i ∈ descendantsAtDepth Q j)
    (u : H10Function (openCubeSet Q)) :
    let r := cubeScaleFactor R
    let c := cubeCorner R i + r
    ((∫ x in openCubeSet R, u.toH1Function.grad x i * ((x i - c + r) / r)) +
      ∫ x in openCubeSet (diagCellNeighbor R i), u.toH1Function.grad x i * ((c + r - x i) / r)) =
      -((∫ x in openCubeSet R, u.toH1Function.toFun x * (1 / r)) +
        ∫ x in openCubeSet (diagCellNeighbor R i), u.toH1Function.toFun x * (-1 / r)) := by
  intro r c
  let strip := fun x : Vec 2 => x s ∈ Ioo (cubeCorner R s) (cubeCorner R s + r)
  let Kt := fun x : Vec 2 => (if strip x then (1 : ℝ) else 0) * diagHat ((x i - c) / r)
  let Ks := fun x : Vec 2 => (if strip x then (1 : ℝ) else 0) * diagHatSlope r (x i - c)
  have hKt : Kt =ᵐ[volume.restrict (openCubeSet Q)] fun x =>
      (openCubeSet R).indicator (fun x => (x i - c + r) / r) x +
        (openCubeSet (diagCellNeighbor R i)).indicator (fun x => (c + r - x i) / r) x := by
    filter_upwards [ae_restrict_of_ae (diagTwoCell_tentKernels R i s his)] with x hx
    exact hx.1
  have hKs : Ks =ᵐ[volume.restrict (openCubeSet Q)] fun x =>
      (openCubeSet R).indicator (fun _ => 1 / r) x +
        (openCubeSet (diagCellNeighbor R i)).indicator (fun _ => -1 / r) x := by
    filter_upwards [ae_restrict_of_ae (diagTwoCell_tentKernels R i s his)] with x hx
    exact hx.2
  have h := diagH10_tentStrip Q u i s his c (cubeScaleFactor_pos' R) (cubeCorner R s) r
  have h' : (∫ x in openCubeSet Q, u.toH1Function.grad x i * Kt x) =
      -∫ x in openCubeSet Q, u.toH1Function.toFun x * Ks x := by
    simpa only [Kt, Ks, strip, mul_left_comm, mul_assoc] using h
  rw [diag_integral_two_cell_kernel Q j R (diagCellNeighbor R i) hR hS
      (u.toH1Function.gradMemL2 i) Kt _ _ (by fun_prop) (by fun_prop) hKt,
    diag_integral_two_cell_kernel Q j R (diagCellNeighbor R i) hR hS
      u.toH1Function.memL2 Ks _ _ continuous_const continuous_const hKs] at h'
  exact h'

theorem diagAverage_mul_centered_add_half (R : TriadicCube 2) (i : Fin 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure R)) :
    cubeAverage R (fun x => f x * (diagCenteredCoordinate R i x + 1 / 2)) =
      pairing R f (diagCenteredCoordinate R i) + cubeAverage R f / 2 := by
  have ht : Integrable (fun x => f x * diagCenteredCoordinate R i x) (normalizedCubeMeasure R) :=
    hf.integrable_mul (diagCenteredCoordinate_memLp R i)
  have hc : Integrable (fun x => f x * (1 / 2)) (normalizedCubeMeasure R) :=
    (hf.integrable one_le_two).mul_const (1 / 2)
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure, pairing, mul_add]
  rw [integral_add ht hc, integral_mul_const]
  ring

theorem diagAverage_mul_half_sub_centered (R : TriadicCube 2) (i : Fin 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure R)) :
    cubeAverage R (fun x => f x * (1 / 2 - diagCenteredCoordinate R i x)) =
      cubeAverage R f / 2 - pairing R f (diagCenteredCoordinate R i) := by
  have ht : Integrable (fun x => f x * diagCenteredCoordinate R i x) (normalizedCubeMeasure R) :=
    hf.integrable_mul (diagCenteredCoordinate_memLp R i)
  have hc : Integrable (fun x => f x * (1 / 2)) (normalizedCubeMeasure R) :=
    (hf.integrable one_le_two).mul_const (1 / 2)
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure, pairing, mul_sub]
  rw [integral_sub hc ht, integral_mul_const]
  ring

/-- The exact source neighboring-face identity in averaged form. It is
proved directly with the two-cell tent kernel and retains the minus sign
on the right cell's centered functional. -/
theorem diagCellNeighbor_mean_difference (Q : TriadicCube 2) (j : ℕ) (R : TriadicCube 2)
    (i s : Fin 2) (his : i ≠ s) (hR : R ∈ descendantsAtDepth Q j)
    (hS : diagCellNeighbor R i ∈ descendantsAtDepth Q j)
    (u : H10Function (openCubeSet Q)) :
    (cubeAverage (diagCellNeighbor R i) u.toH1Function.toFun - cubeAverage R u.toH1Function.toFun) /
        cubeScaleFactor R =
      (cubeAverage R (fun x => u.toH1Function.grad x i) +
        cubeAverage (diagCellNeighbor R i) (fun x => u.toH1Function.grad x i)) / 2 +
      pairing R (fun x => u.toH1Function.grad x i) (diagCenteredCoordinate R i) -
      pairing (diagCellNeighbor R i) (fun x => u.toH1Function.grad x i)
        (diagCenteredCoordinate (diagCellNeighbor R i) i) := by
  let S := diagCellNeighbor R i
  let r := cubeScaleFactor R
  let c := cubeCorner R i + r
  have hraw := diagH10_twoCell_integral_identity Q j R i s his hR hS u
  have hnorm :
      cubeAverage R (fun x => u.toH1Function.grad x i * ((x i - c + r) / r)) +
        cubeAverage S (fun x => u.toH1Function.grad x i * ((c + r - x i) / r)) =
      -(cubeAverage R (fun x => u.toH1Function.toFun x * (1 / r)) +
        cubeAverage S (fun x => u.toH1Function.toFun x * (-1 / r))) := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_normalized_eq_open,
      show cubeVolume S = cubeVolume R from rfl]
    simpa only [mul_add, mul_neg] using congrArg (fun z : ℝ => (cubeVolume R)⁻¹ * z) hraw
  have hgR := memLp_on_descendant_of_memLp hR (u.toH1Function.grad_memL2_normalizedCubeMeasure i)
  have hgS := memLp_on_descendant_of_memLp hS (u.toH1Function.grad_memL2_normalizedCubeMeasure i)
  have hleft (x : Vec 2) : (x i - c + r) / r = diagCenteredCoordinate R i x + 1 / 2 := by
    dsimp only [c, r]
    unfold diagCenteredCoordinate
    ring
  have hright (x : Vec 2) : (c + r - x i) / r = 1 / 2 - diagCenteredCoordinate S i x := by
    dsimp only [S, c, r]
    simp only [diagCenteredCoordinate, diagCellNeighbor_side, diagCellNeighbor_corner, ite_true]
    field_simp [(cubeScaleFactor_pos' R).ne']
    ring
  simp_rw [hleft, hright] at hnorm
  rw [diagAverage_mul_centered_add_half R i hgR,
    diagAverage_mul_half_sub_centered S i hgS] at hnorm
  have hC (V : TriadicCube 2) (d : ℝ) : cubeAverage V (fun x => u.toH1Function.toFun x * d) =
      cubeAverage V u.toH1Function.toFun * d := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_mul_const]
  rw [hC, hC] at hnorm
  change (cubeAverage S u.toH1Function.toFun - cubeAverage R u.toH1Function.toFun) / r = _
  calc
    _ = -(cubeAverage R u.toH1Function.toFun * (1 / r) +
      cubeAverage S u.toH1Function.toFun * (-1 / r)) := by ring
    _ = _ := by rw [← hnorm]; ring

end

end ASDExplicitGamma.Triadic
