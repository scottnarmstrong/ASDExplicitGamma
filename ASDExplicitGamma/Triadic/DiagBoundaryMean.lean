module

public import ASDExplicitGamma.Triadic.DiagCellDifference

/-! The source boundary-face mean identities from actual H¹₀ data. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Set

noncomputable section

/-- The exterior neighbor across the upper parent face has no open overlap
with the parent. -/
theorem diagUpperNeighbor_disjoint (Q R : TriadicCube 2) (i : Fin 2)
    (hface : cubeCorner R i + cubeScaleFactor R = cubeCorner Q i + cubeScaleFactor Q) :
    Disjoint (openCubeSet Q) (openCubeSet (diagCellNeighbor R i)) := by
  apply Set.disjoint_left.mpr
  intro x hxQ hxS
  have hq := (openCubeSet_eq_box Q ▸ hxQ) i (mem_univ i)
  have hs := (openCubeSet_eq_box (diagCellNeighbor R i) ▸ hxS) i (mem_univ i)
  beta_reduce at hq hs
  rw [diagCellNeighbor_corner, ite_eq_left rfl] at hs
  linarith only [hq.2, hs.1, hface]

/-- A single-cell version of kernel splitting. -/
theorem diag_integral_one_cell_kernel (Q : TriadicCube 2) (j : ℕ) (R : TriadicCube 2)
    (hR : R ∈ descendantsAtDepth Q j) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) (K g : Vec 2 → ℝ) (hg : Continuous g)
    (hK : K =ᵐ[volume.restrict (openCubeSet Q)] (openCubeSet R).indicator g) :
    (∫ x in openCubeSet Q, f x * K x) = ∫ x in openCubeSet R, f x * g x := by
  have hK' : K =ᵐ[volume.restrict (openCubeSet Q)] fun x =>
      (openCubeSet R).indicator g x + (openCubeSet R).indicator (fun _ => (0 : ℝ)) x := by
    filter_upwards [hK] with x hx
    rw [hx]
    by_cases hxR : x ∈ openCubeSet R <;> simp [hxR]
  have h := diag_integral_two_cell_kernel Q j R R hR hR hf K g (fun _ => 0) hg continuous_const hK'
  simpa only [mul_zero, integral_zero, add_zero] using h

/-- The exact zero-boundary mean identity at an upper parent face. -/
theorem diagUpperFace_mean_identity (Q : TriadicCube 2) (j : ℕ) (R : TriadicCube 2)
    (i s : Fin 2) (his : i ≠ s) (hR : R ∈ descendantsAtDepth Q j)
    (hface : cubeCorner R i + cubeScaleFactor R = cubeCorner Q i + cubeScaleFactor Q)
    (u : H10Function (openCubeSet Q)) :
    cubeAverage R u.toH1Function.toFun / cubeScaleFactor R =
      -cubeAverage R (fun x => u.toH1Function.grad x i) / 2 -
        pairing R (fun x => u.toH1Function.grad x i) (diagCenteredCoordinate R i) := by
  let r := cubeScaleFactor R
  let c := cubeCorner R i + r
  let strip := fun x : Vec 2 => x s ∈ Ioo (cubeCorner R s) (cubeCorner R s + r)
  let Kt := fun x : Vec 2 => (if strip x then (1 : ℝ) else 0) * diagHat ((x i - c) / r)
  let Ks := fun x : Vec 2 => (if strip x then (1 : ℝ) else 0) * diagHatSlope r (x i - c)
  have hnot : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), x ∉ openCubeSet (diagCellNeighbor R i) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact fun hy => Set.disjoint_left.mp (diagUpperNeighbor_disjoint Q R i hface) hx hy
  have hKt : Kt =ᵐ[volume.restrict (openCubeSet Q)]
      (openCubeSet R).indicator (fun x => (x i - c + r) / r) := by
    filter_upwards [ae_restrict_of_ae (diagTwoCell_tentKernels R i s his), hnot] with x hx hn
    simpa only [Set.indicator_of_notMem hn, add_zero] using hx.1
  have hKs : Ks =ᵐ[volume.restrict (openCubeSet Q)]
      (openCubeSet R).indicator (fun _ => 1 / r) := by
    filter_upwards [ae_restrict_of_ae (diagTwoCell_tentKernels R i s his), hnot] with x hx hn
    simpa only [Set.indicator_of_notMem hn, add_zero] using hx.2
  have h := diagH10_tentStrip Q u i s his c (cubeScaleFactor_pos' R) (cubeCorner R s) r
  have h' : (∫ x in openCubeSet Q, u.toH1Function.grad x i * Kt x) =
      -∫ x in openCubeSet Q, u.toH1Function.toFun x * Ks x := by
    simpa only [Kt, Ks, strip, mul_left_comm, mul_assoc] using h
  rw [diag_integral_one_cell_kernel Q j R hR (u.toH1Function.gradMemL2 i)
      Kt _ (by fun_prop) hKt,
    diag_integral_one_cell_kernel Q j R hR u.toH1Function.memL2
      Ks _ continuous_const hKs] at h'
  have hnorm : cubeAverage R (fun x => u.toH1Function.grad x i * ((x i - c + r) / r)) =
      -cubeAverage R (fun x => u.toH1Function.toFun x * (1 / r)) := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_normalized_eq_open]
    simpa only [mul_neg] using congrArg (fun z : ℝ => (cubeVolume R)⁻¹ * z) h'
  have hleft (x : Vec 2) : (x i - c + r) / r = diagCenteredCoordinate R i x + 1 / 2 := by
    dsimp only [c, r]
    unfold diagCenteredCoordinate
    ring
  simp_rw [hleft] at hnorm
  rw [diagAverage_mul_centered_add_half R i
    (memLp_on_descendant_of_memLp hR (u.toH1Function.grad_memL2_normalizedCubeMeasure i))] at hnorm
  have hC : cubeAverage R (fun x => u.toH1Function.toFun x * (1 / r)) =
      cubeAverage R u.toH1Function.toFun / r := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_mul_const]
    ring
  rw [hC] at hnorm
  change cubeAverage R u.toH1Function.toFun / r = _
  linarith only [hnorm]

/-- The congruent cell immediately before `R` in coordinate `i`. -/
def diagCellBefore (R : TriadicCube 2) (i : Fin 2) : TriadicCube 2 :=
  ⟨R.scale, fun k => R.index k - if k = i then 1 else 0⟩

@[simp] theorem diagCellBefore_side (R : TriadicCube 2) (i : Fin 2) :
    cubeScaleFactor (diagCellBefore R i) = cubeScaleFactor R := rfl

@[simp] theorem diagCellNeighbor_before (R : TriadicCube 2) (i : Fin 2) :
    diagCellNeighbor (diagCellBefore R i) i = R := by
  cases R
  simp [diagCellBefore, diagCellNeighbor]

theorem diagCellBefore_corner (R : TriadicCube 2) (i k : Fin 2) :
    cubeCorner (diagCellBefore R i) k = cubeCorner R k -
      if k = i then cubeScaleFactor R else 0 := by
  by_cases hk : k = i
  · simp [cubeCorner, diagCellBefore, cubeScaleFactor, hk]
    ring
  · simp [cubeCorner, diagCellBefore, cubeScaleFactor, hk]

theorem diagCellBefore_upper_face (R : TriadicCube 2) (i : Fin 2) :
    cubeCorner (diagCellBefore R i) i + cubeScaleFactor (diagCellBefore R i) = cubeCorner R i := by
  rw [diagCellBefore_corner, ite_eq_left rfl, diagCellBefore_side]
  ring

theorem diagLowerNeighbor_disjoint (Q R : TriadicCube 2) (i : Fin 2)
    (hface : cubeCorner R i = cubeCorner Q i) :
    Disjoint (openCubeSet Q) (openCubeSet (diagCellBefore R i)) := by
  apply Set.disjoint_left.mpr
  intro x hxQ hxP
  have hq := (openCubeSet_eq_box Q ▸ hxQ) i (mem_univ i)
  have hp := (openCubeSet_eq_box (diagCellBefore R i) ▸ hxP) i (mem_univ i)
  beta_reduce at hq hp
  rw [diagCellBefore_upper_face] at hp
  linarith only [hq.1, hp.2, hface]

/-- The exact zero-boundary mean identity at a lower parent face. -/
theorem diagLowerFace_mean_identity (Q : TriadicCube 2) (j : ℕ) (R : TriadicCube 2)
    (i s : Fin 2) (his : i ≠ s) (hR : R ∈ descendantsAtDepth Q j)
    (hface : cubeCorner R i = cubeCorner Q i)
    (u : H10Function (openCubeSet Q)) :
    cubeAverage R u.toH1Function.toFun / cubeScaleFactor R =
      cubeAverage R (fun x => u.toH1Function.grad x i) / 2 -
        pairing R (fun x => u.toH1Function.grad x i) (diagCenteredCoordinate R i) := by
  let r := cubeScaleFactor R
  let c := cubeCorner R i
  let strip := fun x : Vec 2 => x s ∈ Ioo (cubeCorner R s) (cubeCorner R s + r)
  let Kt := fun x : Vec 2 => (if strip x then (1 : ℝ) else 0) * diagHat ((x i - c) / r)
  let Ks := fun x : Vec 2 => (if strip x then (1 : ℝ) else 0) * diagHatSlope r (x i - c)
  have hnot : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)), x ∉ openCubeSet (diagCellBefore R i) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact fun hy => Set.disjoint_left.mp (diagLowerNeighbor_disjoint Q R i hface) hx hy
  have hKt : Kt =ᵐ[volume.restrict (openCubeSet Q)]
      (openCubeSet R).indicator (fun x => (c + r - x i) / r) := by
    filter_upwards [ae_restrict_of_ae (diagTwoCell_tentKernels (diagCellBefore R i) i s his), hnot] with x hx hn
    simpa only [diagCellBefore_side, diagCellNeighbor_before, diagCellBefore_corner,
      ite_eq_left rfl, ite_true, ite_eq_right his.symm, sub_add_cancel, sub_zero,
      Set.indicator_of_notMem hn, zero_add] using hx.1
  have hKs : Ks =ᵐ[volume.restrict (openCubeSet Q)]
      (openCubeSet R).indicator (fun _ => -1 / r) := by
    filter_upwards [ae_restrict_of_ae (diagTwoCell_tentKernels (diagCellBefore R i) i s his), hnot] with x hx hn
    simpa only [diagCellBefore_side, diagCellNeighbor_before, diagCellBefore_corner,
      ite_eq_left rfl, ite_true, ite_eq_right his.symm, sub_add_cancel, sub_zero,
      Set.indicator_of_notMem hn, zero_add] using hx.2
  have h := diagH10_tentStrip Q u i s his c (cubeScaleFactor_pos' R) (cubeCorner R s) r
  have h' : (∫ x in openCubeSet Q, u.toH1Function.grad x i * Kt x) =
      -∫ x in openCubeSet Q, u.toH1Function.toFun x * Ks x := by
    simpa only [Kt, Ks, strip, mul_left_comm, mul_assoc] using h
  rw [diag_integral_one_cell_kernel Q j R hR (u.toH1Function.gradMemL2 i)
      Kt _ (by fun_prop) hKt,
    diag_integral_one_cell_kernel Q j R hR u.toH1Function.memL2
      Ks _ continuous_const hKs] at h'
  have hnorm : cubeAverage R (fun x => u.toH1Function.grad x i * ((c + r - x i) / r)) =
      -cubeAverage R (fun x => u.toH1Function.toFun x * (-1 / r)) := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_normalized_eq_open]
    simpa only [mul_neg] using congrArg (fun z : ℝ => (cubeVolume R)⁻¹ * z) h'
  have hright (x : Vec 2) : (c + r - x i) / r = 1 / 2 - diagCenteredCoordinate R i x := by
    dsimp only [c, r]
    unfold diagCenteredCoordinate
    field_simp [(cubeScaleFactor_pos' R).ne']
    ring
  simp_rw [hright] at hnorm
  rw [diagAverage_mul_half_sub_centered R i
    (memLp_on_descendant_of_memLp hR (u.toH1Function.grad_memL2_normalizedCubeMeasure i))] at hnorm
  have hC : cubeAverage R (fun x => u.toH1Function.toFun x * (-1 / r)) =
      -cubeAverage R u.toH1Function.toFun / r := by
    simp only [cubeAverage_eq_integral_normalizedCubeMeasure, integral_mul_const]
    ring
  rw [hC] at hnorm
  change cubeAverage R u.toH1Function.toFun / r = _
  simpa only [neg_div, neg_neg] using hnorm.symm

end

end ASDExplicitGamma.Triadic
