module

public import ASDExplicitGamma.Triadic.DiagFluctuationBounds
public import ASDExplicitGamma.Triadic.DiagEnergyYoung

/-! The exact residual constants 2/pi+1/2 and c0+1/2 for source H10 data. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

/-- Weighted broken positive inequality, splitting at the same source cell mean. -/
theorem diagTiledPositive_residual_split_le (Q : TriadicCube 2) (j : ℕ)
    (u v : H1Function (openCubeSet Q)) {t : ℝ} (ht : 0 < t) :
    diagTiledScalarPositiveEnergy Q j (u-v).toFun ≤
      (1+t)*diagTiledScalarPositiveEnergy Q j (fun x => u.toFun x-cubeProjection Q j u.toFun x) +
      (1+t⁻¹)*diagTiledScalarPositiveEnergy Q j (fun x => v.toFun x-cubeProjection Q j u.toFun x) := by
  have hpoint (k : Fin 2 → Fin (3^j)) :
      primalEnergy (diagMeshCell Q j k) (Real.sqrt 3) (u-v).toFun ≤
        (1+t)*primalEnergy (diagMeshCell Q j k) (Real.sqrt 3) (fun x => u.toFun x-cubeProjection Q j u.toFun x)+
        (1+t⁻¹)*primalEnergy (diagMeshCell Q j k) (Real.sqrt 3) (fun x => v.toFun x-cubeProjection Q j u.toFun x) := by
    let R := diagMeshCell Q j k
    let c := h1ConstantOnCube R (cubeAverage R u.toFun)
    let a := u.restrictToOpenSubcube (diagMeshCell_mem Q j k)-c
    let b := v.restrictToOpenSubcube (diagMeshCell_mem Q j k)-c
    have ha : (fun x => u.toFun x-cubeProjection Q j u.toFun x) =ᵐ[volume.restrict (cubeSet R)] a.toFun := by
      filter_upwards [diagProjection_mesh_cell_ae Q j u k] with x hx
      simp only [a, c, H1Function.sub_toFun, h1ConstantOnCube_toFun]
      change u.toFun x-cubeProjection Q j u.toFun x = u.toFun x-cubeAverage R u.toFun
      rw [hx]
    have hb : (fun x => v.toFun x-cubeProjection Q j u.toFun x) =ᵐ[volume.restrict (cubeSet R)] b.toFun := by
      filter_upwards [diagProjection_mesh_cell_ae Q j u k] with x hx
      simp only [b, c, H1Function.sub_toFun, h1ConstantOnCube_toFun]
      change v.toFun x-cubeProjection Q j u.toFun x = v.toFun x-cubeAverage R u.toFun
      rw [hx]
    have hab : (a-b).toFun = (u-v).toFun := by
      funext x
      simp only [a, b, H1Function.sub_toFun]
      change (u.toFun x-c.toFun x)-(v.toFun x-c.toFun x) = u.toFun x-v.toFun x
      ring
    rw [diagPrimalEnergy_congr_ae R _ ha, diagPrimalEnergy_congr_ae R _ hb, ← hab]
    exact diagPrimalEnergy_sub_le R a b ht
  unfold diagTiledScalarPositiveEnergy
  simp only [diagDescendantsAverage_eq_grid_average]
  have hs := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s := Finset.univ) fun k _ => hpoint k)
    (sq_nonneg (((3^j:ℕ):ℝ)⁻¹))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  convert hs using 1
  ring

/-- Squared source positive residual estimate with the sharp sum of constants. -/
theorem diagInterpolant_h10_residual_positive_energy_le (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    diagTiledScalarPositiveEnergy Q j (u.toH1Function-diagInterpolant Q j u.toH1Function).toFun ≤
      diagMeshRadius Q j^2*(2/Real.pi+1/2)^2*
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  let t : ℝ := Real.pi/4
  have ht : 0 < t := div_pos Real.pi_pos (by norm_num)
  have h := diagTiledPositive_residual_split_le Q j u.toH1Function (diagInterpolant Q j u.toH1Function) ht
  have ha := mul_le_mul_of_nonneg_left (diagTiledFluctuation_positive_energy_le Q j u.toH1Function)
    (show 0 ≤ 1+t by positivity)
  have hb := mul_le_mul_of_nonneg_left (diagInterpolant_h10_mean_positive_energy_le Q j u)
    (show 0 ≤ 1+t⁻¹ by positivity)
  apply (h.trans (add_le_add ha hb)).trans_eq
  dsimp only [t]
  field_simp [Real.pi_ne_zero]
  ring

/-- The exact Neumann cell constant is strictly positive. -/
theorem diagPlanarC0_pos : 0 < planarC0 := by
  have hs := Real.sqrt_nonneg (3:ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have h9 : 0 < 9-Real.sqrt 3 := by nlinarith only [hs, hsq]
  unfold planarC0
  apply Real.sqrt_pos.mpr
  exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
    (mul_pos h9 (sq_pos_of_pos Real.pi_pos))

/-- Squared global L2 residual estimate with the exact Neumann constant c0. -/
theorem diagInterpolant_h10_residual_L2_energy_le (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    energy Q (u.toH1Function-diagInterpolant Q j u.toH1Function).toFun ≤
      diagMeshRadius Q j^2*(planarC0+1/2)^2*
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad := by
  let f := fun x => u.toH1Function.toFun x-cubeProjection Q j u.toH1Function.toFun x
  let g := fun x => (diagInterpolant Q j u.toH1Function).toFun x-cubeProjection Q j u.toH1Function.toFun x
  let t : ℝ := (2*planarC0)⁻¹
  have ht : 0 < t := inv_pos.mpr (mul_pos (by norm_num) diagPlanarC0_pos)
  have hf : MemLp f 2 (normalizedCubeMeasure Q) :=
    u.toH1Function.memL2_normalizedCubeMeasure.sub (projection_memLp Q j u.toH1Function.toFun 2)
  have hg : MemLp g 2 (normalizedCubeMeasure Q) :=
    (diagInterpolant Q j u.toH1Function).memL2_normalizedCubeMeasure.sub
      (projection_memLp Q j u.toH1Function.toFun 2)
  have heq : (fun x => f x-g x) = (u.toH1Function-diagInterpolant Q j u.toH1Function).toFun := by
    funext x
    simp only [H1Function.sub_toFun]
    dsimp only [f, g]
    ring
  have h := diagEnergy_sub_le Q hf hg ht
  rw [heq] at h
  have ha := mul_le_mul_of_nonneg_left (diagTiledFluctuation_L2_energy_le Q j u.toH1Function)
    (show 0 ≤ 1+t by positivity)
  have hb := mul_le_mul_of_nonneg_left (diagInterpolant_h10_mean_L2_energy_le Q j u)
    (show 0 ≤ 1+t⁻¹ by positivity)
  apply (h.trans (add_le_add ha hb)).trans_eq
  dsimp only [t]
  rw [inv_inv]
  field_simp [diagPlanarC0_pos.ne']
  ring

end

end ASDExplicitGamma.Triadic
