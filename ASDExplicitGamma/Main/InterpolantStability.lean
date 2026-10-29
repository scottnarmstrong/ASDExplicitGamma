module

public import ASDExplicitGamma.Main.InterpolantContraction
public import ASDExplicitGamma.Variational.AffinePotentialSpace
public import Homogenization.Sobolev.MatchedPair.Core

/-! Global H¹ stability bounds for the actual source DIAG interpolant. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators

local instance mainInterpolantStabilityFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem main_h1_gradient_energy_identity (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) :
    ‖u.gradToHilbertVectorL2‖ ^ 2 = cubeVolume Q *
      ∑ i : Fin 2, energy Q (fun x => u.grad x i) := by
  have hinner := inner_toHilbertVectorL2OfVecField_eq_integral
    (U := openCubeSet Q) u.grad_memVectorL2 u.grad_memVectorL2
  have hnorm : ‖u.gradToHilbertVectorL2‖ ^ 2 =
      ∫ x in openCubeSet Q, vecDot (u.grad x) (u.grad x) ∂volume := by
    rw [← hinner]
    exact (real_inner_self_eq_norm_sq _).symm
  have hdot : (fun x => vecDot (u.grad x) (u.grad x)) =
      fun x => ∑ i : Fin 2, (u.grad x i) ^ 2 := by
    funext x
    simp [Homogenization.vecDot, Fin.sum_univ_two, pow_two]
  rw [hnorm, hdot, integral_finsetSum]
  · have hi (i : Fin 2) :
        ∫ x in openCubeSet Q, (u.grad x i) ^ 2 ∂volume =
          cubeVolume Q * energy Q (fun x => u.grad x i) := by
      rw [energy_eq_integral_sq, integral_normalized_eq_open]
      have hvol : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
      field_simp
    rw [Finset.sum_congr rfl (fun i _ => hi i), ← Finset.mul_sum]
  · intro i hi
    convert (u.grad_memL2 i).integrable_mul (u.grad_memL2 i) using 1
    funext x
    simp only [Pi.mul_apply, pow_two]

theorem main_h1_value_energy_identity (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) :
    ‖u.toScalarL2‖ ^ 2 = cubeVolume Q * energy Q u.toFun := by
  rw [l2_normSq_eq_integral, energy_eq_integral_sq,
    integral_normalized_eq_open]
  have hvol : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  field_simp

theorem main_energy_const_add_mean_zero (Q : TriadicCube 2) (c : ℝ)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hmean : cubeAverage Q f = 0) :
    energy Q (fun x => c+f x) = c^2 + energy Q f := by
  have hmeanSum : cubeAverage Q (fun x => c+f x) = c := by
    have heq : (fun x => c+f x) = fun x => f x-(-c) := by
      funext x
      ring
    rw [heq, cubeAverage_sub_const_of_memLp_two Q hf, hmean]
    ring
  have hsubfun : (fun x => (c+f x)-c) = f := by
    funext x
    ring
  have hsum : MemLp (fun x => c+f x) 2 (normalizedCubeMeasure Q) :=
    (memLp_const c).add hf
  have h := energy_sub Q hsum (memLp_const c)
  rw [hsubfun, pairing_const_right, hmeanSum, energy_const] at h
  linarith

private theorem dualEnergy_le_energy {d : ℕ} (Q : TriadicCube d) {q : ℝ}
    (hq : 1 < q) {f : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    dualEnergy Q q f ≤ energy Q f := by
  let r := q⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr (by linarith only [hq.le])
  have hr1 : r < 1 := by
    dsimp [r]
    exact (inv_lt_one₀ (by linarith only [hq])).2 hq
  have hc : 0 ≤ 1-r := sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le)
  have hgeom : (∑' k : ℕ, r^k) = (1-r)⁻¹ :=
    tsum_geometric_of_lt_one hr0 hr1
  rw [dualEnergy_eq Q hq hf]
  have hs1 := summable_weighted_projections Q hq hf
  have hs2 := (summable_geometric_of_lt_one hr0 hr1).mul_right (energy Q f)
  have hsum : (∑' k : ℕ, r^k * energy Q (cubeProjection Q k f)) ≤
      energy Q f * (∑' k : ℕ, r^k) := by
    have hterm : ∀ k : ℕ, r^k * energy Q (cubeProjection Q k f) ≤
        r^k * energy Q f := by
      intro k
      exact mul_le_mul_of_nonneg_left (energy_projection_le Q k hf) (pow_nonneg hr0 k)
    calc
      _ ≤ ∑' k : ℕ, r^k * energy Q f := hs1.tsum_le_tsum hterm hs2
      _ = energy Q f * (∑' k : ℕ, r^k) := by
        rw [show (fun k : ℕ => r^k * energy Q f) = fun k => energy Q f * r^k by
          funext k; ring, tsum_mul_left]
  calc
    (1-r) * (∑' k : ℕ, r^k * energy Q (cubeProjection Q k f)) ≤
        (1-r) * (energy Q f * (∑' k : ℕ, r^k)) := mul_le_mul_of_nonneg_left hsum hc
    _ = energy Q f := by
      rw [hgeom]
      have hrne : 1-r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
      field_simp

theorem main_tiledWeak_le_gradient_energy (Q : TriadicCube 2) (j : ℕ)
    (u : H1Function (openCubeSet Q)) :
    lemmaVTiledWeakEnergy Q j u.grad ≤
      ∑ i : Fin 2, energy Q (fun x => u.grad x i) := by
  have hq : 1 < Real.sqrt 3 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1) (by norm_num : (1:ℝ)<3)
    simpa using h
  change descendantsAverage Q j
      (fun R => ∑ i : Fin 2, dualEnergy R (Real.sqrt 3) (fun x => u.grad x i)) ≤ _
  rw [descendantsAverage_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [energy_eq_descendantsAverage Q j (u.grad_memL2_normalizedCubeMeasure i)]
  unfold descendantsAverage
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro R hR
  exact dualEnergy_le_energy R hq
    (u.grad_memL2_normalizedCubeMeasure_of_mem_descendantsAtDepth hR i)

theorem main_interpolant_global_gradient_energy_le (Q : TriadicCube 2) (j : ℕ)
    (u : H10Function (openCubeSet Q)) :
    (∑ i : Fin 2, energy Q (fun x => (diagInterpolant Q j u.toH1Function).grad x i)) ≤
      lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j u.toH1Function).grad := by
  have hcoord (i : Fin 2) : energy Q (fun x => (diagInterpolant Q j u.toH1Function).grad x i) ≤
      descendantsAverage Q j (fun R => primalEnergy R (Real.sqrt 3)
        (fun x => (diagInterpolant Q j u.toH1Function).grad x i)) := by
    rw [energy_eq_descendantsAverage Q j
      ((diagInterpolant Q j u.toH1Function).grad_memL2_normalizedCubeMeasure i)]
    unfold descendantsAverage
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro R hR
    let k := (diagMeshCellEquiv Q j).symm ⟨R,hR⟩
    have hcell : diagMeshCell Q j k = R := congrArg Subtype.val
      ((diagMeshCellEquiv Q j).apply_symm_apply ⟨R,hR⟩)
    rw [← hcell]
    rw [diagEnergy_congr_ae _ (diagInterpolant_h10_cell_grad_ae Q j u k i),
      diagPrimalEnergy_congr_ae _ _ (diagInterpolant_h10_cell_grad_ae Q j u k i)]
    convert diagH1_energy_le_primalEnergy (diagMeshCell Q j k)
      (diagBilinearH1 (diagMeshCell Q j k)
        (diagBilinearDerivativeCoefficients (diagMeshCell Q j k)
          (diagSourceCellCoefficients Q j u.toH1Function k) i)) using 1
    · simp only [diagBilinearH1_toFun, diagBilinearH1_grad_polynomial]
    · simp only [diagBilinearH1_toFun, diagBilinearH1_grad_polynomial]
  change (∑ i : Fin 2, energy Q (fun x => (diagInterpolant Q j u.toH1Function).grad x i)) ≤
    descendantsAverage Q j (fun R => ∑ i : Fin 2, primalEnergy R (Real.sqrt 3)
      (fun x => (diagInterpolant Q j u.toH1Function).grad x i))
  rw [Triadic.descendantsAverage_sum]
  exact Finset.sum_le_sum fun i _ => hcoord i

theorem main_diag_interpolant_stability (Q : TriadicCube 2) (j : ℕ) :
    (∀ v ∈ affinePotentialSubmodule Q,
      ‖(diagInterpolant Q j v).gradToHilbertVectorL2‖ ≤ ‖v.gradToHilbertVectorL2‖) ∧
    (∀ v ∈ affinePotentialSubmodule Q,
      ‖(v-diagInterpolant Q j v).toScalarL2‖ ≤
        diagMeshRadius Q j*(planarC0+1/2)*‖v.gradToHilbertVectorL2‖) := by
  constructor
  · intro v hv
    rw [affinePotentialSubmodule, Submodule.mem_sup] at hv
    rcases hv with ⟨a, ha, b, hb, hab⟩
    rcases ha with ⟨p, rfl⟩
    rcases hb with ⟨r, hr⟩
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let w := lemmaVAffinePotential hU p r
    have hvw : v = w := by
      have hab' : diagAffineLinear Q p + r.toH1Function = v := by
        rw [← hr] at hab
        exact hab
      change v = diagAffineLinear Q p + r.toH1Function
      rw [hab'.symm]
    rw [hvw]
    have hout := main_interpolant_global_gradient_energy_le Q j r
    have hcontract := main_interpolant_energy_contraction Q j p r
    have hweak := main_tiledWeak_le_gradient_energy Q j r.toH1Function
    have hinput :
        (∑ i : Fin 2, energy Q (fun x => p i + r.toH1Function.grad x i)) =
          ∑ i : Fin 2, (p i^2 + energy Q (fun x => r.toH1Function.grad x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact main_energy_const_add_mean_zero Q (p i)
        (r.toH1Function.grad_memL2_normalizedCubeMeasure i)
        (cubeAverage_h10_gradient_eq_zero Q r i)
    have hweakAffine : lemmaVTiledWeakEnergy Q j w.grad =
        ∑ i : Fin 2, p i^2 + lemmaVTiledWeakEnergy Q j r.toH1Function.grad := by
      simpa [w] using diagTiledWeakEnergy_affinePotential Q j p r
    have hsplit :
        lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j w).grad ≤
          ∑ i : Fin 2, energy Q (fun x => p i + r.toH1Function.grad x i) := by
      calc
        lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j w).grad ≤
            lemmaVTiledWeakEnergy Q j w.grad := by simpa [w] using hcontract
        _ = (∑ i : Fin 2, p i^2) + lemmaVTiledWeakEnergy Q j r.toH1Function.grad := hweakAffine
        _ ≤ (∑ i : Fin 2, p i^2) + ∑ i : Fin 2, energy Q (fun x => r.toH1Function.grad x i) := by
              simpa [add_comm] using add_le_add_right hweak (∑ i : Fin 2, p i^2)
        _ = ∑ i : Fin 2, energy Q (fun x => p i + r.toH1Function.grad x i) := by
              rw [hinput]
              simp [Finset.sum_add_distrib]
    have hglobalAffine :
        (∑ i : Fin 2, energy Q (fun x => (diagInterpolant Q j w).grad x i)) =
          (∑ i : Fin 2, p i^2) +
            ∑ i : Fin 2, energy Q (fun x => (diagInterpolant Q j r.toH1Function).grad x i) := by
      rw [diagInterpolant_affinePotential]
      have hmean (i : Fin 2) : cubeAverage Q
          (fun x => (diagInterpolant Q j r.toH1Function).grad x i) = 0 :=
        diagH1_mean_gradient_zero Q (diagInterpolant Q j r.toH1Function)
          (diagInterpolant_h10_memH10 Q j r) i
      have hcoord (i : Fin 2) :
          energy Q (fun x => (diagAffineLinear Q p + diagInterpolant Q j r.toH1Function).grad x i) =
            p i^2 + energy Q (fun x => (diagInterpolant Q j r.toH1Function).grad x i) := by
        have hfun : (fun x => (diagAffineLinear Q p +
            diagInterpolant Q j r.toH1Function).grad x i) =
            fun x => p i + (diagInterpolant Q j r.toH1Function).grad x i := by
          funext x
          simp [diagAffineLinear, H1Function.add_grad]
        rw [hfun]
        exact main_energy_const_add_mean_zero Q (p i)
          ((diagInterpolant Q j r.toH1Function).grad_memL2_normalizedCubeMeasure i) (hmean i)
      calc
        _ = ∑ i : Fin 2, (p i^2 + energy Q (fun x =>
            (diagInterpolant Q j r.toH1Function).grad x i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hcoord i
        _ = _ := by rw [Finset.sum_add_distrib]
    have hpositiveAffine :
        lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j w).grad =
          (∑ i : Fin 2, p i^2) +
            lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j r.toH1Function).grad := by
      simpa [w] using diagTiledPositiveEnergy_affineInterpolant Q j p r
    have hglobal :
        (∑ i : Fin 2, energy Q (fun x => (diagInterpolant Q j w).grad x i)) ≤
          lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j w).grad := by
      rw [hglobalAffine, hpositiveAffine]
      exact add_le_add_right hout _
    have hroot := hglobal.trans hsplit
    have hnormOut := main_h1_gradient_energy_identity Q (diagInterpolant Q j w)
    have hnormIn := main_h1_gradient_energy_identity Q w
    have hcube := cubeVolume_pos Q
    have hsquare : ‖(diagInterpolant Q j w).gradToHilbertVectorL2‖ ^ 2 ≤
        ‖w.gradToHilbertVectorL2‖ ^ 2 := by
      rw [hnormOut, hnormIn]
      exact mul_le_mul_of_nonneg_left hroot hcube.le
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsquare
  · intro v hv
    rw [affinePotentialSubmodule, Submodule.mem_sup] at hv
    rcases hv with ⟨a, ha, b, hb, hab⟩
    rcases ha with ⟨p, rfl⟩
    rcases hb with ⟨r, hr⟩
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let w := lemmaVAffinePotential hU p r
    have hvw : v = w := by
      have hab' : diagAffineLinear Q p + r.toH1Function = v := by
        rw [← hr] at hab
        exact hab
      change v = diagAffineLinear Q p + r.toH1Function
      rw [hab'.symm]
    rw [hvw]
    have hres := diagInterpolant_residual_L2_energy_le Q j p r
    have hweak := main_tiledWeak_le_gradient_energy Q j r.toH1Function
    have hinput :
        (∑ i : Fin 2, energy Q (fun x => p i + r.toH1Function.grad x i)) =
          ∑ i : Fin 2, (p i^2 + energy Q (fun x => r.toH1Function.grad x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact main_energy_const_add_mean_zero Q (p i)
        (r.toH1Function.grad_memL2_normalizedCubeMeasure i)
        (cubeAverage_h10_gradient_eq_zero Q r i)
    have hweakAffine : lemmaVTiledWeakEnergy Q j w.grad =
        ∑ i : Fin 2, p i^2 + lemmaVTiledWeakEnergy Q j r.toH1Function.grad := by
      simpa [w] using diagTiledWeakEnergy_affinePotential Q j p r
    have hroot : lemmaVTiledWeakEnergy Q j w.grad ≤
        ∑ i : Fin 2, energy Q (fun x => p i + r.toH1Function.grad x i) := by
      rw [hweakAffine]
      calc
        (∑ i : Fin 2, p i^2) + lemmaVTiledWeakEnergy Q j r.toH1Function.grad ≤
            (∑ i : Fin 2, p i^2) + ∑ i : Fin 2, energy Q (fun x => r.toH1Function.grad x i) :=
              by simpa [add_comm] using add_le_add_right hweak (∑ i : Fin 2, p i^2)
        _ = ∑ i : Fin 2, energy Q (fun x => p i + r.toH1Function.grad x i) := by
              rw [hinput]
              simp [Finset.sum_add_distrib]
    have hresenergy : energy Q (w-diagInterpolant Q j w).toFun ≤
        diagMeshRadius Q j^2*(planarC0+1/2)^2 *
          (∑ i : Fin 2, energy Q (fun x => w.grad x i)) := by
      have hres' : energy Q (w-diagInterpolant Q j w).toFun ≤
          diagMeshRadius Q j^2*(planarC0+1/2)^2 * lemmaVTiledWeakEnergy Q j w.grad := by
        simpa [w] using hres
      calc
        energy Q (w-diagInterpolant Q j w).toFun ≤
            diagMeshRadius Q j^2*(planarC0+1/2)^2 * lemmaVTiledWeakEnergy Q j w.grad := hres'
        _ ≤ diagMeshRadius Q j^2*(planarC0+1/2)^2 *
            (∑ i : Fin 2, energy Q (fun x => w.grad x i)) := by
              apply mul_le_mul_of_nonneg_left hroot
              positivity
    have hnormRes := main_h1_value_energy_identity Q (w-diagInterpolant Q j w)
    have hnormIn := main_h1_gradient_energy_identity Q w
    have hcube := cubeVolume_pos Q
    have hsq : ‖(w-diagInterpolant Q j w).toScalarL2‖ ^ 2 ≤
        (diagMeshRadius Q j*(planarC0+1/2)*‖w.gradToHilbertVectorL2‖)^2 := by
      calc
        _ = cubeVolume Q * energy Q (w-diagInterpolant Q j w).toFun := hnormRes
        _ ≤ cubeVolume Q * (diagMeshRadius Q j^2*(planarC0+1/2)^2 *
            (∑ i : Fin 2, energy Q (fun x => w.grad x i))) :=
              mul_le_mul_of_nonneg_left hresenergy hcube.le
        _ = _ := by
          calc
            _ = (diagMeshRadius Q j*(planarC0+1/2))^2 *
                (cubeVolume Q * ∑ i : Fin 2, energy Q (fun x => w.grad x i)) := by ring
            _ = (diagMeshRadius Q j*(planarC0+1/2))^2 *
                ‖w.gradToHilbertVectorL2‖^2 := by rw [← hnormIn]
            _ = _ := by ring
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg (diagMeshRadius_pos Q j).le
      (add_nonneg diagPlanarC0_pos.le (by norm_num))) (norm_nonneg _))).1 hsq

end ASDExplicitGamma.Main
