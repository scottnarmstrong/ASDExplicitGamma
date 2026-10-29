module

public import ASDExplicitGamma.Variational.LemmaVH1
public import ASDExplicitGamma.Triadic.PlanarDirichletBridge

/-! Convexity and localization of the Haar norms used in Lemma V. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Triadic

noncomputable section

/-- Projections depend only on the field's equivalence class on the cube. -/
theorem lemmaV_cubeProjection_congr_ae {d : ℕ} (Q : TriadicCube d) (k : ℕ)
    {f g : Vec d → ℝ} (hfg : f =ᵐ[volume.restrict (cubeSet Q)] g) :
    cubeProjection Q k f = cubeProjection Q k g := by
  have havg (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q k) :
      cubeAverage R f = cubeAverage R g := by
    unfold cubeAverage
    congr 1
    apply integral_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset
      (cubeSet_subset_of_mem_descendantsAtDepth hR) hfg
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR, havg R hR]
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q k f hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q k g hx]

/-- L² energy is convex under taking midpoints. -/
theorem lemmaV_energy_midpoint_le {d : ℕ} (Q : TriadicCube d) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => (f x + g x) / 2) ≤ (energy Q f + energy Q g) / 2 := by
  have hmid : MemLp (fun x => (f x + g x) / 2) 2 (normalizedCubeMeasure Q) := by
    convert (hf.add hg).const_smul (1 / 2 : ℝ) using 1
    funext x
    change (f x + g x) / 2 = (1 / 2 : ℝ) * (f x + g x)
    ring
  unfold energy pairing
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure]
  have hsum := integral_add (hf.integrable_mul hf) (hg.integrable_mul hg)
  simp only [Pi.mul_apply] at hsum
  rw [← hsum, ← integral_div]
  apply integral_mono_ae (hmid.integrable_mul hmid)
    (((hf.integrable_mul hf).add (hg.integrable_mul hg)).div_const 2)
  filter_upwards with x
  change ((f x + g x) / 2) * ((f x + g x) / 2) ≤ (f x * f x + g x * g x) / 2
  nlinarith only [sq_nonneg (f x - g x)]

/-- Midpoint convexity of negative Haar energy, including its mean term. -/
theorem lemmaV_dualEnergy_midpoint_le {d : ℕ} (Q : TriadicCube d) {q : ℝ}
    (hq : 1 < q) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    dualEnergy Q q (fun x => (f x + g x) / 2) ≤
      (dualEnergy Q q f + dualEnergy Q q g) / 2 := by
  let mid : Vec d → ℝ := fun x => (f x + g x) / 2
  have hmid : MemLp mid 2 (normalizedCubeMeasure Q) := by
    convert (hf.add hg).const_smul (1 / 2 : ℝ) using 1
    funext x
    change (f x + g x) / 2 = (1 / 2 : ℝ) * (f x + g x)
    ring
  have hproj (k : ℕ) : cubeProjection Q k mid =
      fun x => (cubeProjection Q k f x + cubeProjection Q k g x) / 2 := by
    have heq : mid = (fun x => (1 / 2 : ℝ) * (f x + g x)) := by
      funext x
      simp [mid, div_eq_mul_inv, mul_comm]
    rw [heq, projection_smul, projection_add Q k hf hg]
    funext x
    simp only [div_eq_mul_inv]
    ring
  have hp (k : ℕ) : energy Q (cubeProjection Q k mid) ≤
      (energy Q (cubeProjection Q k f) + energy Q (cubeProjection Q k g)) / 2 := by
    rw [hproj]
    exact lemmaV_energy_midpoint_le Q (projection_memLp Q k f 2) (projection_memLp Q k g 2)
  have hsF := summable_weighted_projections Q hq hf
  have hsG := summable_weighted_projections Q hq hg
  have hw : 0 ≤ q⁻¹ := inv_nonneg.mpr (le_trans zero_le_one hq.le)
  have hw1 : 0 ≤ 1 - q⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hq.le)
  change dualEnergy Q q mid ≤ _
  rw [dualEnergy_eq Q hq hmid, dualEnergy_eq Q hq hf, dualEnergy_eq Q hq hg]
  calc
    (1 - q⁻¹) * ∑' k, (q⁻¹) ^ k * energy Q (cubeProjection Q k mid) ≤
        (1 - q⁻¹) * ∑' k, ((q⁻¹) ^ k * energy Q (cubeProjection Q k f) +
          (q⁻¹) ^ k * energy Q (cubeProjection Q k g)) / 2 := by
      apply mul_le_mul_of_nonneg_left _ hw1
      apply (summable_weighted_projections Q hq hmid).tsum_le_tsum _
        ((hsF.add hsG).div_const 2)
      intro k
      calc
        _ ≤ (q⁻¹) ^ k * ((energy Q (cubeProjection Q k f) +
            energy Q (cubeProjection Q k g)) / 2) :=
          mul_le_mul_of_nonneg_left (hp k) (pow_nonneg hw k)
        _ = _ := by ring
    _ = _ := by
      rw [tsum_div_const, hsF.tsum_add hsG]
      ring

/-- Negative Haar energy is insensitive to null-set changes. -/
theorem lemmaV_dualEnergy_congr_ae {d : ℕ} (Q : TriadicCube d) {q : ℝ}
    (hq : 1 < q) {f g : Vec d → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hfg : f =ᵐ[volume.restrict (cubeSet Q)] g) :
    dualEnergy Q q f = dualEnergy Q q g := by
  rw [dualEnergy_eq Q hq hf, dualEnergy_eq Q hq hg]
  simp only [lemmaV_cubeProjection_congr_ae Q _ hfg]

/-- Vector weak Haar energy of the midpoint of two H¹ gradients. The
midpoint identity is needed only almost everywhere. -/
theorem lemmaV_vectorWeakHaarEnergy_midpoint_le {d : ℕ} (Q : TriadicCube d)
    (v f g : H1Function (openCubeSet Q))
    (hmid : v.grad =ᵐ[volume.restrict (openCubeSet Q)]
      fun x i => (f.grad x i + g.grad x i) / 2) :
    vectorWeakHaarEnergy Q v.grad ≤
      (vectorWeakHaarEnergy Q f.grad + vectorWeakHaarEnergy Q g.grad) / 2 := by
  have hq : 1 < Real.sqrt 3 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 3)
    simpa using h
  have hc (i : Fin d) : dualEnergy Q (Real.sqrt 3) (fun x => v.grad x i) ≤
      (dualEnergy Q (Real.sqrt 3) (fun x => f.grad x i) +
        dualEnergy Q (Real.sqrt 3) (fun x => g.grad x i)) / 2 := by
    have hm : MemLp (fun x => (f.grad x i + g.grad x i) / 2) 2 (normalizedCubeMeasure Q) := by
      convert ((f.grad_memL2_normalizedCubeMeasure i).add
        (g.grad_memL2_normalizedCubeMeasure i)).const_smul (1 / 2 : ℝ) using 1
      funext x
      change (f.grad x i + g.grad x i) / 2 = (1 / 2 : ℝ) * (f.grad x i + g.grad x i)
      ring
    have heq : (fun x => v.grad x i) =ᵐ[volume.restrict (cubeSet Q)]
        (fun x => (f.grad x i + g.grad x i) / 2) := by
      rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
      exact hmid.mono fun x hx => congrFun hx i
    rw [lemmaV_dualEnergy_congr_ae Q hq (v.grad_memL2_normalizedCubeMeasure i) hm heq]
    exact lemmaV_dualEnergy_midpoint_le Q hq (f.grad_memL2_normalizedCubeMeasure i)
      (g.grad_memL2_normalizedCubeMeasure i)
  unfold vectorWeakHaarEnergy
  calc
    _ ≤ ∑ i, (dualEnergy Q (Real.sqrt 3) (fun x => f.grad x i) +
        dualEnergy Q (Real.sqrt 3) (fun x => g.grad x i)) / 2 :=
      Finset.sum_le_sum fun i _ => hc i
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]

end

end ASDExplicitGamma.Variational
