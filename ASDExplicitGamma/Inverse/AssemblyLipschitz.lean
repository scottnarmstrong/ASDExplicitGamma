module

public import ASDExplicitGamma.Triadic.SensitivityPathCoefficient
public import ASDExplicitGamma.Inverse.SensitivityAssembly

/-! Lipschitz representatives retaining the quantitative parent gradient bound. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open scoped ENNReal
open Set
noncomputable section

private theorem sensitivity_rawMeasure_eq_normalized (Q : TriadicCube 2) :
    volume.restrict (openCubeSet Q) =
      ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
  rw [normalizedCubeMeasure, cubeMeasure, smul_smul]
  have hcoeff : ENNReal.ofReal (cubeVolume Q) *
      ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (cubeVolume_pos Q).le]
    rw [mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)), ENNReal.ofReal_one]
  rw [hcoeff, one_smul]
  exact (volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q).symm

private theorem sensitivity_planarNorm_memLp_top (Q : TriadicCube 2)
    (b : PlanarW1Infinity Q) :
    MemLp (fun x => planarEuclideanNorm (planarW1Value b x)) ⊤
      (normalizedCubeMeasure Q) := by
  let C : ℝ := lpNorm (fun x => (b.component 0).toFun x) ⊤
        (normalizedCubeMeasure Q) +
      lpNorm (fun x => (b.component 1).toFun x) ⊤
        (normalizedCubeMeasure Q)
  have hC0 : 0 ≤ lpNorm (fun x => (b.component 0).toFun x) ⊤
      (normalizedCubeMeasure Q) := lpNorm_nonneg
  have hC1 : 0 ≤ lpNorm (fun x => (b.component 1).toFun x) ⊤
      (normalizedCubeMeasure Q) := lpNorm_nonneg
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ‖planarEuclideanNorm (planarW1Value b x)‖ ≤ C := by
    have h0 := ae_le_lpNorm_exponent_top (b.component_memLp_top 0)
    have h1 := ae_le_lpNorm_exponent_top (b.component_memLp_top 1)
    filter_upwards [h0, h1] with x hx0 hx1
    have hx0' : |(b.component 0).toFun x| ≤
        lpNorm (fun y => (b.component 0).toFun y) ⊤
          (normalizedCubeMeasure Q) := by
      simpa [Real.norm_eq_abs] using hx0
    have hx1' : |(b.component 1).toFun x| ≤
        lpNorm (fun y => (b.component 1).toFun y) ⊤
          (normalizedCubeMeasure Q) := by
      simpa [Real.norm_eq_abs] using hx1
    have hs0 : ((b.component 0).toFun x) ^ 2 ≤
        (lpNorm (fun y => (b.component 0).toFun y) ⊤
          (normalizedCubeMeasure Q)) ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg _) hC0).2 hx0'
      simpa [sq_abs] using hs
    have hs1 : ((b.component 1).toFun x) ^ 2 ≤
        (lpNorm (fun y => (b.component 1).toFun y) ⊤
          (normalizedCubeMeasure Q)) ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg _) hC1).2 hx1'
      simpa [sq_abs] using hs
    have hsum : (planarEuclideanNorm (planarW1Value b x)) ^ 2 ≤ C ^ 2 := by
      unfold planarEuclideanNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (planarW1Value b x i))]
      dsimp [planarW1Value, C]
      simp only [Fin.sum_univ_two]
      nlinarith [hs0, hs1, mul_nonneg hC0 hC1]
    have hnonneg : 0 ≤ planarEuclideanNorm (planarW1Value b x) :=
      Real.sqrt_nonneg _
    have hC' : 0 ≤ C := hC
    have hle := (sq_le_sq₀ hnonneg hC').mp hsum
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact hle
  exact MemLp.of_bound (b.valueNorm_aestronglyMeasurable) C hbound

private theorem sensitivity_planarNorm_ae_le (Q : TriadicCube 2)
    (b : PlanarW1Infinity Q) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,
      planarEuclideanNorm (planarW1Value b x) ≤ planarW1ValueLInf b := by
  have hmem := sensitivity_planarNorm_memLp_top Q b
  have h := ae_le_lpNorm_exponent_top hmem
  filter_upwards [h] with x hx
  have hnonneg : 0 ≤ planarEuclideanNorm (planarW1Value b x) := Real.sqrt_nonneg _
  change ‖planarEuclideanNorm (planarW1Value b x)‖ ≤ _ at hx
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hx
  simpa [planarW1ValueLInf, lpNorm] using hx

private theorem sensitivity_vecNorm_le_planarNorm (v : Vec 2) :
    ‖v‖ ≤ planarEuclideanNorm v := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  rw [Real.norm_eq_abs]
  have hsum : (v i) ^ 2 ≤ ∑ j : Fin 2, v j ^ 2 :=
    Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 2 => v j ^ 2)
      (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hsq : |v i| ^ 2 ≤ (planarEuclideanNorm v) ^ 2 := by
    rw [planarEuclideanNorm, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg (v j))]
    simpa [sq_abs] using hsum
  exact (sq_le_sq₀ (abs_nonneg (v i)) (Real.sqrt_nonneg _)).mp hsq

private noncomputable def sensitivityTruncatedGradient {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) (K : ℝ) : Vec 2 → Vec 2 :=
  fun x => if ‖h.value.grad x‖ ≤ K then h.value.grad x else 0

private theorem sensitivityTruncatedGradient_bound {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) {K : ℝ} (hK : 0 ≤ K) (x : Vec 2) :
    ‖sensitivityTruncatedGradient h K x‖ ≤ K := by
  by_cases hx : ‖h.value.grad x‖ ≤ K
  · simp [sensitivityTruncatedGradient, hx]
  · simp [sensitivityTruncatedGradient, hx, hK]

private theorem sensitivityTruncatedGradient_ae_eq {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    h.value.grad =ᵐ[volume.restrict (openCubeSet Q)]
      sensitivityTruncatedGradient h (planarGradientLInf h) := by
  have hK : 0 ≤ planarGradientLInf h := by
    unfold planarGradientLInf planarW1ValueLInf
    exact ENNReal.toReal_nonneg
  have hbound := sensitivity_planarNorm_ae_le Q h.gradient
  have hvol : ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      planarEuclideanNorm (h.value.grad x) ≤ planarGradientLInf h := by
    rw [sensitivity_rawMeasure_eq_normalized Q]
    refine MeasureTheory.Measure.ae_smul_measure ?_ (ENNReal.ofReal (cubeVolume Q))
    filter_upwards [hbound] with x hx
    have heq : planarEuclideanNorm (planarW1Value h.gradient x) =
        planarEuclideanNorm (h.value.grad x) := by
      congr 1
      funext i
      exact congrFun (h.gradient_eq i) x
    simpa [planarGradientLInf] using heq ▸ hx
  filter_upwards [hvol] with x hx
  have hnorm : ‖h.value.grad x‖ ≤ planarEuclideanNorm (h.value.grad x) :=
    sensitivity_vecNorm_le_planarNorm _
  have hle : ‖h.value.grad x‖ ≤ planarGradientLInf h := hnorm.trans hx
  simp [sensitivityTruncatedGradient, hle]

private theorem sensitivityTruncatedGradient_hasWeakGradient {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    HasWeakGradientOn (openCubeSet Q) h.value.toFun
      (sensitivityTruncatedGradient h (planarGradientLInf h)) := by
  intro i φ hφsmooth hφcompact hφsupport
  have hae := sensitivityTruncatedGradient_ae_eq h
  have hae_i : ∀ᵐ x ∂volume,
      x ∈ openCubeSet Q →
        sensitivityTruncatedGradient h (planarGradientLInf h) x i =
          h.value.grad x i := by
    rw [← ae_restrict_iff' (measurableSet_openCubeSet Q)]
    filter_upwards [hae] with x hx
    exact congrArg (fun v : Vec 2 => v i) hx.symm
  calc
    ∫ x in openCubeSet Q, h.value.toFun x *
        (fderiv ℝ φ x) (basisVec i) ∂volume =
      -∫ x in openCubeSet Q, h.value.grad x i * φ x ∂volume :=
        h.value.hasWeakGradient i φ hφsmooth hφcompact hφsupport
    _ = -∫ x in openCubeSet Q,
        sensitivityTruncatedGradient h (planarGradientLInf h) x i * φ x ∂volume := by
      congr 1
      symm
      apply setIntegral_congr_ae (measurableSet_openCubeSet Q)
      filter_upwards [hae_i] with x hx
      intro hxU
      rw [hx hxU]

/-- A parent W^{2,∞} direction has a global Lipschitz representative with its
explicit gradient constant retained, for comparison of descendant means. -/
theorem assembly_W2_lipschitz_representative {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    ∃ r : Vec 2 → ℝ, LipschitzWith (Real.toNNReal (2*planarGradientLInf h)) r ∧
      h.value.toFun =ᵐ[volume.restrict (openCubeSet Q)] r := by
  let K := planarGradientLInf h
  have hK : 0 ≤ K := by
    unfold K planarGradientLInf planarW1ValueLInf
    exact ENNReal.toReal_nonneg
  obtain ⟨r, hrLip, hrAE⟩ :=
    Algsuperdiff.Section5.Support.exists_lipschitzWith_representative_of_hasWeakGradientOn
      (d := 2) (V := openCubeSet Q)
      (isOpenBoundedConvexDomain_openCubeSet Q)
      (Book.Ch02.openCubeSet_nonempty Q) hK h.value.memL2
      (fun i => by
        have hae := sensitivityTruncatedGradient_ae_eq h
        have hcoord : (fun x => sensitivityTruncatedGradient h K x i) =ᵐ[
            volume.restrict (openCubeSet Q)] fun x => h.value.grad x i := by
          filter_upwards [hae] with x hx
          exact congrArg (fun v : Vec 2 => v i) hx.symm
        exact (memLp_congr_ae hcoord).mpr (h.value.gradMemL2 i))
      (sensitivityTruncatedGradient_hasWeakGradient h)
      (sensitivityTruncatedGradient_bound h hK)
  exact ⟨r,hrLip,hrAE⟩

end
end ASDExplicitGamma.Inverse
