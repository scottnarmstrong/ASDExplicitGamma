module

public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import ASDExplicitGamma.Triadic.DiagEnergyCongr

/-! Public weak-Haar triangle bounds for the joint actual reciprocal
loads. The weighted projection representation proves convergence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- Scalar weak-Haar triangle inequality for actual L2 fields. -/
theorem old_signed_weak_triangle (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    weakHaarNorm Q (fun x => f x+g x)≤weakHaarNorm Q f+weakHaarNorm Q g := by
  let w := (Real.sqrt 3)⁻¹
  let weight := fun n : ℕ => (1-w)*w^n
  let h := fun (u : Vec 2 → ℝ) n => Real.sqrt (weight n*energy Q (cubeProjection Q n u))
  have hroot : 1<Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hw : 0≤w := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hw1 : w≤1 := inv_le_one_of_one_le₀ hroot.le
  have hweight (n : ℕ) : 0≤weight n := mul_nonneg (sub_nonneg.mpr hw1) (pow_nonneg hw n)
  have hsq (u : Vec 2 → ℝ) (n : ℕ) : h u n^2=weight n*energy Q (cubeProjection Q n u) :=
    Real.sq_sqrt (mul_nonneg (hweight n) (energy_nonneg Q _))
  have hs (u : Vec 2 → ℝ) (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
      Summable (fun n => h u n^2) := by
    have hh := (summable_weighted_projections Q hroot hu).mul_left (1-w)
    simpa only [hsq,weight,mul_assoc] using hh
  have hid (u : Vec 2 → ℝ) (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
      weakHaarNorm Q u=Real.sqrt (∑' n,h u n^2) := by
    have hh := dualEnergy_eq_weighted_projections Q hroot hu
      (summable_weighted_projections Q hroot hu)
    unfold weakHaarNorm
    rw [hh]
    apply congrArg Real.sqrt
    simp_rw [hsq,weight,mul_assoc]
    exact (tsum_mul_left).symm
  have hp (n : ℕ) : h (fun x => f x+g x) n≤h f n+h g n := by
    have hh := hilbertL2Norm_add_le Q (projection_memLp Q n f 2) (projection_memLp Q n g 2)
    simp only [hilbertL2Norm,hilbertEnergy_real] at hh
    dsimp only [h]
    rw [projection_add Q n hf hg,Real.sqrt_mul (hweight n),
      Real.sqrt_mul (hweight n),Real.sqrt_mul (hweight n)]
    simpa only [mul_add] using mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg (weight n))
  have hh := sqrt_tsum_sq_le_of_pointwise (hs f hf) (hs g hg) (fun _ => Real.sqrt_nonneg _) hp
  rw [hid (fun x => f x+g x) (show MemLp (fun x => f x+g x) 2 (normalizedCubeMeasure Q) from hf.add hg),hid f hf,hid g hg]
  exact hh.2

/-- Vector weak-Haar triangle inequality, with actual coordinate L2 data. -/
theorem old_signed_vector_weak_triangle (Q : TriadicCube 2) {f g : Vec 2 → Vec 2}
    (hf : ∀ i : Fin 2,MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q))
    (hg : ∀ i : Fin 2,MemLp (fun x => g x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarNorm Q (fun x => f x+g x)≤vectorWeakHaarNorm Q f+vectorWeakHaarNorm Q g := by
  have hid (u : Vec 2 → Vec 2) : vectorWeakHaarNorm Q u=
      Real.sqrt (∑ i : Fin 2,weakHaarNorm Q (fun x => u x i)^2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
    change vectorWeakHaarNorm Q u^2=_
    rw [vectorWeakHaarNorm_sq,Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [hid,hid f,hid g]
  refine (Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i _ =>
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (old_signed_weak_triangle Q (hf i) (hg i)) 2))).trans ?_
  exact sqrt_finset_sq_add_le Finset.univ _ _

end
end ASDExplicitGamma.Native
