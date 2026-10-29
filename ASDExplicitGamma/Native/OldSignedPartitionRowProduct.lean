module

public import ASDExplicitGamma.Native.OldSignedDescendantMinkowski
public import ASDExplicitGamma.Native.OldSignedPartitionEnergy
public import ASDExplicitGamma.Native.OldSignedRowProductBounds

/-! Sharp joint covariance row estimate over a finite descendant partition.
Value and derivative energies remain averaged on the same physical family. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

/-- The physical Hilbert H1 product bound aggregated over all coordinates
and cells. The cell length is exactly the descendant side length. -/
theorem old_signed_partition_row_h1_product_bound {H A : Type*} [Fintype A]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Q : TriadicCube 2) (j : ℕ) (b : Vec 2 → H) (hb : ContDiff ℝ 1 b)
    (u : A → HilbertH1Function (openCubeSet Q) H) {M D : ℝ} (hM : 0≤M) (hD : 0≤D)
    (hm : ∀ x,‖b x‖≤M) (hd : ∀ x,(∑ i,‖(fderiv ℝ b x) (basisVec i)‖^2)≤D^2) :
    Real.sqrt (descendantsAverage Q j (fun U => ∑ a,
      hilbertPositiveHaarNorm U (Real.sqrt 3) (fun x => inner ℝ (b x) ((u a).toFun x))^2))≤
      (M+(cubeScaleFactor Q/(3:ℝ)^j)*planarC1*D)*
        Real.sqrt (∑ a,hilbertEnergy Q (u a).toFun)+
      (cubeScaleFactor Q/(3:ℝ)^j)*planarC1*M*
        Real.sqrt (∑ a,hilbertGradientEnergy Q (u a).grad) := by
  classical
  let r := cubeScaleFactor Q/(3:ℝ)^j
  let E : TriadicCube 2 → ℝ := fun U => ∑ a,hilbertEnergy U (u a).toFun
  let G : TriadicCube 2 → ℝ := fun U => ∑ a,hilbertGradientEnergy U (u a).grad
  let c : TriadicCube 2 → ℝ := fun U => Real.sqrt (∑ a,
    hilbertPositiveHaarNorm U (Real.sqrt 3) (fun x => inner ℝ (b x) ((u a).toFun x))^2)
  have hr : 0≤r*planarC1 := mul_nonneg
    (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity)) (Real.sqrt_nonneg _)
  have hE U : 0≤E U := Finset.sum_nonneg (fun a _ => hilbertEnergy_nonneg U _)
  have hG U : 0≤G U := Finset.sum_nonneg (fun a _ =>
    Finset.sum_nonneg (fun k _ => hilbertEnergy_nonneg U _))
  have hcell U (hU : U ∈ descendantsAtDepth Q j) :
      c U≤(M+r*planarC1*D)*Real.sqrt (E U)+r*planarC1*M*Real.sqrt (G U) := by
    let ur (a : A) : HilbertH1Function (openCubeSet U) H := (u a).restrict
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) (isOpen_openCubeSet Q).measurableSet
    have ht := old_signed_finite_sqrt_energy_bound
      (fun a => hilbertEnergy U (ur a).toFun)
      (fun a => hilbertGradientEnergy U (ur a).grad)
      (fun a => hilbertPositiveHaarNorm U (Real.sqrt 3)
        (fun x => inner ℝ (b x) ((ur a).toFun x)))
      (add_nonneg hM (mul_nonneg
        (mul_nonneg (Triadic.cubeScaleFactor_pos' U).le (Real.sqrt_nonneg _)) hD))
      (mul_nonneg (mul_nonneg (Triadic.cubeScaleFactor_pos' U).le (Real.sqrt_nonneg _)) hM)
      (fun a => hilbertEnergy_nonneg U _)
      (fun a => Finset.sum_nonneg (fun k _ => hilbertEnergy_nonneg U _))
      (fun a => Real.sqrt_nonneg _)
      (fun a => (old_signed_row_h1_product_bound U b hb (ur a) hM hD
        (Filter.Eventually.of_forall hm) (Filter.Eventually.of_forall hd)).2)
    simpa only [ur,HilbertH1Function.restrict,cubeScaleFactor_descendant_eq_div_pow hU,
      hilbertL2Norm,r,E,G,c,planarC1] using ht
  have hh := old_signed_descendant_sqrt_energy_bound Q j E G c
    (add_nonneg hM (mul_nonneg hr hD)) (mul_nonneg hr hM)
    (fun U _ => hE U) (fun U _ => hG U) (fun U _ => Real.sqrt_nonneg _) hcell
  dsimp only [E,G,c] at hh
  simp_rw [Real.sq_sqrt (Finset.sum_nonneg (fun a _ => sq_nonneg _))] at hh
  rw [old_signed_hilbert_coordinate_energy_partition Q j _ (fun a => (u a).memL2_normalized Q),
    old_signed_hilbert_gradient_energy_partition] at hh
  exact hh

end
end ASDExplicitGamma.Native
