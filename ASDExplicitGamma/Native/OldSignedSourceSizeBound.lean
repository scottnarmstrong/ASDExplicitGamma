module

public import ASDExplicitGamma.Native.OldSignedSourceLoadBound

/-! Four-load spatial source control for the OLD annealed panel. The
parent first-gradient errors are the same ones used by the signed trial. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Triadic Variational
noncomputable section

/-- The actual complete source size obeys the tiled four-load k_a bound,
with no independence or assumed source estimate. -/
theorem old_signed_source_size_partition_bound (n : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    descendantsAverage Q mesh (fun U => oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L^2)≤
      oldSignedSourceMultiplier Q mesh b L^2*
        descendantsAverage Q mesh (fun U => oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k^2) := by
  classical
  intro Q
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  let g := fun (c : BlockCoord 2) (l : whiteBasisIndex) (U : TriadicCube 2) =>
    vectorPositiveHaarNorm U
      (fun x => (oldSignedOldErrorSource Q mesh a hEll b L l (blockBasis c) x).2)^2
  have hs (c : BlockCoord 2) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q mesh) :
      Summable (fun l => g c l U) :=
    old_signed_old_error_source_cell_energy_summable n mesh a hEll (blockBasis c) b L U hU
  have hsa (c : BlockCoord 2) : Summable (fun l => descendantsAverage Q mesh (g c l)) :=
    (old_signed_partition_series Q mesh (g c) (hs c)).1
  have hpart := old_signed_partition_series Q mesh
    (fun l U => ∑ c : BlockCoord 2,g c l U)
    (fun U hU => summable_sum (fun c _ => hs c U hU))
  have hd : descendantsAverage Q mesh (fun U => oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L^2)=
      ∑ c : BlockCoord 2,∑' l,descendantsAverage Q mesh (g c l) := by
    calc
      _ = descendantsAverage Q mesh (fun U => ∑' l,∑ c : BlockCoord 2,g c l U) := by
        congr 1
        funext U
        exact Real.sq_sqrt (tsum_nonneg (fun l => Finset.sum_nonneg (fun c _ => sq_nonneg _)))
      _ = ∑' l,descendantsAverage Q mesh (fun U => ∑ c : BlockCoord 2,g c l U) := hpart.2.symm
      _ = ∑' l,∑ c : BlockCoord 2,descendantsAverage Q mesh (g c l) := by
        apply tsum_congr
        intro l
        exact Homogenization.descendantsAverage_sum Q mesh Finset.univ (fun U c => g c l U)
      _ = _ := Summable.tsum_finsetSum (fun c _ => hsa c)
  let e := fun (c : BlockCoord 2) (x : Vec 2) =>
    (oldSignedCanonicalAffineField Q a hEll (blockBasis c) x).1-(blockBasis c).1
  have hb (c : BlockCoord 2) : (∑' l,descendantsAverage Q mesh (g c l))≤
      oldSignedSourceMultiplier Q mesh b L^2*lemmaVTiledWeakEnergy Q mesh (e c) :=
    old_signed_old_source_load_energy_bound n mesh a hEll (blockBasis c) b L
  rw [hd]
  apply (Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hb c)).trans_eq
  rw [← Finset.mul_sum]
  congr 1
  unfold lemmaVTiledWeakEnergy
  rw [← Homogenization.descendantsAverage_sum]
  congr 1
  funext U
  rw [oldSignedPrimalErrorSize,Real.sq_sqrt (Finset.sum_nonneg (fun c _ => sq_nonneg _))]
  apply Finset.sum_congr rfl
  intro c _
  exact (Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U (e c))).symm

end
end ASDExplicitGamma.Native
