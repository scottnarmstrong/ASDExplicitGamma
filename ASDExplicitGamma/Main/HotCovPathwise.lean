module

public import ASDExplicitGamma.Main.HotCovPrincipalBound
public import ASDExplicitGamma.Main.HotPatchSourceBound

/-! MA-E-COVARIANCE, step 17: the pathwise (fixed-sample) bound of the affine C carrier
of the hot trial, `C_aff ≤ (v/2) B Δ + 2 P_z κ_E + 2 P_r κ_aff`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

noncomputable section

/-- On a tile, the coarse potential's gradient has the weak energy of the cell
comparison's first block. -/
theorem hotCov_Xk_cell (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (P : BlockVec 2) :
    vectorWeakHaarEnergy U.val
        (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function.grad =
      vectorWeakHaarEnergy U.val (hotCovCmp Q d nu sigma hnu hsigma k U P).potential := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  have hw : MemLp (fun x => (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function.grad x)
      2 (normalizedCubeMeasure Q) := by
    exact memLp_pi_iff.mpr (fun i =>
      (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function.grad_memL2_normalizedCubeMeasure i)
  have hF (i : Fin 2) : MemLp (fun x =>
      (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function.grad x i) 2
      (normalizedCubeMeasure U.val) :=
    memLp_on_descendant_of_memLp U.property
      ((hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function.grad_memL2_normalizedCubeMeasure i)
  have hG (i : Fin 2) : MemLp (fun x => (hotCovCmp Q d nu sigma hnu hsigma k U P).potential x i)
      2 (normalizedCubeMeasure U.val) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
      (memVectorL2_fst_of_memBlockL2
        (old_hessian_parent_cell_comparison_memL2 Q U.val hsub nu sigma hnu hsigma k P)) i)
  have hae : (fun x => (hotPatchPotential Q d nu sigma hnu hsigma k P).toH1Function.grad x) =ᵐ[
      volume.restrict (cubeSet U.val)]
      (hotCovCmp Q d nu sigma hnu hsigma k U P).potential := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet U.val]
    have h := old_hessian_patch_comparison_restrict Q d nu sigma hnu hsigma k P U
    filter_upwards [h] with x hx
    rw [hotPatchPotential_grad]
    exact congrArg Prod.fst hx
  exact main_vector_weak_hair_energy_congr_ae U.val hF hG hae

theorem hotCov_Xk_eq (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q d
      (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) =
      ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U => vectorWeakHaarEnergy U.val
        (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)).potential) := by
  apply Finset.sum_congr rfl
  intro c _
  unfold lemmaVTiledWeakEnergy
  rw [← old_signed_cell_average_eq_descendantsAverage]
  congr 1
  funext U
  exact hotCov_Xk_cell Q d nu sigma hnu hsigma k U _

/-- THE PATHWISE BOUND (NOTE (9.1), before expectation): the affine C carrier of the hot
trial is at most `(v/2) B Δ + 2 P_z κ_E + 2 P_r κ_aff`, with `P_z ≤ √Xk`,
`P_r ≤ κ_rem √Xk + k_d √Vφ`. -/
theorem hot_cov_pathwise_bound (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1) (B : ℝ)
    (hB : ∀ U ∈ descendantsAtDepth Q d,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ B) :
    hotCovAffCarrier Q d nu sigma hnu hsigma k b L ≤
      (b ^ 2 / 2) * (B * (descendantsAverage Q d (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k) 1) -
        traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) 1)) +
      2 * Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q d
          (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) *
        Real.sqrt (hotCovKE2 Q d nu sigma hnu hsigma k b L) +
      2 * (mainKrem (b ^ 2) * Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q d
            (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad) +
          mainKd (b ^ 2) * Real.sqrt (∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q d
            (hotGluedCorrector Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad)) *
        Real.sqrt (hotCovKaff2 Q d nu sigma hnu hsigma k b L) := by
  classical
  set Xk := ∑ c : BlockCoord 2, lemmaVTiledWeakEnergy Q d
    (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad with hXk
  set Pz2 := ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
    vectorPositiveHaarEnergy U.val (fun x => planarQuarterTurn
      (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)) x))) with hPz2
  set Yk := ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
    vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c))) with hYk
  have hPz : Pz2 ≤ Xk := Finset.sum_le_sum (fun c _ =>
    hotCov_Pz_le_Xk Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)))
  have hpaired := hot_cov_paired_drop_weak Q d nu sigma hnu hsigma k B hB
  have hsplit : (∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
      vectorWeakHaarEnergy U.val (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)).potential +
      vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c)))) =
      (∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U => vectorWeakHaarEnergy U.val
        (hotCovCmp Q d nu sigma hnu hsigma k U (blockBasis c)).potential)) + Yk := by
    simp only [old_signed_cell_average_add, Finset.sum_add_distrib]
    rfl
  have hXY : Xk + Yk ≤ B * (descendantsAverage Q d (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k) 1) -
        traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) 1) := by
    rw [hXk, hotCov_Xk_eq, ← hsplit]
    exact hpaired
  have hPz0 : 0 ≤ Pz2 := Finset.sum_nonneg (fun c _ =>
    old_signed_cell_average_mono Q d (f := fun _ => 0) (fun U => vectorPositiveHaarEnergy_nonneg _ _)
      |>.trans' (by simp [oldSignedCellAverage]))
  have hYk0 : 0 ≤ Yk := Finset.sum_nonneg (fun c _ =>
    old_signed_cell_average_mono Q d (f := fun _ => 0) (fun U => vectorWeakHaarEnergy_nonneg _ _)
      |>.trans' (by simp [oldSignedCellAverage]))
  have hprin := hotCov_prin_bound Q d nu sigma hnu hsigma k
  have herr := hotCov_err_bound Q d nu sigma hnu hsigma k b L
  have hres := hotCov_res_bound Q d nu sigma hnu hsigma k b L hL hmesh
  have hsize := (hot_cov_rem_size_bound Q d nu sigma hnu hsigma k b L hL hmesh).2
  have hdec := hotCov_affCarrier_decomp Q d nu sigma hnu hsigma k b L hL hmesh
  -- principal: sqrt Pz2 sqrt Yk ≤ (Pz2 + Yk)/2
  have hyoung : Real.sqrt Pz2 * Real.sqrt Yk ≤ (Pz2 + Yk) / 2 := by
    nlinarith [sq_nonneg (Real.sqrt Pz2 - Real.sqrt Yk), Real.sq_sqrt hPz0, Real.sq_sqrt hYk0]
  have hprin' : |hotCovPrinTotal Q d nu sigma hnu hsigma k| ≤
      (B * (descendantsAverage Q d (fun U => traceDefect (openCubeSet U)
        (responseFramePlanarCoefficientField nu sigma k) 1) -
        traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) 1)) / 2 := by
    refine hprin.trans (hyoung.trans ?_)
    linarith
  have hKaff0 : 0 ≤ Real.sqrt (hotCovKaff2 Q d nu sigma hnu hsigma k b L) := Real.sqrt_nonneg _
  have hres' : |hotCovResTotal Q d nu sigma hnu hsigma k b L| ≤
      (mainKrem (b ^ 2) * Real.sqrt Xk + mainKd (b ^ 2) * Real.sqrt (∑ c : BlockCoord 2,
        lemmaVTiledWeakEnergy Q d
          (hotGluedCorrector Q d nu sigma hnu hsigma k (blockBasis c)).toH1Function.grad)) *
        Real.sqrt (hotCovKaff2 Q d nu sigma hnu hsigma k b L) :=
    hres.trans (mul_le_mul_of_nonneg_right hsize hKaff0)
  have herr' : |hotCovErrTotal Q d nu sigma hnu hsigma k b L| ≤
      Real.sqrt Xk * Real.sqrt (hotCovKE2 Q d nu sigma hnu hsigma k b L) :=
    herr.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hPz) (Real.sqrt_nonneg _))
  rw [hdec]
  have e1 := le_abs_self (hotCovResTotal Q d nu sigma hnu hsigma k b L)
  have e2 := neg_abs_le (hotCovPrinTotal Q d nu sigma hnu hsigma k)
  have e3 := neg_abs_le (hotCovErrTotal Q d nu sigma hnu hsigma k b L)
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  nlinarith [mul_le_mul_of_nonneg_left hprin' hb2]

end

end ASDExplicitGamma.Main
