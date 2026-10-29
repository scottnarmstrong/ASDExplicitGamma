module

public import ASDExplicitGamma.Native.OldSignedHistoryComparison
public import ASDExplicitGamma.Scalar.CellResidualMean
public import ASDExplicitGamma.Scalar.ResidualSourcePairing
public import ASDExplicitGamma.Scalar.ResidualWeakHistory
public import ASDExplicitGamma.Triadic.VectorHaar
import ASDExplicitGamma.Triadic.PlanarDirichletBridge

/-! Source-side flat projection estimates for the actual OLD weighted minimizer. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped ENNReal

theorem old_signed_constant_block_pairing_mean (Q : TriadicCube 2)
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) (P : BlockVec 2) :
    volumeAverage (openCubeSet Q) (fun x => blockVecDot P (F x)) =
      blockVecDot P (oldSignedBlockMean Q F) := by
  have hswap : MemBlockL2 (openCubeSet Q) (fun x => (F x).swap) := by
    exact memBlockL2_blockField (memVectorL2_snd_of_memBlockL2 hF)
      (memVectorL2_fst_of_memBlockL2 hF)
  have hfirst := top_constant_pairing_eq_mean Q hF P.1
  have hsecond := top_constant_pairing_eq_mean Q hswap P.2
  have hIfst : IntegrableOn
      (fun x => blockVecDot (P.1, 0) (F x)) (openCubeSet Q) := by
    have hi := integrableOn_vecDot_of_memVectorL2 (memVectorL2_const P.1)
      (memVectorL2_fst_of_memBlockL2 hF)
    simpa [blockVecDot, vecDot_zero_left] using hi
  have hIsnd : IntegrableOn
      (fun x => blockVecDot (P.2, 0) ((F x).swap)) (openCubeSet Q) := by
    have hi := integrableOn_vecDot_of_memVectorL2 (memVectorL2_const P.2)
      (memVectorL2_snd_of_memBlockL2 hF)
    simpa [blockVecDot, vecDot_zero_left] using hi
  have hpoint (x : Vec 2) :
      blockVecDot P (F x) = blockVecDot (P.1, 0) (F x) +
        blockVecDot (P.2, 0) ((F x).swap) := by
    simp [blockVecDot, vecDot, Fin.sum_univ_two]
  calc
    volumeAverage (openCubeSet Q) (fun x => blockVecDot P (F x)) =
        volumeAverage (openCubeSet Q) (fun x =>
          blockVecDot (P.1, 0) (F x) + blockVecDot (P.2, 0) ((F x).swap)) := by
      congr 1
      funext x
      exact hpoint x
    _ = volumeAverage (openCubeSet Q) (fun x => blockVecDot (P.1, 0) (F x)) +
        volumeAverage (openCubeSet Q) (fun x => blockVecDot (P.2, 0) ((F x).swap)) :=
      volumeAverage_add hIfst hIsnd
    _ = blockVecDot P (oldSignedBlockMean Q F) := by
      rw [hfirst, hsecond]
      simp [oldSignedBlockMean, blockVecDot, vecDot, Fin.sum_univ_two]

private theorem old_signed_block_projection_energy_eq_means
    (Q : TriadicCube 2) (j : ℕ) (F : Vec 2 → BlockVec 2)
    (hF : ∀ b : Bool, ∀ i : Fin 2,
      MemLp (fun x => (if b then (F x).1 else (F x).2) i) 2
        (normalizedCubeMeasure Q)) :
    (∑ i, energy Q (cubeProjection Q j (fun x => (F x).1 i))) +
      (∑ i, energy Q (cubeProjection Q j (fun x => (F x).2 i))) =
    descendantsAverage Q j (fun R =>
      blockVecDot (oldSignedBlockMean R F) (oldSignedBlockMean R F)) := by
  have hfst := vector_projection_energy_eq_means Q j (fun x => (F x).1)
    (fun i => hF true i)
  have hsnd := vector_projection_energy_eq_means Q j (fun x => (F x).2)
    (fun i => hF false i)
  rw [hfst, hsnd]
  unfold descendantsAverage
  calc
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          vecNormSq (fun i => cubeAverage R (fun x => (F x).1 i)) +
            ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          vecNormSq (fun i => cubeAverage R (fun x => (F x).2 i)) =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ((∑ R ∈ descendantsAtDepth Q j,
            vecNormSq (fun i => cubeAverage R (fun x => (F x).1 i))) +
          ∑ R ∈ descendantsAtDepth Q j,
            vecNormSq (fun i => cubeAverage R (fun x => (F x).2 i))) := by ring
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          (vecNormSq (fun i => cubeAverage R (fun x => (F x).1 i)) +
            vecNormSq (fun i => cubeAverage R (fun x => (F x).2 i))) := by
      rw [Finset.sum_add_distrib]
    _ = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          blockVecDot (oldSignedBlockMean R F) (oldSignedBlockMean R F) := by
      congr 1

/-- Every finite dyadic projection of the actual four-component OLD flux is
bounded by the full doubled-response depth history times the true residual
energy. -/
theorem old_signed_flux_projection_energy_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (H : HilbertBlockL2 (openCubeSet Q))
    (j : ℕ) :
    (∑ i, energy Q (cubeProjection Q j (fun x =>
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k H) x).1 i))) +
      (∑ i, energy Q (cubeProjection Q j (fun x =>
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k H) x).2 i))) ≤
    fullResponseDepthMax Q (responseFramePlanarCoefficientField nu sigma k) j *
      cubeAverage Q (fun x => blockVecDot
        (scalarResidualField Q nu sigma hnu hsigma k H x)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k H) x)) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let J : Vec 2 → BlockVec 2 := scalarCoefficientFlux a Z
  let E : Vec 2 → ℝ := fun x => blockVecDot (Z x) (J x)
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hZ : MemBlockL2 (openCubeSet Q) Z := Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k H)
  have hJ : MemBlockL2 (openCubeSet Q) J := by
    exact scalar_coefficient_flux_memL2 Q a hEll hZ
  have hJcoords : ∀ b : Bool, ∀ i : Fin 2,
      MemLp (fun x => (if b then (J x).1 else (J x).2) i) 2
        (normalizedCubeMeasure Q) := by
    intro b i
    cases b
    · exact memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hJ) i)
    · exact memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hJ) i)
  have hEintOpen : IntegrableOn E (openCubeSet Q) volume := by
    exact scalar_coefficient_energy_integrable Q a hEll hZ
  have hEint : IntegrableOn E (cubeSet Q) volume :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hEintOpen
  have hEaverage (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      cubeAverage R E = volumeAverage (openCubeSet R) E :=
    cube_average_eq_volume_average_open R E
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      blockVecDot (oldSignedBlockMean R J) (oldSignedBlockMean R J) ≤
        fullResponseDepthMax Q a j * cubeAverage R E := by
    let U := openCubeSet R
    let mR := oldSignedBlockMean R J
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
    have hJR : MemBlockL2 U J :=
      hJ.mono_measure (Measure.restrict_mono_set volume hsub)
    have hER : 0 ≤ volumeAverage U E := by
      exact scalar_coefficient_energy_average_nonneg R a hEllR Z
    have hpair := scalar_residual_cell_pairing_bound Q R hsub nu sigma hnu hsigma k H mR
    have hpair' :
        (volumeAverage U (fun x => blockVecDot mR (J x))) ^ 2 ≤
          volumeAverage U E * blockVecDot mR
            (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) mR) := by
      simpa [J, E, Z, a, scalarCoefficientFlux] using hpair
    rw [old_signed_constant_block_pairing_mean R hJR mR] at hpair'
    have hquad := block_quadratic_le_operator_norm (coarseBlockMatrix (cubeSet R) a) mR
    have hfull :
        blockVecDot mR (blockMatVecMul (coarseBlockMatrix (cubeSet R) a) mR) ≤
          fullResponseOperatorNorm R a * blockVecDot mR mR := by
      simpa only [fullResponseOperatorNorm] using hquad
    have hupper := mul_le_mul_of_nonneg_left hfull hER
    have hmax := full_response_norm_le_depth_max Q R a j hR
    have hnonneg : 0 ≤ blockVecDot mR mR := by
      simpa [blockVecDot, vecNormSq] using
        add_nonneg (vecNormSq_nonneg mR.1) (vecNormSq_nonneg mR.2)
    have hmax' := mul_le_mul_of_nonneg_right hmax hnonneg
    have hnorm2 : blockVecDot mR mR = 0 ∨ 0 < blockVecDot mR mR := by
      rcases eq_or_lt_of_le hnonneg with hz | hp
      · exact Or.inl hz.symm
      · exact Or.inr hp
    rw [hEaverage R hR]
    rcases hnorm2 with hz | hz
    · rw [hz]
      exact mul_nonneg (full_response_depth_max_nonneg Q a j) hER
    · nlinarith [hpair', hupper, hmax']
  rw [old_signed_block_projection_energy_eq_means Q j J hJcoords,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j E hEint]
  unfold descendantsAverage
  calc
    _ ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j,
          fullResponseDepthMax Q a j * cubeAverage R E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun R hR => hpoint R hR)
        (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The actual four-component OLD flux has weak Haar energy bounded by its
complete full-response history times its actual residual energy. -/
private theorem old_signed_dual_energy_mono (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    dualEnergy Q (Real.sqrt 3) f ≤ dualEnergy Q sourceHaarBase f := by
  have hbase : sourceHaarBase ≤ Real.sqrt 3 := by
    change (3 : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt 3
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by norm_num)
  have hbasePos : 0 < sourceHaarBase := lt_trans zero_lt_one source_haar_base_gt_one
  have hrootPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hrootOne : 1 < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  have hinv : (Real.sqrt 3)⁻¹ ≤ sourceHaarBase⁻¹ :=
    (inv_le_inv₀ hrootPos hbasePos).2 hbase
  have hsmall := summable_dual_increments Q source_haar_base_gt_one hf
  have hlarge := summable_dual_increments Q hrootOne hf
  have hterm (j : ℕ) : (Real.sqrt 3)⁻¹ ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) f) ≤
      sourceHaarBase⁻¹ ^ (j + 1) * energy Q (cubeIncrement Q (j + 1) f) := by
    apply mul_le_mul_of_nonneg_right _ (energy_nonneg Q _)
    exact pow_le_pow_left₀ (inv_nonneg.mpr hrootPos.le) hinv (j + 1)
  unfold dualEnergy primalEnergy
  exact add_le_add_right (hlarge.tsum_le_tsum hterm hsmall)
    (energy Q (cubeIncrement Q 0 f))

theorem old_signed_flux_weak_history_bound (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (H : HilbertBlockL2 (openCubeSet Q)) :
    oldSignedBlockWeakNorm Q (fun x =>
        scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k H) x) ^ 2 ≤
      oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        cubeAverage Q (fun x => blockVecDot
          (scalarResidualField Q nu sigma hnu hsigma k H x)
          (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
            (scalarResidualField Q nu sigma hnu hsigma k H) x)) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let J : Vec 2 → BlockVec 2 := scalarCoefficientFlux a Z
  let E : Vec 2 → ℝ := fun x => blockVecDot (Z x) (J x)
  let α := Scalar.inverseHistoryDiscount
  let e₁ (j : ℕ) := ∑ i, energy Q (cubeProjection Q j (fun x => (J x).1 i))
  let e₂ (j : ℕ) := ∑ i, energy Q (cubeProjection Q j (fun x => (J x).2 i))
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hZ : MemBlockL2 (openCubeSet Q) Z :=
    Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k H)
  have hJ : MemBlockL2 (openCubeSet Q) J := scalar_coefficient_flux_memL2 Q a hEll hZ
  have hJcoords : ∀ b : Bool, ∀ i : Fin 2,
      MemLp (fun x => (if b then (J x).1 else (J x).2) i) 2
        (normalizedCubeMeasure Q) := by
    intro b i
    cases b
    · exact memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hJ) i)
    · exact memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hJ) i)
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr Scalar.inverse_history_discount_range.2.le
  have hinv : sourceHaarBase⁻¹ = α := by
    dsimp [α]
    exact Scalar.inverse_history_discount_eq.symm
  have hcoord (b : Bool) (i : Fin 2) : Summable (fun j : ℕ =>
      α ^ j * energy Q (cubeProjection Q j
        (fun x => (if b then (J x).1 else (J x).2) i))) := by
    simpa only [← hinv] using
      (summable_weighted_projections Q source_haar_base_gt_one (hJcoords b i))
  have he₁ : Summable (fun j : ℕ => α ^ j * e₁ j) := by
    simp_rw [e₁, Finset.mul_sum]
    exact summable_sum fun i hi => by simpa using hcoord true i
  have he₂ : Summable (fun j : ℕ => α ^ j * e₂ j) := by
    simp_rw [e₂, Finset.mul_sum]
    exact summable_sum fun i hi => by simpa using hcoord false i
  have heall : Summable (fun j : ℕ => α ^ j * (e₁ j + e₂ j)) := by
    have hEq : (fun j : ℕ => α ^ j * (e₁ j + e₂ j)) =
        (fun j => α ^ j * e₁ j + α ^ j * e₂ j) := by
      funext j
      ring
    rw [hEq]
    exact he₁.add he₂
  have habel₁ := vector_weak_energy_abel Q (fun x i => (J x).1 i)
    (fun i => hJcoords true i)
  have habel₂ := vector_weak_energy_abel Q (fun x i => (J x).2 i)
    (fun i => hJcoords false i)
  have hweakSq (f : Vec 2 → ℝ) : weakHaarNorm Q f ^ 2 =
      dualEnergy Q (Real.sqrt 3) f := by
    rw [weakHaarNorm]
    exact Real.sq_sqrt (Triadic.dualEnergy_nonneg Q (Real.sqrt 3)
      (Real.sqrt_nonneg _) f)
  have hweak_bound : oldSignedBlockWeakNorm Q J ^ 2 ≤
      (1 - α) * ∑' j : ℕ, α ^ j * (e₁ j + e₂ j) := by
    unfold oldSignedBlockWeakNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),
      vectorWeakHaarNorm_sq, vectorWeakHaarNorm_sq]
    simp_rw [hweakSq]
    calc
      _ ≤ (∑ i, dualEnergy Q sourceHaarBase (fun x => (J x).1 i)) +
          ∑ i, dualEnergy Q sourceHaarBase (fun x => (J x).2 i) := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro i hi
          exact old_signed_dual_energy_mono Q (hJcoords true i)
        · apply Finset.sum_le_sum
          intro i hi
          exact old_signed_dual_energy_mono Q (hJcoords false i)
      _ = (1 - α) * ∑' j : ℕ, α ^ j * (e₁ j + e₂ j) := by
        rw [habel₁, habel₂]
        calc
          _ = (1 - α) * ((∑' j : ℕ, α ^ j * e₁ j) +
                (∑' j : ℕ, α ^ j * e₂ j)) := by ring
          _ = _ := by
            rw [← he₁.tsum_add he₂]
            congr 1
            apply tsum_congr
            intro j
            ring
  have hEavg : 0 ≤ cubeAverage Q E := by
    rw [cube_average_eq_volume_average_open]
    exact scalar_coefficient_energy_average_nonneg Q a hEll Z
  have hresp : Summable (fun j : ℕ => α ^ j * fullResponseDepthMax Q a j) := by
    simpa [α] using old_signed_response_depth_series_summable Q a hEll
  have hrespr : Summable (fun j : ℕ => α ^ j * (fullResponseDepthMax Q a j * cubeAverage Q E)) := by
    convert hresp.mul_right (cubeAverage Q E) using 1
    ext j
    ring
  have hproj (j : ℕ) : e₁ j + e₂ j ≤
      fullResponseDepthMax Q a j * cubeAverage Q E := by
    dsimp [e₁, e₂, J, E, a]
    exact old_signed_flux_projection_energy_bound Q nu sigma hnu hsigma k H j
  have hterm (j : ℕ) : α ^ j * (e₁ j + e₂ j) ≤
      α ^ j * (fullResponseDepthMax Q a j * cubeAverage Q E) :=
    mul_le_mul_of_nonneg_left (hproj j) (pow_nonneg hα j)
  have htsum := heall.tsum_le_tsum hterm hrespr
  have hrespOf : oldSignedResponseHistory Q a = (1 - α) *
      (∑' j : ℕ, α ^ j * fullResponseDepthMax Q a j) := by
    have hrespNonneg : ∀ j : ℕ, 0 ≤ α ^ j * fullResponseDepthMax Q a j :=
      fun j => mul_nonneg (pow_nonneg hα j) (full_response_depth_max_nonneg Q a j)
    have hTsumNonneg : 0 ≤ ∑' j : ℕ, α ^ j * fullResponseDepthMax Q a j :=
      tsum_nonneg hrespNonneg
    unfold oldSignedResponseHistory completeFullResponseHistory
    rw [← ENNReal.ofReal_tsum_of_nonneg hrespNonneg hresp,
      ← ENNReal.ofReal_mul h1α]
    simp only [ENNReal.toReal_ofReal (mul_nonneg h1α hTsumNonneg)]
  calc
    oldSignedBlockWeakNorm Q J ^ 2 ≤
        (1 - α) * ∑' j : ℕ, α ^ j * (e₁ j + e₂ j) := hweak_bound
    _ ≤ (1 - α) * ∑' j : ℕ,
        α ^ j * (fullResponseDepthMax Q a j * cubeAverage Q E) :=
      mul_le_mul_of_nonneg_left htsum h1α
    _ = (1 - α) * ((∑' j : ℕ, α ^ j * fullResponseDepthMax Q a j) *
          cubeAverage Q E) := by
      rw [← tsum_mul_right]
      congr 1
      apply tsum_congr
      intro j
      ring
    _ = oldSignedResponseHistory Q a * cubeAverage Q E := by
      calc
        _ = ((1 - α) * (∑' j : ℕ, α ^ j * fullResponseDepthMax Q a j)) *
              cubeAverage Q E := by ring
        _ = _ := by rw [hrespOf]

private theorem old_signed_block_volume_pairing_eq (Q : TriadicCube 2)
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (G x)) =
      Triadic.vectorPairing Q (fun x => (F x).1) (fun x => (G x).1) +
        Triadic.vectorPairing Q (fun x => (F x).2) (fun x => (G x).2) := by
  let F₁ := memVectorL2_fst_of_memBlockL2 hF
  let F₂ := memVectorL2_snd_of_memBlockL2 hF
  let G₁ := memVectorL2_fst_of_memBlockL2 hG
  let G₂ := memVectorL2_snd_of_memBlockL2 hG
  have hF₁i (i : Fin 2) : MemScalarL2 (openCubeSet Q) (fun x => (F x).1 i) :=
    memScalarL2_coord_of_memVectorL2 F₁ i
  have hF₂i (i : Fin 2) : MemScalarL2 (openCubeSet Q) (fun x => (F x).2 i) :=
    memScalarL2_coord_of_memVectorL2 F₂ i
  have hG₁i (i : Fin 2) : MemScalarL2 (openCubeSet Q) (fun x => (G x).1 i) :=
    memScalarL2_coord_of_memVectorL2 G₁ i
  have hG₂i (i : Fin 2) : MemScalarL2 (openCubeSet Q) (fun x => (G x).2 i) :=
    memScalarL2_coord_of_memVectorL2 G₂ i
  have hI₁ : IntegrableOn (fun x => vecDot ((F x).1) ((G x).1))
      (openCubeSet Q) volume := integrableOn_vecDot_of_memVectorL2 F₁ G₁
  have hI₂ : IntegrableOn (fun x => vecDot ((F x).2) ((G x).2))
      (openCubeSet Q) volume := integrableOn_vecDot_of_memVectorL2 F₂ G₂
  have hpair₁ : volumeAverage (openCubeSet Q)
      (fun x => vecDot ((F x).1) ((G x).1)) =
      Triadic.vectorPairing Q (fun x => (F x).1) (fun x => (G x).1) := by
    change volumeAverage (openCubeSet Q) (fun x =>
      ∑ i, (F x).1 i * (G x).1 i) = _
    rw [volumeAverage_sum Finset.univ (fun i x => (F x).1 i * (G x).1 i)
      (fun i _ => (hF₁i i).integrable_mul (hG₁i i))]
    unfold Triadic.vectorPairing
    apply Finset.sum_congr rfl
    intro i hi
    rw [Triadic.pairing, cube_average_eq_volume_average_open]
  have hpair₂ : volumeAverage (openCubeSet Q)
      (fun x => vecDot ((F x).2) ((G x).2)) =
      Triadic.vectorPairing Q (fun x => (F x).2) (fun x => (G x).2) := by
    change volumeAverage (openCubeSet Q) (fun x =>
      ∑ i, (F x).2 i * (G x).2 i) = _
    rw [volumeAverage_sum Finset.univ (fun i x => (F x).2 i * (G x).2 i)
      (fun i _ => (hF₂i i).integrable_mul (hG₂i i))]
    unfold Triadic.vectorPairing
    apply Finset.sum_congr rfl
    intro i hi
    rw [Triadic.pairing, cube_average_eq_volume_average_open]
  change volumeAverage (openCubeSet Q) (fun x =>
    vecDot ((F x).1) ((G x).1) + vecDot ((F x).2) ((G x).2)) = _
  have hsplit : (fun x => vecDot ((F x).1) ((G x).1) +
      vecDot ((F x).2) ((G x).2)) =
      (fun x => vecDot ((F x).1) ((G x).1)) +
        (fun x => vecDot ((F x).2) ((G x).2)) := by
    funext x
    rfl
  rw [hsplit, volumeAverage_add hI₁ hI₂, hpair₁, hpair₂]

/-- The normalized weighted pairing of doubled fields is controlled by their
four-component positive and weak Haar norms. -/
theorem old_signed_block_pairing_bound (Q : TriadicCube 2)
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G)
    (hP₁ : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (F x).1 i))))
    (hP₂ : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (F x).2 i)))) :
    |volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (G x))| ≤
      oldSignedBlockPositiveNorm Q F * oldSignedBlockWeakNorm Q G := by
  let F₁ := memVectorL2_fst_of_memBlockL2 hF
  let F₂ := memVectorL2_snd_of_memBlockL2 hF
  let G₁ := memVectorL2_fst_of_memBlockL2 hG
  let G₂ := memVectorL2_snd_of_memBlockL2 hG
  have hF₁i (i : Fin 2) : MemLp (fun x => (F x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 F₁ i)
  have hF₂i (i : Fin 2) : MemLp (fun x => (F x).2 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 F₂ i)
  have hG₁i (i : Fin 2) : MemLp (fun x => (G x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 G₁ i)
  have hG₂i (i : Fin 2) : MemLp (fun x => (G x).2 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 G₂ i)
  let p (b : Bool) := vectorPositiveHaarEnergy Q (if b then (fun x => (F x).1) else (fun x => (F x).2))
  let w (b : Bool) := vectorWeakHaarEnergy Q (if b then (fun x => (G x).1) else (fun x => (G x).2))
  have hpair₁ := Triadic.abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
    Q hF₁i hG₁i hP₁
  have hpair₂ := Triadic.abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
    Q hF₂i hG₂i hP₂
  have hWnonneg (b : Bool) : 0 ≤ w b := by
    dsimp [w]
    exact Triadic.vectorWeakHaarEnergy_nonneg (d := 2) (m := 2) Q
      (if b then (fun x => (G x).1) else (fun x => (G x).2))
  have hPnonneg (b : Bool) : 0 ≤ p b := by
    dsimp [p]
    exact Triadic.vectorPositiveHaarEnergy_nonneg (d := 2) (m := 2) Q
      (if b then (fun x => (F x).1) else (fun x => (F x).2))
  have hsumCS : Real.sqrt (w true) * Real.sqrt (p true) +
      Real.sqrt (w false) * Real.sqrt (p false) ≤
      Real.sqrt (w true + w false) * Real.sqrt (p true + p false) := by
    have hcs := Real.sum_sqrt_mul_sqrt_le Finset.univ hWnonneg hPnonneg
    simpa [w, p] using hcs
  have hnormP : oldSignedBlockPositiveNorm Q F = Real.sqrt (p true + p false) := by
    unfold oldSignedBlockPositiveNorm
    rw [show vectorPositiveHaarNorm Q (fun x => (F x).1) ^ 2 =
        vectorPositiveHaarEnergy Q (fun x => (F x).1) by
          unfold vectorPositiveHaarNorm
          exact Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg Q _),
      show vectorPositiveHaarNorm Q (fun x => (F x).2) ^ 2 =
        vectorPositiveHaarEnergy Q (fun x => (F x).2) by
          unfold vectorPositiveHaarNorm
          exact Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg Q _)]
    rfl
  have hnormW : oldSignedBlockWeakNorm Q G = Real.sqrt (w true + w false) := by
    unfold oldSignedBlockWeakNorm
    rw [show vectorWeakHaarNorm Q (fun x => (G x).1) ^ 2 =
        vectorWeakHaarEnergy Q (fun x => (G x).1) by
          unfold vectorWeakHaarNorm
          exact Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _),
      show vectorWeakHaarNorm Q (fun x => (G x).2) ^ 2 =
        vectorWeakHaarEnergy Q (fun x => (G x).2) by
          unfold vectorWeakHaarNorm
          exact Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)]
    rfl
  have hrepr := old_signed_block_volume_pairing_eq Q hF hG
  calc
    |volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (G x))| =
        |Triadic.vectorPairing Q (fun x => (F x).1) (fun x => (G x).1) +
          Triadic.vectorPairing Q (fun x => (F x).2) (fun x => (G x).2)| := by rw [hrepr]
    _ ≤ |Triadic.vectorPairing Q (fun x => (F x).1) (fun x => (G x).1)| +
          |Triadic.vectorPairing Q (fun x => (F x).2) (fun x => (G x).2)| := abs_add_le _ _
    _ ≤ Real.sqrt (w true) * Real.sqrt (p true) +
          Real.sqrt (w false) * Real.sqrt (p false) := by
      dsimp [w, p]
      calc
        _ ≤ vectorPositiveHaarNorm Q (fun x => (F x).1) *
              vectorWeakHaarNorm Q (fun x => (G x).1) +
            vectorPositiveHaarNorm Q (fun x => (F x).2) *
              vectorWeakHaarNorm Q (fun x => (G x).2) := add_le_add hpair₁ hpair₂
        _ = _ := by
          simp only [vectorPositiveHaarNorm, vectorWeakHaarNorm]
          ring
    _ ≤ Real.sqrt (w true + w false) * Real.sqrt (p true + p false) := hsumCS
    _ = oldSignedBlockPositiveNorm Q F * oldSignedBlockWeakNorm Q G := by
      rw [hnormP, hnormW]
      ring

theorem old_signed_residual_source_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 (openCubeSet Q) F) :
    cubeAverage Q (fun x => blockVecDot
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF) x)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k
            (toHilbertBlockL2OfBlockField hF)) x)) =
      volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x)
        (scalarCoefficientFlux (responseFramePlanarCoefficientField nu sigma k)
          (scalarResidualField Q nu sigma hnu hsigma k
            (toHilbertBlockL2OfBlockField hF)) x)) := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let H := toHilbertBlockL2OfBlockField hF
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let J : Vec 2 → BlockVec 2 := scalarCoefficientFlux a Z
  have hZ : MemBlockL2 (openCubeSet Q) Z := Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k H)
  have hZrebuild : toHilbertBlockL2OfBlockField hZ =
      scalarProjectionResidual Q nu sigma hnu hsigma k H := hilbert_field_rebuild _
  have hSourceBilin := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hZ hF
  have hEnergyBilin := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hZ hZ
  rw [hZrebuild] at hSourceBilin hEnergyBilin
  have hPair := scalar_projection_residual_energy_pairing Q nu sigma hnu hsigma k H
  rw [hSourceBilin, hEnergyBilin] at hPair
  calc
    cubeAverage Q (fun x => blockVecDot (Z x) (J x)) =
        volumeAverage (openCubeSet Q) (fun x => blockVecDot (Z x) (J x)) :=
          cube_average_eq_volume_average_open Q _
    _ = volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (J x)) := hPair.symm

/-- A genuinely positive-Haar source has its actual OLD weighted projection
energy bounded by the complete full-response history. -/
theorem old_signed_flat_source_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hP₁ : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (F x).1 i))))
    (hP₂ : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => (F x).2 i)))) :
    oldSignedEnergyPairing Q nu sigma k
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF))
        (scalarResidualField Q nu sigma hnu hsigma k
          (toHilbertBlockL2OfBlockField hF)) ≤
      oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        oldSignedBlockPositiveNorm Q F ^ 2 := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let H := toHilbertBlockL2OfBlockField hF
  let Z : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let J : Vec 2 → BlockVec 2 := scalarCoefficientFlux a Z
  let E := cubeAverage Q (fun x => blockVecDot (Z x) (J x))
  let P := oldSignedBlockPositiveNorm Q F
  let W := oldSignedBlockWeakNorm Q J
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hE : 0 ≤ E := by
    dsimp [E]
    rw [cube_average_eq_volume_average_open]
    exact scalar_coefficient_energy_average_nonneg Q a hEll Z
  have hPnonneg : 0 ≤ P := Real.sqrt_nonneg _
  have hWnonneg : 0 ≤ W := Real.sqrt_nonneg _
  have hMnonneg : 0 ≤ oldSignedResponseHistory Q a := by
    unfold oldSignedResponseHistory
    exact ENNReal.toReal_nonneg
  have hWeak : W ^ 2 ≤ oldSignedResponseHistory Q a * E := by
    dsimp [W, J, E, a, Z, H]
    exact old_signed_flux_weak_history_bound Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF)
  have hPair := old_signed_block_pairing_bound Q hF
    (scalar_coefficient_flux_memL2 Q a hEll
      (Lp.memLp (scalarResidualField Q nu sigma hnu hsigma k H))) hP₁ hP₂
  have hEpair : E = volumeAverage (openCubeSet Q) (fun x => blockVecDot (F x) (J x)) := by
    dsimp [E, J, a, Z, H]
    exact old_signed_residual_source_pairing Q nu sigma hnu hsigma k hF
  have hEupper : E ≤ P * W := by
    rw [← hEpair] at hPair
    exact (le_abs_self E).trans hPair
  have hPWnonneg : 0 ≤ P * W := mul_nonneg hPnonneg hWnonneg
  have hEsq : E ^ 2 ≤ oldSignedResponseHistory Q a * P ^ 2 * E := by
    have hmulSq : E ^ 2 ≤ (P * W) ^ 2 :=
      (sq_le_sq₀ hE (hPWnonneg)).2 hEupper
    calc
      E ^ 2 ≤ (P * W) ^ 2 := hmulSq
      _ = P ^ 2 * W ^ 2 := by ring
      _ ≤ P ^ 2 * (oldSignedResponseHistory Q a * E) :=
        mul_le_mul_of_nonneg_left hWeak (sq_nonneg P)
      _ = oldSignedResponseHistory Q a * P ^ 2 * E := by ring
  have hEnergy : E ≤ oldSignedResponseHistory Q a * P ^ 2 := by
    by_cases hzero : E = 0
    · rw [hzero]
      exact mul_nonneg hMnonneg (sq_nonneg P)
    · have hEpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
      have hcancel : E * E ≤ (oldSignedResponseHistory Q a * P ^ 2) * E := by
        calc
          E * E = E ^ 2 := by ring
          _ ≤ oldSignedResponseHistory Q a * P ^ 2 * E := hEsq
          _ = (oldSignedResponseHistory Q a * P ^ 2) * E := by ring
      exact le_of_mul_le_mul_right hcancel hEpos
  change oldSignedEnergyPairing Q nu sigma k Z Z ≤ _
  change volumeAverage (openCubeSet Q) (fun x => blockVecDot (Z x) (J x)) ≤ _
  rw [← cube_average_eq_volume_average_open Q (fun x => blockVecDot (Z x) (J x))]
  simpa [P, E, a] using hEnergy

end ASDExplicitGamma.Native
