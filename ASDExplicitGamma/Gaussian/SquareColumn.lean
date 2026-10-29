module

public import ASDExplicitGamma.Gaussian.SquareDirections
public import ASDExplicitGamma.Inverse.PureFluxGeneratorSharpTrace

/-! The full covariance source column on arbitrary translated triadic squares. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
open scoped BigOperators
noncomputable section

local instance squareColumnFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The positive Haar energy of one physical row on the requested tiling. -/
def squareQ3RowEnergy (Q : TriadicCube 2) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (m : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) (l : whiteBasisIndex) : ℝ :=
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  descendantsAverage Q m (fun U => vectorPositiveHaarEnergy U
    (lemmaVPlanarRowField (diagInterpolant Q m) (squareQ3BasisMultiplier Q b σ L l) v))

private theorem square_raw_row_coordinate {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (l : s) (i : Fin 2) (x : Vec 2) :
    (pureFluxMainQ3FiniteRawRow e s b L Q j v x).ofLp (l,i) =
      q3Convolution b L h3Zero (e l) x *
        (diagInterpolant Q j v).grad x i -
          (v-diagInterpolant Q j v).toFun x *
            (fderiv ℝ (q3Convolution b L h3Zero (e l)) x) (basisVec i) := by
  simp only [pureFluxMainQ3FiniteRawRow, mainEuclideanTensor,
    WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply,
    mainQ3FiniteValue, mainQ3FiniteColumn, smul_eq_mul]
  ring

private theorem square_raw_row_tile_bound
    (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) (s : Finset whiteBasisIndex)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q j) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    MemLp (pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j v) 2
      (normalizedCubeMeasure U) ∧
    Summable (fun k => (Real.sqrt 3)^(k+1) * hilbertEnergy U
      (hilbertCubeIncrement U (k+1)
        (pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j v))) ∧
    hilbertPositiveHaarNorm U (Real.sqrt 3)
        (pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j v) ≤
      (Real.sqrt (b^2) + cubeScaleFactor U * planarC1 *
          Real.sqrt ((156/5)*b^2/L.1^2)) *
          vectorPositiveHaarNorm U (diagInterpolant Q j v).grad +
        Real.sqrt ((156/5)*b^2/L.1^2) *
          positiveHaarNorm U (v-diagInterpolant Q j v).toFun +
        cubeScaleFactor U * planarC1 *
          Real.sqrt ((46488/25)*b^2/L.1^4) *
          Real.sqrt (energy U (v-diagInterpolant Q j v).toFun) := by
  intro v
  let I := diagInterpolant Q j
  let ψ := mainQ3FiniteValue whiteBasis s b L
  let F := fun x => WithLp.toLp 2 ((I v).grad x)
  let z := v-I v
  let zU := z.restrictToOpenSubcube hU
  let C := pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j v
  have hFcoord (i : Fin 2) : MemLp (fun x => (I v).grad x i) 2
      (normalizedCubeMeasure U) :=
    memLp_on_descendant_of_memLp hU ((I v).grad_memL2_normalizedCubeMeasure i)
  have hPcoord (i : Fin 2) : Summable (fun k => (Real.sqrt 3)^(k+1) *
      energy U (cubeIncrement U (k+1) (fun x => (I v).grad x i))) :=
    diagInterpolant_gradient_summable Q j p u U hU i
  have hF : MemLp F 2 (normalizedCubeMeasure U) := by
    simpa only [F] using (memLp_piLp_iff.mpr hFcoord)
  have hPF := main_hilbert_summable_of_coordinates U hF hPcoord
  have hPHF := main_hilbertPositive_eq_vectorPositive U hFcoord hPcoord
  have hM : 0 ≤ Real.sqrt (b^2) := Real.sqrt_nonneg _
  have hD : 0 ≤ Real.sqrt ((156/5:ℝ)*b^2/L.1^2) := Real.sqrt_nonneg _
  have hψbound : ∀ᵐ x ∂normalizedCubeMeasure U, ‖ψ x‖ ≤ Real.sqrt (b^2) := by
    filter_upwards with x
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    exact (pureFluxMainQ3FiniteValue_norm_sq_le whiteBasis s b L Q x).trans_eq
      (Real.sq_sqrt (sq_nonneg b)).symm
  have hψderivative : ∀ᵐ x ∂normalizedCubeMeasure U,
      (∑ i : Fin 2, ‖(fderiv ℝ ψ x) (basisVec i)‖^2) ≤
        (Real.sqrt ((156/5:ℝ)*b^2/L.1^2))^2 := by
    filter_upwards with x
    rw [Real.sq_sqrt (by positivity : 0 ≤ (156/5:ℝ)*b^2/L.1^2)]
    exact mainQ3FiniteValue_derivative_frobenius whiteBasis s b L x
  have hT := main_hilbert_tensor_product U ψ
      (mainQ3FiniteValue_contDiff whiteBasis s b L) hF hPF hM hD hψbound hψderivative
  have hCol := main_q3_negative_column_h1_product whiteBasis s b L U zU
  let Mcol := mainRankOneMultiplier U (mainQ3FiniteColumn whiteBasis s b L)
    (mainQ3FiniteColumn_contDiff whiteBasis s b L)
  have hBpos := Mcol.product_memLp zU.memL2_normalizedCubeMeasure
  have hB : MemLp (fun x => (-zU.toFun x) • mainQ3FiniteColumn whiteBasis s b L x)
      2 (normalizedCubeMeasure U) := by
    have hneg := hBpos.neg
    convert hneg using 1
    funext x
    simp [Mcol, mainRankOneMultiplier, neg_smul]
  let T := mainEuclideanTensorMap (κ := s) (ρ := Fin 2)
  let Aop := mainSmoothHilbertOperator U (fun x => T (ψ x))
    (T.contDiff.comp (mainQ3FiniteValue_contDiff whiteBasis s b L))
  have hA : MemLp (fun x => mainEuclideanTensor (ψ x) (F x)) 2
      (normalizedCubeMeasure U) := by
    change MemLp (fun x => T (ψ x) (F x)) 2 (normalizedCubeMeasure U)
    exact Aop.product_memLp hF
  have hAdd := main_hilbert_positive_add U hA hB hT.1 hCol.1
  have hL2F := main_hilbertL2_le_positive U hF hPF
  have hFirst :
      Real.sqrt (b^2) * hilbertPositiveHaarNorm U (Real.sqrt 3) F +
        cubeScaleFactor U * planarC1 * Real.sqrt ((156/5)*b^2/L.1^2) *
          hilbertL2Norm U F ≤
      (Real.sqrt (b^2) + cubeScaleFactor U * planarC1 *
          Real.sqrt ((156/5)*b^2/L.1^2)) *
        hilbertPositiveHaarNorm U (Real.sqrt 3) F := by
    have hc : 0 ≤ cubeScaleFactor U * planarC1 *
        Real.sqrt ((156/5:ℝ)*b^2/L.1^2) := by
      have hc1 : 0 ≤ planarC1 := by
        unfold planarC1
        exact Real.sqrt_nonneg _
      exact mul_nonneg (mul_nonneg (Triadic.cubeScaleFactor_pos' U).le hc1)
        (Real.sqrt_nonneg _)
    calc
      _ ≤ Real.sqrt (b^2) * hilbertPositiveHaarNorm U (Real.sqrt 3) F +
          cubeScaleFactor U * planarC1 * Real.sqrt ((156/5)*b^2/L.1^2) *
            hilbertPositiveHaarNorm U (Real.sqrt 3) F :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hL2F hc)
      _ = _ := by ring
  have hbound : hilbertPositiveHaarNorm U (Real.sqrt 3) C ≤
      hilbertPositiveHaarNorm U (Real.sqrt 3)
          (fun x => mainEuclideanTensor (ψ x) (F x)) +
        hilbertPositiveHaarNorm U (Real.sqrt 3)
          (fun x => (-zU.toFun x) • mainQ3FiniteColumn whiteBasis s b L x) := by
    change hilbertPositiveHaarNorm U (Real.sqrt 3)
        (fun x => mainEuclideanTensor (ψ x) (F x) +
          (-zU.toFun x) • mainQ3FiniteColumn whiteBasis s b L x) ≤ _
    exact hAdd.2
  refine ⟨hA.add hB, hAdd.1, ?_⟩
  have hbound' : hilbertPositiveHaarNorm U (Real.sqrt 3) C ≤
      (Real.sqrt (b^2) + cubeScaleFactor U * planarC1 *
          Real.sqrt ((156/5)*b^2/L.1^2)) *
          hilbertPositiveHaarNorm U (Real.sqrt 3) F +
        Real.sqrt ((156/5)*b^2/L.1^2) * positiveHaarNorm U zU.toFun +
        cubeScaleFactor U * planarC1 *
          Real.sqrt ((46488/25)*b^2/L.1^4) * Real.sqrt (energy U zU.toFun) := by
    calc
      _ ≤ hilbertPositiveHaarNorm U (Real.sqrt 3)
            (fun x => mainEuclideanTensor (ψ x) (F x)) +
          hilbertPositiveHaarNorm U (Real.sqrt 3)
            (fun x => (-zU.toFun x) • mainQ3FiniteColumn whiteBasis s b L x) := hbound
      _ ≤ (Real.sqrt (b^2) + cubeScaleFactor U * planarC1 *
            Real.sqrt ((156/5)*b^2/L.1^2)) *
            hilbertPositiveHaarNorm U (Real.sqrt 3) F +
          (Real.sqrt ((156/5)*b^2/L.1^2) * positiveHaarNorm U zU.toFun +
            cubeScaleFactor U * planarC1 *
              Real.sqrt ((46488/25)*b^2/L.1^4) * Real.sqrt (energy U zU.toFun)) :=
        add_le_add (hT.2.trans hFirst) hCol.2
      _ = _ := by ring
  have heqZ : zU.toFun = (v-I v).toFun := rfl
  rw [hPHF] at hbound'
  simpa only [C, F, ψ, z, zU, heqZ,
    hilbertPositiveHaarNorm, hilbertL2Norm, hilbertPrimalEnergy_real,
    hilbertEnergy_real] using hbound'

private theorem square_raw_row_tile_energy_eq
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q))
    (s : Finset whiteBasisIndex) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q j) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    ∑ l ∈ s, vectorPositiveHaarEnergy U (lemmaVPlanarRowField
        (diagInterpolant Q j)
        (squareQ3BasisMultiplier Q b 1 L l) v) =
      hilbertPrimalEnergy U (Real.sqrt 3)
        (pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j v) := by
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q j
  let C := pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j v
  have hlocal := square_raw_row_tile_bound Q j p u s U hU b L
  have hmem : MemLp C 2 (normalizedCubeMeasure U) := by
    simpa only [C] using hlocal.1
  have hsum : Summable (fun k => (Real.sqrt 3)^(k+1) * hilbertEnergy U
      (hilbertCubeIncrement U (k+1) C)) := by
    simpa only [C] using hlocal.2.1
  have hrow (l : s) :
      vectorPositiveHaarEnergy U (lemmaVPlanarRowField I
        (squareQ3BasisMultiplier Q b 1 L l) v) =
        ∑ i : Fin 2, primalEnergy U (Real.sqrt 3)
          (fun x => (C x).ofLp (l,i)) := by
    let η := squareQ3BasisMultiplier Q b 1 L l
    let f := fun x i => η.toFun x * (I v).grad x i - η.grad x i * (v-I v).toFun x
    have heta : η = (mainQ3DirectionW2 Q b L (whiteBasis l)).value := by
      simp [η, squareQ3BasisMultiplier]
    have hvalue (x : Vec 2) : η.toFun x =
        q3Convolution b L h3Zero (whiteBasis l) x := by
      rw [heta, mainQ3DirectionW2_value]
    have hgrad (x : Vec 2) (i : Fin 2) : η.grad x i =
        (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis l)) x)
          (basisVec i) := by
      have hj := mainQ3DirectionW2_jet Q b L (whiteBasis l) (.first i) x
      change (mainQ3DirectionW2 Q b L (whiteBasis l)).value.grad x i =
        q3Convolution b L (mainQ3JetIndex (.first i)) (whiteBasis l) x at hj
      have hderiv : (fderiv ℝ (q3Convolution b L h3Zero
          (whiteBasis l)) x) (basisVec i) =
          q3Convolution b L (mainQ3JetIndex (.first i))
            (whiteBasis l) x := by
        rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
        fin_cases i <;> norm_num [mainQ3JetIndex, h3Next, h3Zero,
          Model.Q3SpatialJet.count]
      rw [heta]
      exact hj.trans hderiv.symm
    have hcoord (x : Vec 2) (i : Fin 2) :
        (C x).ofLp (l,i) = f x i := by
      rw [square_raw_row_coordinate]
      simp only [f]
      rw [hvalue, hgrad]
      ring
    have hfield : (fun x => lemmaVPlanarRowField I η v x) =
        (fun x => planarQuarterTurn (f x)) := by
      rw [lemmaVH2_rowField_eq]
    have hturn : vectorPositiveHaarEnergy U (lemmaVPlanarRowField I η v) =
        vectorPositiveHaarEnergy U f := by
      calc
        _ = vectorPositiveHaarEnergy U (fun x => planarQuarterTurn (f x)) := by
          exact congrArg (vectorPositiveHaarEnergy U) hfield
        _ = vectorPositiveHaarEnergy U f := main_vectorPositiveHaarEnergy_quarterTurn U f
    rw [hturn]
    unfold vectorPositiveHaarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    have hfun : (fun x => f x i) = fun x => (C x).ofLp (l,i) := by
      funext x
      exact (hcoord x i).symm
    rw [hfun]
  calc
    _ = ∑ l : s, vectorPositiveHaarEnergy U (lemmaVPlanarRowField I
          (squareQ3BasisMultiplier Q b 1 L l) v) :=
        (Finset.sum_coe_sort s _).symm
    _ = ∑ l : s, ∑ i : Fin 2, primalEnergy U (Real.sqrt 3)
          (fun x => (C x).ofLp (l,i)) := by
        apply Finset.sum_congr rfl
        intro l hl
        exact hrow l
    _ = hilbertPrimalEnergy U (Real.sqrt 3) C := by
        symm
        rw [main_hilbertPrimalEnergy_euclidean U hmem hsum,
          Fintype.sum_prod_type]

/-- Sharp finite-family trace bound for the actual q3 source rows. The value
column retains its full cell mean; the residual and derivative terms use the
full 31.2 and 1859.52 column traces. -/
theorem square_row_trace_finset_sharp
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q))
    (s : Finset whiteBasisIndex) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Real.sqrt (∑ l ∈ s, squareQ3RowEnergy Q b 1 L m p u l) ≤
      (Real.sqrt (b^2) + diagMeshRadius Q m * (36/25) *
          Real.sqrt ((156/5)*b^2/L.1^2) +
        (diagMeshRadius Q m)^2 * (57/200) *
          Real.sqrt ((46488/25)*b^2/L.1^4)) *
        Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
  intro v
  let I := diagInterpolant Q m
  let z := v-I v
  let r := diagMeshRadius Q m
  let σ₁ := Real.sqrt ((156/5:ℝ)*b^2/L.1^2)
  let σ₂ := Real.sqrt ((46488/25:ℝ)*b^2/L.1^4)
  let A := Real.sqrt (b^2) + r*planarC1*σ₁
  let B := σ₁
  let C := r*planarC1*σ₂
  let E := fun U : TriadicCube 2 => hilbertPrimalEnergy U (Real.sqrt 3)
    (pureFluxMainQ3FiniteRawRow whiteBasis s b L Q m v)
  let F := fun U : TriadicCube 2 => vectorPositiveHaarEnergy U (I v).grad
  let G := fun U : TriadicCube 2 => primalEnergy U (Real.sqrt 3) z.toFun
  let H := fun U : TriadicCube 2 => energy U z.toFun
  have hRowsAvg : (∑ l ∈ s, squareQ3RowEnergy Q b 1 L m p u l) =
      descendantsAverage Q m E := by
    unfold squareQ3RowEnergy
    rw [← main_descendantsAverage_finset_sum Q m s
      (fun l U => vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField (diagInterpolant Q m)
          (squareQ3BasisMultiplier Q b 1 L l) v))]
    unfold descendantsAverage
    apply congrArg (fun x : ℝ => ((descendantsAtDepth Q m).card : ℝ)⁻¹ * x)
    apply Finset.sum_congr rfl
    intro U hU
    change (∑ l ∈ s, vectorPositiveHaarEnergy U
      (lemmaVPlanarRowField (diagInterpolant Q m)
        (squareQ3BasisMultiplier Q b 1 L l) v)) = E U
    simpa only [v, E] using
      (square_raw_row_tile_energy_eq Q b L m p u s U hU)
  have hE_nonneg (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :
      0 ≤ E U := by
    change 0 ≤ hilbertPrimalEnergy U (Real.sqrt 3)
      (pureFluxMainQ3FiniteRawRow whiteBasis s b L Q m v)
    rw [← square_raw_row_tile_energy_eq Q b L m p u s U hU]
    exact Finset.sum_nonneg fun l hl => vectorPositiveHaarEnergy_nonneg U
      (lemmaVPlanarRowField (diagInterpolant Q m)
        (squareQ3BasisMultiplier Q b 1 L l) v)
  have hF_nonneg (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q m) : 0 ≤ F U :=
    vectorPositiveHaarEnergy_nonneg U (I v).grad
  have hG_nonneg (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q m) : 0 ≤ G U :=
    primalEnergy_nonneg U (Real.sqrt 3) (Real.sqrt_nonneg _) z.toFun
  have hH_nonneg (U : TriadicCube 2) (_hU : U ∈ descendantsAtDepth Q m) : 0 ≤ H U :=
    energy_nonneg U z.toFun
  have hr : 0 ≤ r := (diagMeshRadius_pos Q m).le
  have hσ₁ : 0 ≤ σ₁ := Real.sqrt_nonneg _
  have hσ₂ : 0 ≤ σ₂ := Real.sqrt_nonneg _
  have hc1 : 0 ≤ planarC1 := by
    unfold planarC1
    exact Real.sqrt_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; exact hσ₁
  have hC : 0 ≤ C := by dsimp [C]; exact mul_nonneg (mul_nonneg hr hc1) hσ₂
  have hlocal (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :
      Real.sqrt (E U) ≤ A*Real.sqrt (F U)+B*Real.sqrt (G U)+C*Real.sqrt (H U) := by
    have ht := square_raw_row_tile_bound Q m p u s U hU b L
    change Real.sqrt (E U) ≤ _
    simpa only [E, F, G, H, A, B, C, r,
      cubeScaleFactor_descendant_eq_div_pow hU, diagMeshRadius,
      hilbertPositiveHaarNorm, vectorPositiveHaarNorm, positiveHaarNorm] using ht.2.2
  have hagg := sqrt_descendantsAverage_energy_bound_three Q m E F G H hA hB hC
    hE_nonneg hF_nonneg hG_nonneg hH_nonneg hlocal
  rw [hRowsAvg]
  have hFavg : descendantsAverage Q m F = lemmaVTiledPositiveEnergy Q m (I v).grad := rfl
  have hGavg : descendantsAverage Q m G = diagTiledScalarPositiveEnergy Q m z.toFun := rfl
  have hHavg : descendantsAverage Q m H = energy Q z.toFun :=
    (energy_eq_descendantsAverage Q m z.memL2_normalizedCubeMeasure).symm
  rw [hFavg, hGavg, hHavg] at hagg
  have hgrad := diagInterpolant_gradient_estimate Q m p u
  have hresP := diagInterpolant_residual_positive_estimate Q m p u
  have hresL := diagInterpolant_residual_L2_estimate Q m p u
  have hW : 0 ≤ lemmaVTiledWeakEnergy Q m v.grad := lemmaVTiledWeakEnergy_nonneg Q m v.grad
  have hrootW : 0 ≤ Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := Real.sqrt_nonneg _
  have hagg' : Real.sqrt (descendantsAverage Q m E) ≤
      A*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
        B*(r*(2/Real.pi+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)) +
        C*(r*(planarC0+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)) := by
    calc
      _ ≤ A*Real.sqrt (lemmaVTiledPositiveEnergy Q m (I v).grad) +
          B*Real.sqrt (diagTiledScalarPositiveEnergy Q m z.toFun) +
          C*Real.sqrt (energy Q z.toFun) := hagg
      _ ≤ _ := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hgrad hA
          · exact mul_le_mul_of_nonneg_left hresP hB
        · exact mul_le_mul_of_nonneg_left hresL hC
  have hcoeff1 : r*(planarC1+2/Real.pi+1/2)*σ₁*
      Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) ≤
        r*(36/25)*σ₁*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
    calc
      _ = r*((planarC1+2/Real.pi+1/2)*(σ₁*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad))) := by ring
      _ ≤ r*((36/25)*(σ₁*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right lemmaVH2C1_outward
            (mul_nonneg hσ₁ hrootW)) hr
      _ = _ := by ring
  have hcoeff2 : r^2*(planarC1*(planarC0+1/2))*σ₂*
      Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) ≤
        r^2*(57/200)*σ₂*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
    calc
      _ = r^2*((planarC1*(planarC0+1/2))*(σ₂*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad))) := by ring
      _ ≤ r^2*((57/200)*(σ₂*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right lemmaVH2C2_outward
            (mul_nonneg hσ₂ hrootW)) (sq_nonneg r)
      _ = _ := by ring
  calc
    _ ≤ A*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
        B*(r*(2/Real.pi+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)) +
        C*(r*(planarC0+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)) := hagg'
    _ = (Real.sqrt (b^2) +
          r*(planarC1+2/Real.pi+1/2)*σ₁ +
          r^2*(planarC1*(planarC0+1/2))*σ₂) *
        Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
          simp only [A, B, C, r, σ₁, σ₂]
          ring
    _ ≤ (Real.sqrt (b^2) + r*(36/25)*σ₁ + r^2*(57/200)*σ₂) *
        Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
          calc
            (Real.sqrt (b^2) +
                r*(planarC1+2/Real.pi+1/2)*σ₁ +
                r^2*(planarC1*(planarC0+1/2))*σ₂) *
                Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) =
              Real.sqrt (b^2)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
                (r*(planarC1+2/Real.pi+1/2)*σ₁)*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
                (r^2*(planarC1*(planarC0+1/2))*σ₂)*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by ring
            _ ≤ Real.sqrt (b^2)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
                (r*(36/25)*σ₁)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
                (r^2*(57/200)*σ₂)*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) :=
              add_le_add (add_le_add le_rfl hcoeff1) hcoeff2
            _ = (Real.sqrt (b^2) + r*(36/25)*σ₁ +
                r^2*(57/200)*σ₂) *
                Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by ring
    _ = _ := by simp only [r, σ₁, σ₂]

end
end ASDExplicitGamma.Gaussian
