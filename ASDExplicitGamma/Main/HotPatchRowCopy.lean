module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorSharpTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Main.HilbertTensorProduct
public import ASDExplicitGamma.Main.Q3ColumnH1Product
public import ASDExplicitGamma.Main.HilbertPositiveTriangle
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates
public import ASDExplicitGamma.Triadic.DiagEstimates
public import ASDExplicitGamma.Triadic.PositiveNormAggregation
public import ASDExplicitGamma.Variational.LemmaVH2Constants

/-! Public copies of the private tile lemmas of `PureFluxGeneratorSharpTrace`
(unchanged proofs), needed for the hot-patched row. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
open scoped BigOperators

namespace ASDExplicitGamma.Inverse

local instance hotCopyFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem pureFluxMainQ3FiniteRawRow_coordinate_hotcopy {ι : Type*}
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

theorem pureFluxMainQ3FiniteRawRow_tile_bound_hotcopy
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

theorem pureFluxMainQ3FiniteRawRow_tile_energy_eq_hotcopy
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (s : Finset whiteBasisIndex) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) j) :
    let Q := originCube 2 n
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    ∑ l ∈ s, vectorPositiveHaarEnergy U (lemmaVPlanarRowField
        (diagInterpolant Q j)
        (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) v) =
      hilbertPrimalEnergy U (Real.sqrt 3)
        (pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j v) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q j
  let C := pureFluxMainQ3FiniteRawRow whiteBasis s b L Q j v
  have hlocal := pureFluxMainQ3FiniteRawRow_tile_bound_hotcopy Q j p u s U hU b L
  have hmem : MemLp C 2 (normalizedCubeMeasure U) := by
    simpa only [C] using hlocal.1
  have hsum : Summable (fun k => (Real.sqrt 3)^(k+1) * hilbertEnergy U
      (hilbertCubeIncrement U (k+1) C)) := by
    simpa only [C] using hlocal.2.1
  have hrow (l : s) :
      vectorPositiveHaarEnergy U (lemmaVPlanarRowField I
        (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) v) =
        ∑ i : Fin 2, primalEnergy U (Real.sqrt 3)
          (fun x => (C x).ofLp (l,i)) := by
    let η := pureFluxMainQ3BasisFrameMultiplier n b 1 L l
    let f := fun x i => η.toFun x * (I v).grad x i - η.grad x i * (v-I v).toFun x
    have heta : η = (mainQ3DirectionW2 Q b L (whiteBasis l)).value := by
      simp [η, pureFluxMainQ3BasisFrameMultiplier, Q]
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
      rw [pureFluxMainQ3FiniteRawRow_coordinate_hotcopy]
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
          (pureFluxMainQ3BasisFrameMultiplier n b 1 L l) v) :=
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

end ASDExplicitGamma.Inverse
