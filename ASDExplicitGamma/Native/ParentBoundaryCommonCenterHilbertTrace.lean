module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertTile

/-! The complete common-parent-center Hilbert--Schmidt row trace, with the
source column constants. Generalized from Inverse/PureFluxGeneratorCenteredTrace. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped BigOperators
noncomputable section

local instance parentCommonHilbertTraceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- A genuine W^{2,∞} direction on Q, with its one original source-cell center P. -/
def parentBoundaryCommonQ3Direction (P Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) : PlanarW2Infinity Q where
  value := (mainQ3DirectionW2 Q b L w).value - pureFluxH1Constant Q
    (q3Convolution b L h3Zero w (cubeCenter P))
  value_memLp_top := by
    have hh := (mainQ3DirectionW2 Q b L w).value_memLp_top.sub
      (memLp_const (q3Convolution b L h3Zero w (cubeCenter P)))
    convert hh using 1
    funext x
    simp only [H1Function.sub_toFun,pureFluxH1Constant_toFun,Pi.sub_apply]
  gradient := (mainQ3DirectionW2 Q b L w).gradient
  gradient_eq i := by
    simp only [H1Function.sub_grad,pureFluxH1Constant_grad,Pi.sub_apply,Pi.zero_apply,sub_zero]
    exact (mainQ3DirectionW2 Q b L w).gradient_eq i

/-- Literal value of the actual common-center W^{2,∞} direction. -/
theorem parent_boundary_common_q3_direction_value (P Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (x : Vec 2) :
    (parentBoundaryCommonQ3Direction P Q b L w).value.toFun x =
      q3Convolution b L h3Zero w x-q3Convolution b L h3Zero w (cubeCenter P) := by
  simp only [parentBoundaryCommonQ3Direction,H1Function.sub_toFun,pureFluxH1Constant_toFun,mainQ3DirectionW2_value]

/-- The common center affects only value, never the physical first jets. -/
theorem parent_boundary_common_q3_direction_grad (P Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (x : Vec 2) (i : Fin 2) :
    (parentBoundaryCommonQ3Direction P Q b L w).value.grad x i =
      q3Convolution b L (mainQ3JetIndex (.first i)) w x := by
  rw [← congrFun ((parentBoundaryCommonQ3Direction P Q b L w).gradient_eq i) x]
  change ((mainQ3DirectionW2 Q b L w).gradient.component i).toFun x = _
  rw [congrFun ((mainQ3DirectionW2 Q b L w).gradient_eq i) x]
  exact mainQ3DirectionW2_jet Q b L w (.first i) x

/-- Physical-frame common-center basis multiplier. -/
def parentBoundaryCommonBasisMultiplier (P Q : TriadicCube 2) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) : H1Function (openCubeSet Q) :=
  (σ⁻¹ : ℝ) • (parentBoundaryCommonQ3Direction P Q b L (whiteBasis l)).value

/-- Actual complete positive energy of one common-center covariance row. -/
def parentBoundaryCommonRowEnergy (P Q : TriadicCube 2) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (m : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) (l : whiteBasisIndex) : ℝ :=
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  descendantsAverage Q m (fun U => vectorPositiveHaarEnergy U
    (lemmaVPlanarRowField (diagInterpolant Q m) (parentBoundaryCommonBasisMultiplier P Q b σ L l) v))

theorem parent_boundary_common_finite_row_coordinate {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (P Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (l : s) (i : Fin 2) (x : Vec 2) :
    (parentBoundaryCommonFiniteRawRow e s b L P Q j v x).ofLp (l,i) =
      (q3Convolution b L h3Zero (e l) x -
        q3Convolution b L h3Zero (e l) (cubeCenter P)) *
        (diagInterpolant Q j v).grad x i -
          (v-diagInterpolant Q j v).toFun x *
            (fderiv ℝ (q3Convolution b L h3Zero (e l)) x) (basisVec i) := by
  simp only [parentBoundaryCommonFiniteRawRow, mainEuclideanTensor,
    WithLp.ofLp_toLp, PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
    mainQ3FiniteValue, mainQ3FiniteColumn, smul_eq_mul]
  ring

theorem parent_boundary_common_hilbert_tile_energy
    (P Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P) (b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q))
    (s : Finset whiteBasisIndex) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q j) :
      let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    ∑ l ∈ s, vectorPositiveHaarEnergy U (lemmaVPlanarRowField
        (diagInterpolant Q j)
        (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v) =
      hilbertPrimalEnergy U (Real.sqrt 3)
        (parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q j v) := by
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q j
  let C := parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q j v
  have hlocal := parent_boundary_common_center_hilbert_tile P Q hQP j p u s U hU b L
  have hmem : MemLp C 2 (normalizedCubeMeasure U) := by
    simpa only [C] using hlocal.1
  have hsum : Summable (fun k => (Real.sqrt 3)^(k+1) * hilbertEnergy U
      (hilbertCubeIncrement U (k+1) C)) := by
    simpa only [C] using hlocal.2.1
  have hrow (l : s) :
      vectorPositiveHaarEnergy U (lemmaVPlanarRowField I
        (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v) =
        ∑ i : Fin 2, primalEnergy U (Real.sqrt 3)
          (fun x => (C x).ofLp (l,i)) := by
    let η := parentBoundaryCommonBasisMultiplier P Q b 1 L l
    let f := fun x i => η.toFun x * (I v).grad x i - η.grad x i * (v-I v).toFun x
    have heta : η = (parentBoundaryCommonQ3Direction P Q b L (whiteBasis l)).value := by
      simp [η, parentBoundaryCommonBasisMultiplier]
    have hvalue (x : Vec 2) : η.toFun x =
        q3Convolution b L h3Zero (whiteBasis l) x -
          q3Convolution b L h3Zero (whiteBasis l) (cubeCenter P) := by
      rw [heta, parent_boundary_common_q3_direction_value]
    have hgrad (x : Vec 2) (i : Fin 2) : η.grad x i =
        (fderiv ℝ (q3Convolution b L h3Zero (whiteBasis l)) x)
          (basisVec i) := by
      have hj := parent_boundary_common_q3_direction_grad P Q b L (whiteBasis l) x i
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
      rw [parent_boundary_common_finite_row_coordinate]
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
          (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v) :=
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

theorem parent_boundary_common_hilbert_trace_finset
    (P Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P) (b : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q))
    (s : Finset whiteBasisIndex) :
      let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Real.sqrt (∑ l ∈ s, parentBoundaryCommonRowEnergy P Q b 1 L m p u l) ≤
      (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) + diagMeshRadius Q m * (36/25) *
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
  let A := Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) + r*planarC1*σ₁
  let B := σ₁
  let C := r*planarC1*σ₂
  let E := fun U : TriadicCube 2 => hilbertPrimalEnergy U (Real.sqrt 3)
    (parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q m v)
  let F := fun U : TriadicCube 2 => vectorPositiveHaarEnergy U (I v).grad
  let G := fun U : TriadicCube 2 => primalEnergy U (Real.sqrt 3) z.toFun
  let H := fun U : TriadicCube 2 => energy U z.toFun
  have hRowsAvg : (∑ l ∈ s, parentBoundaryCommonRowEnergy P Q b 1 L m p u l) =
      descendantsAverage Q m E := by
    unfold parentBoundaryCommonRowEnergy
    rw [← main_descendantsAverage_finset_sum Q m s
      (fun l U => vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField (diagInterpolant Q m)
          (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v))]
    unfold descendantsAverage
    apply congrArg (fun x : ℝ => ((descendantsAtDepth Q m).card : ℝ)⁻¹ * x)
    apply Finset.sum_congr rfl
    intro U hU
    change (∑ l ∈ s, vectorPositiveHaarEnergy U
      (lemmaVPlanarRowField (diagInterpolant Q m)
        (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v)) = E U
    simpa only [v, E] using
      (parent_boundary_common_hilbert_tile_energy P Q hQP b L m p u s U hU)
  have hE_nonneg (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :
      0 ≤ E U := by
    change 0 ≤ hilbertPrimalEnergy U (Real.sqrt 3)
      (parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q m v)
    rw [← parent_boundary_common_hilbert_tile_energy P Q hQP b L m p u s U hU]
    exact Finset.sum_nonneg fun l hl => vectorPositiveHaarEnergy_nonneg U
      (lemmaVPlanarRowField (diagInterpolant Q m)
        (parentBoundaryCommonBasisMultiplier P Q b 1 L l) v)
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
    have ht := parent_boundary_common_center_hilbert_tile P Q hQP m p u s U hU b L
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
    _ = (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) +
          r*(planarC1+2/Real.pi+1/2)*σ₁ +
          r^2*(planarC1*(planarC0+1/2))*σ₂) *
        Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
          simp only [A, B, C, r, σ₁, σ₂]
          ring
    _ ≤ (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) + r*(36/25)*σ₁ + r^2*(57/200)*σ₂) *
        Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
          calc
            (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) +
                r*(planarC1+2/Real.pi+1/2)*σ₁ +
                r^2*(planarC1*(planarC0+1/2))*σ₂) *
                Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) =
              Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
                (r*(planarC1+2/Real.pi+1/2)*σ₁)*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
                (r^2*(planarC1*(planarC0+1/2))*σ₂)*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by ring
            _ ≤ Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
                (r*(36/25)*σ₁)*Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) +
                (r^2*(57/200)*σ₂)*
                  Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) :=
              add_le_add (add_le_add le_rfl hcoeff1) hcoeff2
            _ = (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) + r*(36/25)*σ₁ +
                r^2*(57/200)*σ₂) *
                Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by ring
    _ = _ := by simp only [r, σ₁, σ₂]

end
end ASDExplicitGamma.Native
