module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowOperator
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Main.HilbertCoordinateMembership
public import ASDExplicitGamma.Triadic.DiagAffine

/-! The covariance row acts on distinct zero-trace first potentials. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Model
open scoped BigOperators
noncomputable section

/-- At depth zero the H10 DIAG interpolant has no interior degrees of freedom. -/
theorem pureFlux_diagInterpolant_zero_h10 (Q : TriadicCube 2)
    (z : H10Function (openCubeSet Q)) :
    diagInterpolant Q 0 z.toH1Function = 0 := by
  change diagAffineLinear Q (diagMeanGradientLinear Q z.toH1Function) +
    diagSynthesisH1Linear Q 0 (diagNodalValuesLinear Q 0 z.toH1Function) = 0
  rw [diagMeanGradient_h10, map_zero, zero_add]
  simp [diagSynthesisH1Linear]

/-- The finite Hilbert-valued array of actual first potentials. -/
def pureFluxH10FiniteFamily {ι : Type*} (s : Finset ι) (Q : TriadicCube 2)
    (z : ι → H10Function (openCubeSet Q)) (x : Vec 2) : EuclideanSpace ℝ s :=
  WithLp.toLp 2 (fun l => (z l).toH1Function.toFun x)

theorem pureFluxH10FiniteFamily_memLp {ι : Type*} (s : Finset ι) (Q : TriadicCube 2)
    (z : ι → H10Function (openCubeSet Q)) :
    MemLp (pureFluxH10FiniteFamily s Q z) 2 (normalizedCubeMeasure Q) := by
  apply memLp_piLp_iff.mpr
  intro l
  exact (z l).toH1Function.memL2_normalizedCubeMeasure

theorem pureFluxH10FiniteFamily_positive_summable {ι : Type*} (s : Finset ι)
    (Q : TriadicCube 2) (z : ι → H10Function (openCubeSet Q)) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (pureFluxH10FiniteFamily s Q z))) := by
  apply main_hilbert_summable_of_coordinates Q (pureFluxH10FiniteFamily_memLp s Q z)
  intro l
  exact positiveHaarIncrementSeries_summable Q
    (z l).toH1Function.memL2_normalizedCubeMeasure
    (z l).toH1Function.grad_memL2_normalizedCubeMeasure (z l).toH1Function.hasWeakGradient

private theorem pureFluxH10FiniteFamily_positive_bound {ι : Type*} (s : Finset ι)
    (Q : TriadicCube 2) (z : ι → H10Function (openCubeSet Q)) :
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (pureFluxH10FiniteFamily s Q z) ≤
      cubeScaleFactor Q*planarFD*
        Real.sqrt (∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad) := by
  have hw : 0 ≤ ∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad :=
    Finset.sum_nonneg fun l _ => vectorWeakHaarEnergy_nonneg Q _
  unfold hilbertPositiveHaarNorm
  apply diagSqrt_energy_bound hw
    (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le (by unfold planarFD; positivity))
  rw [main_hilbertPrimalEnergy_euclidean Q (pureFluxH10FiniteFamily_memLp s Q z)
    (pureFluxH10FiniteFamily_positive_summable s Q z)]
  have hper (l : s) : primalEnergy Q (Real.sqrt 3) (z l).toH1Function.toFun ≤
      cubeScaleFactor Q^2*planarFD^2*vectorWeakHaarEnergy Q (z l).toH1Function.grad := by
    have h := dirichlet_positiveHaar_bridge_sq Q (z l)
    simp only [positiveHaarNorm, vectorWeakHaarNorm] at h
    rw [Real.sq_sqrt (primalEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) _),
      Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)] at h
    exact h
  calc
    _ ≤ ∑ l : s, cubeScaleFactor Q^2*planarFD^2*
        vectorWeakHaarEnergy Q (z l).toH1Function.grad := Finset.sum_le_sum fun l _ => hper l
    _ = _ := by rw [← Finset.mul_sum]; ring

private theorem pureFluxH10FiniteFamily_L2_bound {ι : Type*} (s : Finset ι)
    (Q : TriadicCube 2) (z : ι → H10Function (openCubeSet Q)) :
    hilbertL2Norm Q (pureFluxH10FiniteFamily s Q z) ≤
      cubeScaleFactor Q*planarCD*
        Real.sqrt (∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad) := by
  have hw : 0 ≤ ∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad :=
    Finset.sum_nonneg fun l _ => vectorWeakHaarEnergy_nonneg Q _
  unfold hilbertL2Norm
  apply diagSqrt_energy_bound hw
    (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _))
  rw [main_hilbertEnergy_euclidean Q (pureFluxH10FiniteFamily_memLp s Q z)]
  have hper (l : s) : energy Q (z l).toH1Function.toFun ≤
      cubeScaleFactor Q^2*planarCD^2*vectorWeakHaarEnergy Q (z l).toH1Function.grad := by
    have h := dirichlet_L2_bridge_sq Q (z l)
    simp only [vectorWeakHaarNorm] at h
    rw [Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)] at h
    exact h
  calc
    _ ≤ ∑ l : s, cubeScaleFactor Q^2*planarCD^2*
        vectorWeakHaarEnergy Q (z l).toH1Function.grad := Finset.sum_le_sum fun l _ => hper l
    _ = _ := by rw [← Finset.mul_sum]; dsimp only [planarCD]; ring

private theorem pureFlux_planarCD_le : planarCD ≤ planarC0 + 1/2 := by
  have hsq : planarCD^2 ≤ planarC0^2 := by
    rw [planarCD_sq, planarC0_sq_eq_planarC1_sq_add]
    apply add_le_add le_rfl
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith only [sq_nonneg Real.pi]
  have hle : planarCD ≤ planarC0 :=
    (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp hsq
  linarith

/-- Sharp covariance-row products allow a different H10 first potential in
 every Gaussian direction. The operator covariance is discharged internally. -/
theorem pureFluxQ3_distinct_h10_product {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (z : ι → H10Function (openCubeSet Q)) :
    let A := pureFluxQ3DerivativeRow e s b L Q
    let Z := pureFluxH10FiniteFamily s Q z
    Summable (fun k => (Real.sqrt 3)^(k+1)*hilbertEnergy Q
      (hilbertCubeIncrement Q (k+1) (fun x => A.toFun x (Z x)))) ∧
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (fun x => A.toFun x (Z x)) ≤
      (cubeScaleFactor Q*(36/25)*Real.sqrt ((78/5)*b^2/L.1^2) +
        (cubeScaleFactor Q)^2*(57/200)*Real.sqrt ((23244/25)*b^2/L.1^4))*
          Real.sqrt (∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad) := by
  intro A Z
  let G := Real.sqrt ((78/5:ℝ)*b^2/L.1^2)
  let H := Real.sqrt ((23244/25:ℝ)*b^2/L.1^4)
  let W := ∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hq9 : Real.sqrt 3 < 9 := by
    nlinarith only [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hM : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖A.toFun x‖ ≤ G :=
    Filter.Eventually.of_forall (pureFluxQ3DerivativeRow_norm_le e s b L Q)
  have hD : ∀ᵐ x ∂normalizedCubeMeasure Q, ∀ c : EuclideanSpace ℝ s,
      (∑ i, ‖A.grad x i c‖^2) ≤ H^2*‖c‖^2 := by
    apply Filter.Eventually.of_forall
    intro x c
    dsimp only [H]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (23244/25:ℝ)*b^2/L.1^4)]
    exact pureFluxQ3DerivativeRow_combined_gradient_le e s b L Q x c
  have h := pureFlux_positive_product_of_combined_bounds A hq hq9
    (pureFluxH10FiniteFamily_memLp s Q z) (pureFluxH10FiniteFamily_positive_summable s Q z)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hM hD
  have hc1 : Real.sqrt (haarPoincareM2 (Real.sqrt 3)) = planarC1 := by
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
    rfl
  rw [hc1] at h
  have hFD : planarFD ≤ (36/25:ℝ) := by linarith only [planarFD_lt_decimal]
  have hCD : planarC1*planarCD ≤ (57/200:ℝ) :=
    (mul_le_mul_of_nonneg_left pureFlux_planarCD_le (Real.sqrt_nonneg _)).trans
      lemmaVH2C2_outward
  have hr : 0 ≤ cubeScaleFactor Q := (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
  have hG : 0 ≤ G := Real.sqrt_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    G*hilbertPositiveHaarNorm Q (Real.sqrt 3) Z +
        cubeScaleFactor Q*planarC1*H*hilbertL2Norm Q Z ≤
      G*(cubeScaleFactor Q*planarFD*Real.sqrt W) +
        cubeScaleFactor Q*planarC1*H*(cubeScaleFactor Q*planarCD*Real.sqrt W) :=
      add_le_add (mul_le_mul_of_nonneg_left (pureFluxH10FiniteFamily_positive_bound s Q z) hG)
        (mul_le_mul_of_nonneg_left (pureFluxH10FiniteFamily_L2_bound s Q z)
          (mul_nonneg (mul_nonneg hr (Real.sqrt_nonneg _)) hH))
    _ = (cubeScaleFactor Q*planarFD*G +
        (cubeScaleFactor Q)^2*(planarC1*planarCD)*H)*Real.sqrt W := by ring
    _ ≤ (cubeScaleFactor Q*(36/25)*G +
        (cubeScaleFactor Q)^2*(57/200)*H)*Real.sqrt W := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFD hr) hG)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCD (sq_nonneg _)) hH)
    _ = _ := rfl


/-- The actual direction row evaluated on distinct first potentials. -/
def pureFluxMainQ3DistinctRow (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l})
    (s : Finset whiteBasisIndex)
    (z : whiteBasisIndex → H10Function (openCubeSet (originCube 2 n))) : Vec 2 → Vec 2 :=
  fun x => ∑ l ∈ s, lemmaVPlanarRowField (diagInterpolant (originCube 2 n) 0)
    (pureFluxMainQ3BasisFrameMultiplier n b σ L l) (z l).toH1Function x

private theorem pureFluxMainQ3DistinctRow_eq (n : ℤ) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (z : whiteBasisIndex → H10Function (openCubeSet (originCube 2 n))) :
    pureFluxMainQ3DistinctRow n b σ L s z =
      fun x => planarQuarterTurn (fun i => (-σ⁻¹) *
        (((pureFluxQ3DerivativeRow whiteBasis s b L (originCube 2 n)).toFun x)
          (pureFluxH10FiniteFamily s (originCube 2 n) z x)).ofLp i) := by
  let Q := originCube 2 n
  have hgrad (l : whiteBasisIndex) (x : Vec 2) (i : Fin 2) :
      (pureFluxMainQ3BasisFrameMultiplier n b σ L l).grad x i =
        σ⁻¹*q3Convolution b L (mainQ3JetIndex (.first i)) (whiteBasis l) x := by
    simp only [pureFluxMainQ3BasisFrameMultiplier, H1Function.smul_grad,
      Pi.smul_apply, smul_eq_mul]
    change σ⁻¹*q3DirectionJet (mainQ3DirectionW2 Q b L (whiteBasis l)) (.first i) x = _
    rw [mainQ3DirectionW2_jet]
  have hlocal (l : whiteBasisIndex) (x : Vec 2) (i : Fin 2) :
      lemmaVPlanarRowField (diagInterpolant Q 0)
        (pureFluxMainQ3BasisFrameMultiplier n b σ L l) (z l).toH1Function x i =
      planarQuarterTurn (fun a => (-σ⁻¹) * (z l).toH1Function.toFun x *
        q3Convolution b L (mainQ3JetIndex (.first a)) (whiteBasis l) x) i := by
    rw [lemmaVH2_rowField_eq, pureFlux_diagInterpolant_zero_h10 Q (z l)]
    simp only [H1Function.zero_grad, Pi.zero_apply, mul_zero, sub_zero,
      zero_sub, hgrad]
    fin_cases i <;> simp [planarQuarterTurn] <;> ring
  funext x i
  change (∑ l ∈ s, lemmaVPlanarRowField (diagInterpolant Q 0)
    (pureFluxMainQ3BasisFrameMultiplier n b σ L l) (z l).toH1Function x) i = _
  simp only [Finset.sum_apply, hlocal]
  rw [← Finset.sum_coe_sort s]
  fin_cases i <;>
    simp [planarQuarterTurn, pureFluxQ3DerivativeRow_apply, pureFluxH10FiniteFamily,
      Finset.mul_sum, Finset.sum_neg_distrib, mul_assoc, mul_left_comm, mul_comm]


private theorem pureFluxDistinct_increment_smul (Q : TriadicCube 2) (n : ℕ)
    (f : Vec 2 → ℝ) (c : ℝ) :
    cubeIncrement Q n (fun x => c*f x) = fun x => c*cubeIncrement Q n f x := by
  cases n with
  | zero => simp [cubeIncrement_zero, projection_smul]
  | succ n =>
    simp only [cubeIncrement_succ, projection_smul]
    funext x
    ring

private theorem pureFluxDistinct_energy_smul (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (c : ℝ) :
    energy Q (fun x => c*f x) = c^2*energy Q f := by
  rw [energy_eq_integral_sq, energy_eq_integral_sq]
  simp only [mul_pow]
  rw [integral_const_mul]

private theorem pureFluxDistinct_summable_smul (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (c : ℝ)
    (hP : Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) f))) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q
      (cubeIncrement Q (k+1) (fun x => c*f x))) := by
  refine (hP.mul_left (c^2)).congr ?_
  intro k
  rw [pureFluxDistinct_increment_smul, pureFluxDistinct_energy_smul]
  ring

/-- The actual scaled q3 covariance row acts on distinct first potentials,
with the source operator coefficients and genuine positive-series membership. -/
theorem pureFluxMainQ3_distinct_h10_row_bound (n : ℤ) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (z : whiteBasisIndex → H10Function (openCubeSet (originCube 2 n))) :
    let Q := originCube 2 n
    let F := pureFluxMainQ3DistinctRow n b σ L s z
    (∀ i : Fin 2, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q
      (cubeIncrement Q (k+1) (fun x => F x i)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q 0 F) ≤
      |σ⁻¹| * mainQ3RowConstant (cubeScaleFactor Q) b L.1*
        Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q 0 (z l).toH1Function.grad) := by
  intro Q F
  let A := pureFluxQ3DerivativeRow whiteBasis s b L Q
  let Z := pureFluxH10FiniteFamily s Q z
  let Y := fun x => A.toFun x (Z x)
  have hYmem : MemLp Y 2 (normalizedCubeMeasure Q) :=
    A.product_memLp (pureFluxH10FiniteFamily_memLp s Q z)
  obtain ⟨hYP, hYbound⟩ := pureFluxQ3_distinct_h10_product whiteBasis s b L Q z
  have hcoordP (i : Fin 2) : Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q
      (cubeIncrement Q (k+1) (fun x => (Y x).ofLp i))) :=
    main_hilbert_coordinate_summable Q hYmem hYP i
  have hrow : F = fun x => planarQuarterTurn (fun i => (-σ⁻¹)*(Y x).ofLp i) :=
    pureFluxMainQ3DistinctRow_eq n b σ L s z
  have hFP (i : Fin 2) : Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q
      (cubeIncrement Q (k+1) (fun x => F x i))) := by
    rw [hrow]
    fin_cases i
    · simpa [planarQuarterTurn] using
        pureFluxDistinct_summable_smul Q (fun x => (Y x).ofLp 1) (σ⁻¹) (hcoordP 1)
    · simpa [planarQuarterTurn] using
        pureFluxDistinct_summable_smul Q (fun x => (Y x).ofLp 0) (-σ⁻¹) (hcoordP 0)
  have henergy : vectorPositiveHaarEnergy Q F =
      (σ⁻¹)^2*hilbertPrimalEnergy Q (Real.sqrt 3) Y := by
    rw [hrow, main_vectorPositiveHaarEnergy_quarterTurn]
    unfold vectorPositiveHaarEnergy
    simp_rw [sensitivity_primalEnergy_smul]
    rw [← Finset.mul_sum, ← main_hilbertPrimalEnergy_euclidean Q hYmem hYP]
    simp only [neg_sq]
  have hroot : Real.sqrt (lemmaVTiledPositiveEnergy Q 0 F) =
      |σ⁻¹| * hilbertPositiveHaarNorm Q (Real.sqrt 3) Y := by
    simp only [lemmaVTiledPositiveEnergy, descendantsAverage, descendantsAtDepth_zero,
      Finset.card_singleton, Nat.cast_one, inv_one, Finset.sum_singleton, one_mul]
    rw [henergy, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    rfl
  have hweak : (∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad) =
      ∑ l ∈ s, lemmaVTiledWeakEnergy Q 0 (z l).toH1Function.grad := by
    simp only [lemmaVTiledWeakEnergy, descendantsAverage, descendantsAtDepth_zero,
      Finset.card_singleton, Nat.cast_one, inv_one, Finset.sum_singleton, one_mul]
    exact Finset.sum_coe_sort s (fun l => vectorWeakHaarEnergy Q (z l).toH1Function.grad)
  have hcoef : cubeScaleFactor Q*(36/25)*Real.sqrt ((78/5)*b^2/L.1^2) +
      (cubeScaleFactor Q)^2*(57/200)*Real.sqrt ((23244/25)*b^2/L.1^4) ≤
      mainQ3RowConstant (cubeScaleFactor Q) b L.1 := by
    unfold mainQ3RowConstant
    linarith only [Real.sqrt_nonneg (b^2)]
  refine ⟨hFP, ?_⟩
  rw [hroot]
  calc
    _ ≤ |σ⁻¹| * (cubeScaleFactor Q*(36/25)*Real.sqrt ((78/5)*b^2/L.1^2) +
        (cubeScaleFactor Q)^2*(57/200)*Real.sqrt ((23244/25)*b^2/L.1^4))*
          Real.sqrt (∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hYbound (abs_nonneg (σ⁻¹))
    _ ≤ |σ⁻¹| * mainQ3RowConstant (cubeScaleFactor Q) b L.1*
          Real.sqrt (∑ l : s, vectorWeakHaarEnergy Q (z l).toH1Function.grad) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef (abs_nonneg _)) (Real.sqrt_nonneg _)
    _ = _ := by rw [hweak]

end
end ASDExplicitGamma.Inverse
