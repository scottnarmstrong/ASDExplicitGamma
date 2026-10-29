module

public import ASDExplicitGamma.Main.HilbertFiniteCoordinates
public import ASDExplicitGamma.Gaussian.Q3ModelH3Realization
public import ASDExplicitGamma.Response.FrameAlgebra
public import ASDExplicitGamma.Scalar.FlatSourceProjectedModeTrace
public import ASDExplicitGamma.Scalar.Lambda8Q3ParentOscillation
public import ASDExplicitGamma.Scalar.Lambda8HessianPoincare
public import ASDExplicitGamma.Triadic.HilbertSkewMultipliers
public import ASDExplicitGamma.Numerics.Joint.LocalCaps
public import ASDExplicitGamma.Main.LoadsAndSlopes

/-! The stationary q3 flat fields and their actual Hilbert-valued H¹ carriers. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic
open ASDExplicitGamma.Numerics.Joint
open scoped BigOperators ENNReal

noncomputable section

private theorem mainH1SumToFun {ι : Type*} {U : Set (Vec 2)}
    (s : Finset ι) (F : ι → H1Function U) :
    (∑ i ∈ s, F i).toFun = fun x => ∑ i ∈ s, (F i).toFun x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [H1Function.add_toFun, Finset.sum_insert ha, ih]

private theorem mainH1SumGrad {ι : Type*} {U : Set (Vec 2)}
    (s : Finset ι) (F : ι → H1Function U) :
    (∑ i ∈ s, F i).grad = fun x => ∑ i ∈ s, (F i).grad x := by
  classical
  induction s using Finset.induction with
  | empty => funext x; simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [H1Function.add_grad, Finset.sum_insert ha, ih]

/-- The trace of the normalized q3 shell gradient covariance. -/
def mainFlatSigmaSq (β : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  2 * (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ))

/-- A finite coordinate family of scalar H¹ functions as one genuine Hilbert H¹ field. -/
def mainHilbertH1OfCoordinates {ι : Type*} [Fintype ι] (Q : TriadicCube 2)
    (F : ι → H1Function (openCubeSet Q)) :
    HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ ι) where
  toFun x := WithLp.toLp 2 (fun i => F i x)
  grad x j := WithLp.toLp 2 (fun i => (F i).grad x j)
  memL2 := (memLp_piLp_iff).2 (fun i => (F i).memL2)
  gradMemL2 j := (memLp_piLp_iff).2 (fun i => (F i).grad_memL2 j)
  hasWeakGradient e := by
    let w : H1Function (openCubeSet Q) := ∑ i, (e.ofLp i) • F i
    have hvalW : w.toFun = fun x => ∑ i, e.ofLp i * F i x := by
      dsimp [w]
      rw [mainH1SumToFun]
      simp [H1Function.smul_toFun]
    have hgradW : w.grad = fun x j => ∑ i, e.ofLp i * (F i).grad x j := by
      dsimp [w]
      rw [mainH1SumGrad]
      funext x j
      simp [H1Function.smul_grad, smul_eq_mul, Pi.smul_apply]
    have hval : (fun x => inner ℝ e (WithLp.toLp 2 (fun i => F i x))) = w.toFun := by
      funext x
      rw [PiLp.inner_apply]
      simpa [mul_comm] using (congrFun hvalW x).symm
    have hgrad (j : Fin 2) :
        (fun x => inner ℝ e (WithLp.toLp 2 (fun i => (F i).grad x j))) =
          fun x => w.grad x j := by
      funext x
      rw [PiLp.inner_apply]
      simpa [mul_comm] using (congrFun (congrFun hgradW x) j).symm
    rw [hval]
    convert w.hasWeakGradient using 1
    funext x j
    exact congrFun (hgrad j) x

/-- The two q3 source loads for a fixed white-noise basis mode. -/
def mainFlatRotatedBasis (i : Fin 2) : Vec 2 :=
  matVecMul responsePlanarJ (basisVec i)

/-- The minus flat field is the local Dirichlet projection of `ψ J eᵢ`. Its
two load directions and two vector components are retained as coordinates. -/
def mainFlatMinusCoordinate (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex)
    (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  (lambda8HessianGradientH1 Q
    (lambda8Q3GaussianModeParentPotential Q β L (mainFlatRotatedBasis a.1) n)
    (lambda8Q3GaussianModeParentHessian Q β L (mainFlatRotatedBasis a.1) n)).scalar
      (HilbertVec.ofVec (basisVec a.2))

/-- The smooth source part of the plus field. -/
def mainFlatPlusSourceCoordinate (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex)
    (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  lambda8Q3GaussianModeLoadH1 Q β L (mainFlatRotatedBasis a.1) n a.2

/-- The rotated Dirichlet correction in the plus field. -/
def mainFlatPlusCorrectionCoordinate (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex)
    (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  (((lambda8HessianGradientH1 Q
      (lambda8Q3GaussianModeParentPotential Q β L (basisVec a.1) n)
      (lambda8Q3GaussianModeParentHessian Q β L (basisVec a.1) n)).map
        hilbertPlanarJ.toContinuousLinearMap).scalar (HilbertVec.ofVec (basisVec a.2)))

/-- The actual plus flat field `ψ J eᵢ − J P_D(ψ eᵢ)`, component by
component, on the same local square. -/
def mainFlatPlusCoordinate (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex)
    (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  mainFlatPlusSourceCoordinate Q β L n a - mainFlatPlusCorrectionCoordinate Q β L n a

/-- The minus flat field as one Hilbert-valued H¹ function with four real
coordinates (load direction, vector component). -/
def mainFlatMinusH1 (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ (Fin 2 × Fin 2)) :=
  mainHilbertH1OfCoordinates Q (mainFlatMinusCoordinate Q β L n)

/-- The plus flat field as one Hilbert-valued H¹ function with four real
coordinates (load direction, vector component). -/
def mainFlatPlusH1 (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ (Fin 2 × Fin 2)) :=
  mainHilbertH1OfCoordinates Q (mainFlatPlusCoordinate Q β L n)

/-- The smooth-source and Dirichlet-correction parts, jointly over both load
directions, as genuine Hilbert-valued H¹ functions. -/
def mainFlatPlusSourceH1 (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ (Fin 2 × Fin 2)) :=
  mainHilbertH1OfCoordinates Q (mainFlatPlusSourceCoordinate Q β L n)

def mainFlatPlusCorrectionH1 (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ (Fin 2 × Fin 2)) :=
  mainHilbertH1OfCoordinates Q (mainFlatPlusCorrectionCoordinate Q β L n)

/-- The full spatial gradient, flattened over its derivative direction and
the finite Hilbert coordinates. -/
def mainHilbertGradientField {κ : Type*} [Fintype κ] (Q : TriadicCube 2)
    (u : HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ κ)) :
    Vec 2 → EuclideanSpace ℝ (Fin 2 × κ) :=
  fun x => WithLp.toLp 2 (fun a => (u.grad x a.1).ofLp a.2)

/-- L² membership of the flattened spatial gradient follows from each actual
weak-gradient coordinate. -/
theorem mainHilbertGradientField_memLp {κ : Type*} [Fintype κ]
    (Q : TriadicCube 2)
    (u : HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ κ)) :
    MemLp (mainHilbertGradientField Q u) 2 (normalizedCubeMeasure Q) := by
  apply (memLp_piLp_iff).2
  intro a
  change MemLp (fun x => (u.grad x a.1).ofLp a.2) 2 (normalizedCubeMeasure Q)
  let P : EuclideanSpace ℝ κ →L[ℝ] ℝ := PiLp.proj 2 (fun _ : κ => ℝ) a.2
  have h := P.comp_memLp' (u.gradMemL2_normalized Q a.1)
  convert h using 1
  funext x
  rfl

/-- The flattened gradient has exactly the Hilbert H¹ gradient energy. -/
theorem mainHilbertGradientField_energy {κ : Type*} [Fintype κ]
    (Q : TriadicCube 2)
    (u : HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ κ)) :
    hilbertEnergy Q (mainHilbertGradientField Q u) = hilbertGradientEnergy Q u.grad := by
  rw [main_hilbertEnergy_euclidean Q (mainHilbertGradientField_memLp Q u)]
  unfold mainHilbertGradientField
  rw [Fintype.sum_prod_type]
  unfold hilbertGradientEnergy
  apply Finset.sum_congr rfl
  intro j hj
  exact (main_hilbertEnergy_euclidean Q (u.gradMemL2_normalized Q j)).symm

private theorem mainHilbertGradientEnergy_coordinates (Q : TriadicCube 2)
    {ι : Type*} [Fintype ι] (F : ι → H1Function (openCubeSet Q)) :
    hilbertGradientEnergy Q (mainHilbertH1OfCoordinates Q F).grad =
      ∑ j : Fin 2, ∑ a : ι, energy Q (fun x => (F a).grad x j) := by
  unfold hilbertGradientEnergy
  apply Finset.sum_congr rfl
  intro j hj
  rw [main_hilbertEnergy_euclidean Q
    ((mainHilbertH1OfCoordinates Q F).gradMemL2_normalized Q j)]
  apply Finset.sum_congr rfl
  intro a ha
  rfl

private theorem mainHilbertGradientEnergy_nonneg (Q : TriadicCube 2)
    {κ : Type*} [Fintype κ] (G : Vec 2 → Fin 2 → EuclideanSpace ℝ κ) :
    0 ≤ hilbertGradientEnergy Q G :=
  Finset.sum_nonneg fun j _ => hilbertEnergy_nonneg Q (fun x => G x j)

private theorem mainHessianCoordinateEnergy_eq_frobenius (Q : TriadicCube 2)
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u) :
    (∑ i : Fin 2, ∑ j : Fin 2, energy Q (fun x => H.hess i j x)) =
      H.frobeniusNormalizedL2 Q ^ 2 := by
  have hcoord (i j : Fin 2) :
      energy Q (fun x => H.hess i j x) =
        (cubeVolume Q)⁻¹ * ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
    rw [energy_eq_integral_sq, H.integral_hess_sq_normalizedCubeMeasure Q i j]
  calc
    _ = ∑ i : Fin 2, ∑ j : Fin 2,
        (cubeVolume Q)⁻¹ * ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
      simp_rw [hcoord]
    _ = (cubeVolume Q)⁻¹ *
        ∑ i : Fin 2, ∑ j : Fin 2, ‖H.hessCoordToScalarL2 i j‖ ^ 2 := by
      simp_rw [Finset.mul_sum]
    _ = H.frobeniusNormalizedL2 Q ^ 2 :=
      (H.frobeniusNormalizedL2_sq Q).symm

private theorem main_sqrt_tsum_sq_le_of_pointwise {ι : Type*} [Countable ι]
    [DecidableEq ι] {a b c : ι → ℝ}
    (ha : Summable (fun i => a i ^ 2))
    (hb : Summable (fun i => b i ^ 2))
    (hc : ∀ i, 0 ≤ c i) (hbound : ∀ i, c i ≤ a i + b i) :
    Summable (fun i => c i ^ 2) ∧
      Real.sqrt (∑' i, c i ^ 2) ≤
        Real.sqrt (∑' i, a i ^ 2) + Real.sqrt (∑' i, b i ^ 2) := by
  classical
  have hadd : Summable (fun i => (a i + b i) ^ 2) :=
    ((ha.mul_left 2).add (hb.mul_left 2)).of_nonneg_of_le
      (fun i => sq_nonneg (a i + b i)) (fun i => by
        nlinarith only [sq_nonneg (a i - b i)])
  have hsq (i : ι) : c i ^ 2 ≤ (a i + b i) ^ 2 :=
    pow_le_pow_left₀ (hc i) (hbound i) 2
  have hcs : Summable (fun i => c i ^ 2) :=
    hadd.of_nonneg_of_le (fun i => sq_nonneg (c i)) hsq
  have hmem (f : ι → ℝ) (hf : Summable (fun i => f i ^ 2)) :
      Memℓp f (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa [Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using hf
  let A : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞) := ⟨a, hmem a ha⟩
  let B : lp (fun _ : ι => ℝ) (2 : ℝ≥0∞) := ⟨b, hmem b hb⟩
  have hA : ‖A‖ ^ 2 = ∑' i, a i ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) A
    simpa [A, Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
  have hB : ‖B‖ ^ 2 = ∑' i, b i ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) B
    simpa [B, Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
  have hAB : ‖A + B‖ ^ 2 = ∑' i, (a i + b i) ^ 2 := by
    have h := lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (A + B)
    have h' : ‖A + B‖ ^ 2 = ∑' i, ‖(A + B) i‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
    calc
      ‖A + B‖ ^ 2 = ∑' i, ‖(A + B) i‖ ^ 2 := h'
      _ = ∑' i, (a i + b i) ^ 2 := by
        apply tsum_congr
        intro i
        rw [lp.coeFn_add]
        change ‖a i + b i‖ ^ 2 = (a i + b i) ^ 2
        simp [Real.norm_eq_abs, sq_abs]
  have hnorm := norm_add_le A B
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  have hBn : 0 ≤ ‖B‖ := norm_nonneg _
  have hABn : 0 ≤ ‖A + B‖ := norm_nonneg _
  refine ⟨hcs, ?_⟩
  calc
    Real.sqrt (∑' i, c i ^ 2) ≤ Real.sqrt (∑' i, (a i + b i) ^ 2) :=
      Real.sqrt_le_sqrt (hcs.tsum_le_tsum hsq hadd)
    _ = ‖A + B‖ := by
      rw [← hAB, Real.sqrt_sq_eq_abs, abs_of_nonneg hABn]
    _ ≤ ‖A‖ + ‖B‖ := hnorm
    _ = Real.sqrt (∑' i, a i ^ 2) + Real.sqrt (∑' i, b i ^ 2) := by
      rw [← hA, ← hB, Real.sqrt_sq_eq_abs, abs_of_nonneg hAn,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hBn]

private theorem mainQ3HessianFrobeniusEnergy_summable (Q : TriadicCube 2)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2) :
    Summable (fun n : Gaussian.whiteBasisIndex =>
      (lambda8Q3GaussianModeParentHessian Q β L v n).frobeniusNormalizedL2 Q ^ 2) := by
  have htrace := lambda8Q3GaussianModeDerivative_energy_tsum Q β L v
  have hmode (n : Gaussian.whiteBasisIndex) :
      (lambda8Q3GaussianModeParentHessian Q β L v n).frobeniusNormalizedL2 Q ^ 2 =
        energy Q (lambda8Q3GaussianModeDerivative β L v n) := by
    let u := lambda8Q3GaussianModeParentPotential Q β L v n
    let H := lambda8Q3GaussianModeParentHessian Q β L v n
    have hdiv := (lambda8Q3GaussianModeParentPotential_spec Q β L v n).2
    have hmemLap : MemLp (dirichletWeakLaplacian H) 2 (normalizedCubeMeasure Q) :=
      memLp_dirichlet_weak_laplacian H
    have hmemDeriv : MemLp (lambda8Q3GaussianModeDerivative β L v n) 2
        (normalizedCubeMeasure Q) := (memLp_congr_ae hdiv).mp hmemLap
    have hnorm : cubeLpNorm Q 2 (dirichletWeakLaplacian H) =
        cubeLpNorm Q 2 (lambda8Q3GaussianModeDerivative β L v n) := by
      unfold cubeLpNorm
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae hdiv)
    calc
      _ = cubeLpNorm Q 2 (dirichletWeakLaplacian H) ^ 2 := by
        rw [dirichlet_square_hessian_identity Q u H]
      _ = cubeLpNorm Q 2 (lambda8Q3GaussianModeDerivative β L v n) ^ 2 := by
        rw [hnorm]
      _ = energy Q (lambda8Q3GaussianModeDerivative β L v n) :=
        (energy_eq_cubeLpNorm_sq Q hmemDeriv).symm
  exact htrace.1.congr (fun n => (hmode n).symm)

/-- The three plus-field pieces have the source-identical gradient relation. -/
theorem mainFlatPlusH1_grad (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex)
    (x : Vec 2) (j : Fin 2) :
    (mainFlatPlusH1 Q β L n).grad x j =
      (mainFlatPlusSourceH1 Q β L n).grad x j -
        (mainFlatPlusCorrectionH1 Q β L n).grad x j := by
  ext a
  rcases a with ⟨i, k⟩
  fin_cases i <;> fin_cases k <;>
    simp [mainFlatPlusH1, mainFlatPlusSourceH1,
      mainFlatPlusCorrectionH1, mainHilbertH1OfCoordinates,
      mainFlatPlusCoordinate, mainFlatPlusSourceCoordinate,
      mainFlatPlusCorrectionCoordinate, mainFlatRotatedBasis,
      H1Function.sub_grad]

/-- The flattened plus gradient is the source gradient minus the local
Dirichlet correction gradient. -/
theorem mainFlatPlusGradientField_eq (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    mainHilbertGradientField Q (mainFlatPlusH1 Q β L n) =
      fun x => mainHilbertGradientField Q (mainFlatPlusSourceH1 Q β L n) x -
        mainHilbertGradientField Q (mainFlatPlusCorrectionH1 Q β L n) x := by
  funext x
  ext a
  rcases a with ⟨j, k⟩
  simp only [mainHilbertGradientField, WithLp.ofLp_toLp]
  rw [mainFlatPlusH1_grad]
  simp

/-- Minkowski gives the plus-field H¹ bound mode by mode. -/
theorem mainFlatPlusModeGradient_sqrt_le (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    Real.sqrt (hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad) ≤
      Real.sqrt (hilbertGradientEnergy Q (mainFlatPlusSourceH1 Q β L n).grad) +
        Real.sqrt (hilbertGradientEnergy Q (mainFlatPlusCorrectionH1 Q β L n).grad) := by
  let F := mainHilbertGradientField Q (mainFlatPlusSourceH1 Q β L n)
  let G := mainHilbertGradientField Q (mainFlatPlusCorrectionH1 Q β L n)
  rw [← mainHilbertGradientField_energy Q (mainFlatPlusH1 Q β L n),
    ← mainHilbertGradientField_energy Q (mainFlatPlusSourceH1 Q β L n),
    ← mainHilbertGradientField_energy Q (mainFlatPlusCorrectionH1 Q β L n)]
  rw [mainFlatPlusGradientField_eq]
  have htri := hilbertL2Norm_add_le Q
    (mainHilbertGradientField_memLp Q (mainFlatPlusSourceH1 Q β L n))
    ((mainHilbertGradientField_memLp Q (mainFlatPlusCorrectionH1 Q β L n)).neg)
  simp only [hilbertL2Norm] at htri
  have hneg : hilbertEnergy Q (-G) = hilbertEnergy Q G := by
    simp [hilbertEnergy]
  rw [hneg] at htri
  simpa [F, G, sub_eq_add_neg] using htri

/-- The smooth load's weak gradient is its classical coordinate derivative. -/
theorem mainFlatLoadH1_grad (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (v : Vec 2)
    (n : Gaussian.whiteBasisIndex) (i j : Fin 2) (x : Vec 2) :
    (lambda8Q3GaussianModeLoadH1 Q β L v n i).grad x j =
      v i * (fderiv ℝ (Gaussian.q3Convolution β L Gaussian.h3Zero
        (Gaussian.whiteBasis n)) x) (basisVec j) := by
  let ψ := Gaussian.q3Convolution β L Gaussian.h3Zero (Gaussian.whiteBasis n)
  have hψcont : ContDiff ℝ 1 ψ := by
    exact Gaussian.q3Convolution_contDiff_one β L Gaussian.h3Zero
      (by norm_num [Gaussian.h3Zero, Gaussian.H3Index])
      (Gaussian.whiteBasis n)
  have hψ : DifferentiableAt ℝ ψ x :=
    (hψcont.differentiable (by norm_num)).differentiableAt
  change (fderiv ℝ (fun y => ψ y * v i) x) (basisVec j) = _
  calc
    (fderiv ℝ (fun y => ψ y * v i) x) (basisVec j) =
        ((v i) • fderiv ℝ ψ x) (basisVec j) := by rw [fderiv_mul_const hψ]
    _ = v i * (fderiv ℝ ψ x) (basisVec j) := by simp
    _ = v i * (fderiv ℝ (Gaussian.q3Convolution β L Gaussian.h3Zero
          (Gaussian.whiteBasis n)) x) (basisVec j) := by rfl

private theorem mainEnergy_scalar_mul (Q : TriadicCube 2) (c : ℝ)
    (f : Vec 2 → ℝ) :
    energy Q (fun x => c * f x) = c ^ 2 * energy Q f := by
  rw [energy_eq_integral_sq Q, energy_eq_integral_sq Q]
  calc
    (∫ x, (c * f x) ^ 2 ∂normalizedCubeMeasure Q) =
        ∫ x, c ^ 2 * f x ^ 2 ∂normalizedCubeMeasure Q := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = c ^ 2 * ∫ x, f x ^ 2 ∂normalizedCubeMeasure Q := integral_const_mul _ _

/-- The smooth plus-field source has twice the minus-field trace energy. -/
theorem mainFlatPlusSourceModeGradientEnergy (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    hilbertGradientEnergy Q (mainFlatPlusSourceH1 Q β L n).grad =
      2 * ∑ j : Fin 2,
        energy Q (lambda8Q3GaussianModeDerivative β L (basisVec j) n) := by
  change hilbertGradientEnergy Q
      (mainHilbertH1OfCoordinates Q (mainFlatPlusSourceCoordinate Q β L n)).grad = _
  rw [mainHilbertGradientEnergy_coordinates]
  simp_rw [mainFlatPlusSourceCoordinate, mainFlatLoadH1_grad]
  have hcoeff (j : Fin 2) :
      (∑ i : Fin 2, ∑ k : Fin 2,
        (mainFlatRotatedBasis i k) ^ 2) = 2 := by
    fin_cases j <;> norm_num [mainFlatRotatedBasis, responsePlanarJ,
      matVecMul, basisVec, Fin.sum_univ_two]
  calc
    _ = ∑ j : Fin 2,
        (∑ i : Fin 2, ∑ k : Fin 2,
          (mainFlatRotatedBasis i k) ^ 2) *
          energy Q (lambda8Q3GaussianModeDerivative β L (basisVec j) n) := by
      simp_rw [Fintype.sum_prod_type, mainEnergy_scalar_mul]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro k hk
      rfl
    _ = ∑ j : Fin 2,
        2 * energy Q (lambda8Q3GaussianModeDerivative β L (basisVec j) n) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcoeff j]
    _ = 2 * ∑ j : Fin 2,
        energy Q (lambda8Q3GaussianModeDerivative β L (basisVec j) n) := by
      rw [← Finset.mul_sum]

/-- The source part's full white-noise gradient trace is twice σ². -/
theorem mainFlatPlusSourceGradientEnergy_tsum (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Summable (fun n : Gaussian.whiteBasisIndex =>
      hilbertGradientEnergy Q (mainFlatPlusSourceH1 Q β L n).grad) ∧
    (∑' n : Gaussian.whiteBasisIndex,
      hilbertGradientEnergy Q (mainFlatPlusSourceH1 Q β L n).grad) =
        2 * mainFlatSigmaSq β L := by
  have htrace (j : Fin 2) :=
    lambda8Q3GaussianModeDerivative_energy_tsum Q β L (basisVec j)
  have hsraw : Summable (fun n : Gaussian.whiteBasisIndex =>
      2 * ∑ j : Fin 2,
        energy Q (lambda8Q3GaussianModeDerivative β L (basisVec j) n)) := by
    exact (summable_sum (s := Finset.univ) (fun j hj => (htrace j).1)).mul_left 2
  have hs : Summable (fun n : Gaussian.whiteBasisIndex =>
      hilbertGradientEnergy Q (mainFlatPlusSourceH1 Q β L n).grad) :=
    hsraw.congr (fun n => (mainFlatPlusSourceModeGradientEnergy Q β L n).symm)
  refine ⟨hs, ?_⟩
  calc
    (∑' n : Gaussian.whiteBasisIndex,
        hilbertGradientEnergy Q (mainFlatPlusSourceH1 Q β L n).grad) =
      ∑' n : Gaussian.whiteBasisIndex, 2 * ∑ j : Fin 2,
        energy Q (lambda8Q3GaussianModeDerivative β L (basisVec j) n) := by
      apply tsum_congr
      intro n
      exact mainFlatPlusSourceModeGradientEnergy Q β L n
    _ = 2 * ∑ j : Fin 2, ∑' n : Gaussian.whiteBasisIndex,
        energy Q (lambda8Q3GaussianModeDerivative β L (basisVec j) n) := by
      rw [tsum_mul_left, Summable.tsum_finsetSum (fun j hj => (htrace j).1)]
    _ = 2 * mainFlatSigmaSq β L := by
      have hunit (j : Fin 2) :
          (basisVec j) 0 ^ 2 + (basisVec j) 1 ^ 2 = 1 := by
        fin_cases j <;> simp [basisVec]
      rw [show (∑ j : Fin 2,
          ∑' n : Gaussian.whiteBasisIndex,
            energy Q (lambda8Q3GaussianModeDerivative β L (basisVec j) n)) =
          ∑ j : Fin 2,
            β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) *
              ((basisVec j) 0 ^ 2 + (basisVec j) 1 ^ 2) by
        apply Finset.sum_congr rfl
        intro j hj
        exact (htrace j).2]
      simp_rw [hunit]
      simp [mainFlatSigmaSq]

/-- Coordinate gradients of the minus field are the actual weak Hessian entries. -/
theorem mainFlatMinusCoordinate_grad (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex)
    (a : Fin 2 × Fin 2) (x : Vec 2) (j : Fin 2) :
    (mainFlatMinusCoordinate Q β L n a).grad x j =
      (lambda8Q3GaussianModeParentHessian Q β L (mainFlatRotatedBasis a.1) n).hess
        a.2 j x := by
  simp [mainFlatMinusCoordinate, lambda8HessianGradientH1,
    HilbertH1Function.scalar, HilbertVec.inner_def, vecDot]

/-- The minus flat field's mode gradient energy is the sum of the two
Dirichlet Hessian Frobenius energies. -/
theorem mainFlatMinusModeGradientEnergy (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    hilbertGradientEnergy Q (mainFlatMinusH1 Q β L n).grad =
      ∑ i : Fin 2,
        (lambda8Q3GaussianModeParentHessian Q β L
          (mainFlatRotatedBasis i) n).frobeniusNormalizedL2 Q ^ 2 := by
  change hilbertGradientEnergy Q
      (mainHilbertH1OfCoordinates Q (mainFlatMinusCoordinate Q β L n)).grad = _
  rw [mainHilbertGradientEnergy_coordinates]
  have hperm :
      (∑ j : Fin 2, ∑ a : Fin 2 × Fin 2,
        energy Q (fun x =>
          (mainFlatMinusCoordinate Q β L n a).grad x j)) =
        ∑ i : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
          energy Q (fun x =>
            (mainFlatMinusCoordinate Q β L n (i, k)).grad x j) := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [hperm]
  simp_rw [mainFlatMinusCoordinate_grad]
  apply Finset.sum_congr rfl
  intro i hi
  exact mainHessianCoordinateEnergy_eq_frobenius Q
    (lambda8Q3GaussianModeParentHessian Q β L (mainFlatRotatedBasis i) n)

/-- The exact white-noise trace of the minus flat-field H¹ seminorm is σ². -/
theorem mainFlatMinusGradientEnergy_tsum (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Summable (fun n : Gaussian.whiteBasisIndex =>
      hilbertGradientEnergy Q (mainFlatMinusH1 Q β L n).grad) ∧
    (∑' n : Gaussian.whiteBasisIndex,
      hilbertGradientEnergy Q (mainFlatMinusH1 Q β L n).grad) =
        mainFlatSigmaSq β L := by
  have hs_i (i : Fin 2) :=
    mainQ3HessianFrobeniusEnergy_summable Q β L (mainFlatRotatedBasis i)
  have hsraw : Summable (fun n : Gaussian.whiteBasisIndex =>
      ∑ i : Fin 2,
        (lambda8Q3GaussianModeParentHessian Q β L
          (mainFlatRotatedBasis i) n).frobeniusNormalizedL2 Q ^ 2) := by
    exact summable_sum (s := Finset.univ) (fun i hi => hs_i i)
  have hs : Summable (fun n : Gaussian.whiteBasisIndex =>
      hilbertGradientEnergy Q (mainFlatMinusH1 Q β L n).grad) :=
    hsraw.congr (fun n => (mainFlatMinusModeGradientEnergy Q β L n).symm)
  refine ⟨hs, ?_⟩
  calc
    (∑' n : Gaussian.whiteBasisIndex,
        hilbertGradientEnergy Q (mainFlatMinusH1 Q β L n).grad) =
      ∑' n : Gaussian.whiteBasisIndex, ∑ i : Fin 2,
        (lambda8Q3GaussianModeParentHessian Q β L
          (mainFlatRotatedBasis i) n).frobeniusNormalizedL2 Q ^ 2 := by
      apply tsum_congr
      intro n
      exact mainFlatMinusModeGradientEnergy Q β L n
    _ = ∑ i : Fin 2, ∑' n : Gaussian.whiteBasisIndex,
        (lambda8Q3GaussianModeParentHessian Q β L
          (mainFlatRotatedBasis i) n).frobeniusNormalizedL2 Q ^ 2 := by
      rw [Summable.tsum_finsetSum (fun i hi => hs_i i)]
    _ = ∑ i : Fin 2,
        (β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) *
          ((mainFlatRotatedBasis i) 0 ^ 2 + (mainFlatRotatedBasis i) 1 ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact lambda8Q3GaussianModeParent_hessian_energy_trace Q β L
        (mainFlatRotatedBasis i)
    _ = mainFlatSigmaSq β L := by
      simp [mainFlatSigmaSq, mainFlatRotatedBasis,
        responsePlanarJ, matVecMul, basisVec, Fin.sum_univ_two]
      ring

/-- Coordinate gradients of the plus field retain the literal source minus
the rotated local Hessian correction. -/
theorem mainFlatPlusCoordinate_grad (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex)
    (a : Fin 2 × Fin 2) (x : Vec 2) (j : Fin 2) :
    (mainFlatPlusCoordinate Q β L n a).grad x j =
      (mainFlatRotatedBasis a.1 a.2) *
        (fderiv ℝ (Gaussian.q3Convolution β L Gaussian.h3Zero
          (Gaussian.whiteBasis n)) x) (basisVec j) -
        (matVecMul responsePlanarJ (fun q =>
          (lambda8Q3GaussianModeParentHessian Q β L (basisVec a.1) n).hess q j x)) a.2 := by
  rcases a with ⟨i, k⟩
  fin_cases i <;> fin_cases k <;>
    simp [mainFlatPlusCoordinate, mainFlatPlusSourceCoordinate,
      mainFlatPlusCorrectionCoordinate, mainFlatRotatedBasis,
      H1Function.sub_grad, mainFlatLoadH1_grad,
      lambda8HessianGradientH1, HilbertH1Function.map,
      HilbertH1Function.scalar, HilbertVec.inner_def,
      vecDot, Fin.sum_univ_two, hilbertPlanarJ,
      responsePlanarJ, matVecMul]

/-- The correction field's coordinate gradients are the quarter-turn of the
local Dirichlet Hessian columns. -/
theorem mainFlatPlusCorrectionCoordinate_grad (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex)
    (a : Fin 2 × Fin 2) (x : Vec 2) (j : Fin 2) :
    (mainFlatPlusCorrectionCoordinate Q β L n a).grad x j =
      (matVecMul responsePlanarJ (fun q =>
        (lambda8Q3GaussianModeParentHessian Q β L (basisVec a.1) n).hess
          q j x)) a.2 := by
  have hp := mainFlatPlusCoordinate_grad Q β L n a x j
  have hs := mainFlatLoadH1_grad Q β L (mainFlatRotatedBasis a.1) n a.2 j x
  simp only [mainFlatPlusCoordinate, H1Function.sub_grad, Pi.sub_apply] at hp
  rw [mainFlatPlusSourceCoordinate] at hp
  rw [hs] at hp
  linarith

/-- The rotated Dirichlet correction has the same total mode trace as the
minus field. -/
theorem mainFlatPlusCorrectionModeGradientEnergy (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (n : Gaussian.whiteBasisIndex) :
    hilbertGradientEnergy Q (mainFlatPlusCorrectionH1 Q β L n).grad =
      ∑ i : Fin 2,
        (lambda8Q3GaussianModeParentHessian Q β L (basisVec i) n).frobeniusNormalizedL2 Q ^ 2 := by
  change hilbertGradientEnergy Q
      (mainHilbertH1OfCoordinates Q (mainFlatPlusCorrectionCoordinate Q β L n)).grad = _
  rw [mainHilbertGradientEnergy_coordinates]
  have hperm :
      (∑ j : Fin 2, ∑ a : Fin 2 × Fin 2,
        energy Q (fun x =>
          (mainFlatPlusCorrectionCoordinate Q β L n a).grad x j)) =
        ∑ i : Fin 2, ∑ k : Fin 2, ∑ j : Fin 2,
          energy Q (fun x =>
            (mainFlatPlusCorrectionCoordinate Q β L n (i, k)).grad x j) := by
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [hperm]
  simp_rw [mainFlatPlusCorrectionCoordinate_grad]
  apply Finset.sum_congr rfl
  intro i hi
  have hrotate (j : Fin 2) :
      (∑ k : Fin 2, energy Q (fun x =>
        (matVecMul responsePlanarJ (fun q =>
          (lambda8Q3GaussianModeParentHessian Q β L (basisVec i) n).hess
            q j x)) k)) =
        ∑ q : Fin 2, energy Q (fun x =>
          (lambda8Q3GaussianModeParentHessian Q β L (basisVec i) n).hess q j x) := by
    fin_cases j
    · simp [responsePlanarJ, matVecMul, Fin.sum_univ_two,
        energy_eq_integral_sq]
      ring
    · simp [responsePlanarJ, matVecMul, Fin.sum_univ_two,
        energy_eq_integral_sq]
      ring
  rw [Finset.sum_comm]
  simp_rw [hrotate]
  rw [Finset.sum_comm]
  exact mainHessianCoordinateEnergy_eq_frobenius Q
    (lambda8Q3GaussianModeParentHessian Q β L (basisVec i) n)

/-- The exact white-noise trace of the plus correction gradient energy is σ². -/
theorem mainFlatPlusCorrectionGradientEnergy_tsum (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Summable (fun n : Gaussian.whiteBasisIndex =>
      hilbertGradientEnergy Q (mainFlatPlusCorrectionH1 Q β L n).grad) ∧
    (∑' n : Gaussian.whiteBasisIndex,
      hilbertGradientEnergy Q (mainFlatPlusCorrectionH1 Q β L n).grad) =
        mainFlatSigmaSq β L := by
  have hs_i (i : Fin 2) :=
    mainQ3HessianFrobeniusEnergy_summable Q β L (basisVec i)
  have hsraw : Summable (fun n : Gaussian.whiteBasisIndex =>
      ∑ i : Fin 2,
        (lambda8Q3GaussianModeParentHessian Q β L (basisVec i) n).frobeniusNormalizedL2 Q ^ 2) := by
    exact summable_sum (s := Finset.univ) (fun i hi => hs_i i)
  have hs : Summable (fun n : Gaussian.whiteBasisIndex =>
      hilbertGradientEnergy Q (mainFlatPlusCorrectionH1 Q β L n).grad) :=
    hsraw.congr (fun n =>
      (mainFlatPlusCorrectionModeGradientEnergy Q β L n).symm)
  refine ⟨hs, ?_⟩
  calc
    (∑' n : Gaussian.whiteBasisIndex,
        hilbertGradientEnergy Q (mainFlatPlusCorrectionH1 Q β L n).grad) =
      ∑' n : Gaussian.whiteBasisIndex, ∑ i : Fin 2,
        (lambda8Q3GaussianModeParentHessian Q β L (basisVec i) n).frobeniusNormalizedL2 Q ^ 2 := by
      apply tsum_congr
      intro n
      exact mainFlatPlusCorrectionModeGradientEnergy Q β L n
    _ = ∑ i : Fin 2, ∑' n : Gaussian.whiteBasisIndex,
        (lambda8Q3GaussianModeParentHessian Q β L (basisVec i) n).frobeniusNormalizedL2 Q ^ 2 := by
      rw [Summable.tsum_finsetSum (fun i hi => hs_i i)]
    _ = mainFlatSigmaSq β L := by
      rw [show (∑ i : Fin 2,
          ∑' n : Gaussian.whiteBasisIndex,
            (lambda8Q3GaussianModeParentHessian Q β L (basisVec i) n).frobeniusNormalizedL2 Q ^ 2) =
          ∑ i : Fin 2,
            β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) *
              ((basisVec i) 0 ^ 2 + (basisVec i) 1 ^ 2) by
        apply Finset.sum_congr rfl
        intro i hi
        exact lambda8Q3GaussianModeParent_hessian_energy_trace Q β L
          (basisVec i)]
      have hunit (i : Fin 2) :
          (basisVec i) 0 ^ 2 + (basisVec i) 1 ^ 2 = 1 := by
        fin_cases i <;> simp [basisVec]
      simp_rw [hunit]
      simp [mainFlatSigmaSq]

/-- The total plus flat-field H¹ seminorm has the source's `(1+√2)² σ²`
bound, with no assumed mode-family summability. -/
theorem mainFlatPlusGradientEnergy_tsum (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) :
    Summable (fun n : Gaussian.whiteBasisIndex =>
      hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad) ∧
    (∑' n : Gaussian.whiteBasisIndex,
      hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad) ≤
        (1 + Real.sqrt 2) ^ 2 * mainFlatSigmaSq β L := by
  classical
  let a := fun n : Gaussian.whiteBasisIndex =>
    Real.sqrt (hilbertGradientEnergy Q (mainFlatPlusSourceH1 Q β L n).grad)
  let b := fun n : Gaussian.whiteBasisIndex =>
    Real.sqrt (hilbertGradientEnergy Q (mainFlatPlusCorrectionH1 Q β L n).grad)
  let c := fun n : Gaussian.whiteBasisIndex =>
    Real.sqrt (hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad)
  have hsource := mainFlatPlusSourceGradientEnergy_tsum Q β L
  have hcorrect := mainFlatPlusCorrectionGradientEnergy_tsum Q β L
  have hsigma : 0 ≤ mainFlatSigmaSq β L := by
    unfold mainFlatSigmaSq
    positivity
  have hsa (n : Gaussian.whiteBasisIndex) :
      a n ^ 2 = hilbertGradientEnergy Q
        (mainFlatPlusSourceH1 Q β L n).grad := by
    exact Real.sq_sqrt (mainHilbertGradientEnergy_nonneg Q
      (mainFlatPlusSourceH1 Q β L n).grad)
  have hsb (n : Gaussian.whiteBasisIndex) :
      b n ^ 2 = hilbertGradientEnergy Q
        (mainFlatPlusCorrectionH1 Q β L n).grad := by
    exact Real.sq_sqrt (mainHilbertGradientEnergy_nonneg Q
      (mainFlatPlusCorrectionH1 Q β L n).grad)
  have hsc (n : Gaussian.whiteBasisIndex) :
      c n ^ 2 = hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad := by
    exact Real.sq_sqrt (mainHilbertGradientEnergy_nonneg Q
      (mainFlatPlusH1 Q β L n).grad)
  have ha : Summable (fun n => a n ^ 2) :=
    hsource.1.congr (fun n => (hsa n).symm)
  have hb : Summable (fun n => b n ^ 2) :=
    hcorrect.1.congr (fun n => (hsb n).symm)
  have hpoint (n : Gaussian.whiteBasisIndex) :
      0 ≤ c n ∧ c n ≤ a n + b n := by
    constructor
    · exact Real.sqrt_nonneg _
    · exact mainFlatPlusModeGradient_sqrt_le Q β L n
  have htriangle := main_sqrt_tsum_sq_le_of_pointwise ha hb
    (fun n => (hpoint n).1) (fun n => (hpoint n).2)
  have hsplus : Summable (fun n : Gaussian.whiteBasisIndex =>
      hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad) :=
    htriangle.1.congr hsc
  have hsumA : (∑' n : Gaussian.whiteBasisIndex, a n ^ 2) =
      2 * mainFlatSigmaSq β L := by
    calc
      _ = ∑' n : Gaussian.whiteBasisIndex,
          hilbertGradientEnergy Q (mainFlatPlusSourceH1 Q β L n).grad := by
        apply tsum_congr
        intro n
        exact hsa n
      _ = _ := hsource.2
  have hsumB : (∑' n : Gaussian.whiteBasisIndex, b n ^ 2) =
      mainFlatSigmaSq β L := by
    calc
      _ = ∑' n : Gaussian.whiteBasisIndex,
          hilbertGradientEnergy Q (mainFlatPlusCorrectionH1 Q β L n).grad := by
        apply tsum_congr
        intro n
        exact hsb n
      _ = _ := hcorrect.2
  have hsumC : (∑' n : Gaussian.whiteBasisIndex, c n ^ 2) =
      ∑' n : Gaussian.whiteBasisIndex,
        hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad := by
    apply tsum_congr
    intro n
    exact hsc n
  have hroot := htriangle.2
  rw [hsumA, hsumB, hsumC] at hroot
  have hrootRhs :
      Real.sqrt (2 * mainFlatSigmaSq β L) +
          Real.sqrt (mainFlatSigmaSq β L) =
        (1 + Real.sqrt 2) * Real.sqrt (mainFlatSigmaSq β L) := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
    ring
  rw [hrootRhs] at hroot
  refine ⟨hsplus, ?_⟩
  have hsum_nonneg : 0 ≤
      ∑' n : Gaussian.whiteBasisIndex,
        hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad :=
    tsum_nonneg (fun n => mainHilbertGradientEnergy_nonneg Q
      (mainFlatPlusH1 Q β L n).grad)
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mpr hroot
  calc
    _ = Real.sqrt (∑' n : Gaussian.whiteBasisIndex,
        hilbertGradientEnergy Q (mainFlatPlusH1 Q β L n).grad) ^ 2 := by
      rw [Real.sq_sqrt hsum_nonneg]
    _ ≤ ((1 + Real.sqrt 2) * Real.sqrt (mainFlatSigmaSq β L)) ^ 2 := hsq
    _ = (1 + Real.sqrt 2) ^ 2 * mainFlatSigmaSq β L := by
      rw [mul_pow, Real.sq_sqrt hsigma]

private theorem mainFlatOscillationEnergy_tsum_le {κ : Type*} [Fintype κ]
    (Q : TriadicCube 2)
    (F : Gaussian.whiteBasisIndex →
      HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ κ))
    (henergy : Summable (fun n => hilbertGradientEnergy Q (F n).grad))
    (B : ℝ)
    (henergyTotal : (∑' n, hilbertGradientEnergy Q (F n).grad) ≤ B) :
    Summable (fun n =>
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) (F n).toFun) ^ 2) ∧
    (∑' n,
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) (F n).toFun) ^ 2) ≤
      (cubeScaleFactor Q * planarC0) ^ 2 * B := by
  classical
  let p := fun n : Gaussian.whiteBasisIndex =>
    hilbertPositiveCircHaarNorm Q
      ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) (F n).toFun
  let D := (cubeScaleFactor Q * planarC0) ^ 2
  have hc0nn : 0 ≤ planarC0 := by
    unfold planarC0
    exact Real.sqrt_nonneg _
  have hpoincare (n : Gaussian.whiteBasisIndex) :
      p n ≤ cubeScaleFactor Q * planarC0 *
        Real.sqrt (hilbertGradientEnergy Q (F n).grad) := by
    have hp := hilbert_positive_circ_poincare_norm Q (1 / 4 : ℝ)
      (by constructor <;> norm_num) (F n)
    rw [haarPoincareC2_quarter, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hc0nn] at hp
    simpa only [p] using hp
  have hsq (n : Gaussian.whiteBasisIndex) :
      p n ^ 2 ≤ D * hilbertGradientEnergy Q (F n).grad := by
    have hgrad := mainHilbertGradientEnergy_nonneg Q (F n).grad
    have hright : 0 ≤ cubeScaleFactor Q * planarC0 *
        Real.sqrt (hilbertGradientEnergy Q (F n).grad) :=
      mul_nonneg (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le hc0nn)
        (Real.sqrt_nonneg _)
    have h := (sq_le_sq₀ (Real.sqrt_nonneg _) hright).mpr (hpoincare n)
    dsimp [D]
    calc
      _ ≤ (cubeScaleFactor Q * planarC0 *
          Real.sqrt (hilbertGradientEnergy Q (F n).grad)) ^ 2 := h
      _ = (cubeScaleFactor Q * planarC0) ^ 2 *
          hilbertGradientEnergy Q (F n).grad := by
        rw [mul_pow, Real.sq_sqrt hgrad]
  have hD : 0 ≤ D := sq_nonneg _
  have hbound : Summable (fun n : Gaussian.whiteBasisIndex =>
      D * hilbertGradientEnergy Q (F n).grad) := henergy.mul_left D
  have hp : Summable (fun n : Gaussian.whiteBasisIndex => p n ^ 2) :=
    hbound.of_nonneg_of_le (fun n => sq_nonneg _) hsq
  have hsum : (∑' n : Gaussian.whiteBasisIndex, p n ^ 2) ≤ D * B := by
    calc
      (∑' n : Gaussian.whiteBasisIndex, p n ^ 2) ≤
          ∑' n : Gaussian.whiteBasisIndex,
            D * hilbertGradientEnergy Q (F n).grad :=
        hp.tsum_le_tsum hsq hbound
      _ = D * ∑' n : Gaussian.whiteBasisIndex,
          hilbertGradientEnergy Q (F n).grad := tsum_mul_left
      _ ≤ D * B := mul_le_mul_of_nonneg_left henergyTotal hD
  refine ⟨?_, ?_⟩
  · change Summable (fun n => p n ^ 2)
    exact hp
  · simpa only [p, D] using hsum

private theorem mainFlatOscillationNorm_tsum_le {κ : Type*} [Fintype κ]
    (Q : TriadicCube 2)
    (F : Gaussian.whiteBasisIndex →
      HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ κ))
    (henergy : Summable (fun n => hilbertGradientEnergy Q (F n).grad))
    (B : ℝ)
    (henergyTotal : (∑' n, hilbertGradientEnergy Q (F n).grad) ≤ B) :
    Real.sqrt (∑' n,
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ))) (F n).toFun) ^ 2) ≤
      cubeScaleFactor Q * planarC0 * Real.sqrt B := by
  have h := mainFlatOscillationEnergy_tsum_le Q F henergy B henergyTotal
  have hc0nn : 0 ≤ planarC0 := by
    unfold planarC0
    exact Real.sqrt_nonneg _
  have hprod : 0 ≤ cubeScaleFactor Q * planarC0 :=
    mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le hc0nn
  calc
    _ ≤ Real.sqrt ((cubeScaleFactor Q * planarC0) ^ 2 * B) :=
      Real.sqrt_le_sqrt h.2
    _ = cubeScaleFactor Q * planarC0 * Real.sqrt B := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
        abs_of_nonneg hprod]

private theorem main_planarC0_lt_044 : planarC0 < 440 / 1000 := by
  have h := local_caps.2.1
  change Real.sqrt (8 * Real.sqrt 3 /
    (Real.pi ^ 2 * (9 - Real.sqrt 3))) < 440 / 1000 at h
  have heq : planarC0 = Real.sqrt (8 * Real.sqrt 3 /
      (Real.pi ^ 2 * (9 - Real.sqrt 3))) := by
    unfold planarC0
    congr 1
    ring
  rw [heq]
  exact h

/-- The q3 minus-field broken quarter-order oscillation is bounded by the
certified `o_m` once the source shell scaling is supplied. -/
private theorem mainFlatMinusOscillation_le_of_scale (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (A2 : ℝ)
    (hscale : cubeScaleFactor Q ^ 2 * mainFlatSigmaSq β L =
      (31.2 : ℝ) * A2) :
    Real.sqrt (∑' n : Gaussian.whiteBasisIndex,
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (mainFlatMinusH1 Q β L n).toFun) ^ 2) ≤
      (440 / 1000 : ℝ) * Real.sqrt ((31.2 : ℝ) * A2) := by
  have htrace := mainFlatMinusGradientEnergy_tsum Q β L
  have hnorm := mainFlatOscillationNorm_tsum_le Q
    (fun n => mainFlatMinusH1 Q β L n) htrace.1
    (mainFlatSigmaSq β L) (le_of_eq htrace.2)
  have hscaleroot :
      Real.sqrt ((31.2 : ℝ) * A2) =
        cubeScaleFactor Q * Real.sqrt (mainFlatSigmaSq β L) := by
    rw [← hscale, Real.sqrt_mul (sq_nonneg (cubeScaleFactor Q)),
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le]
  have hcoef := main_planarC0_lt_044
  calc
    _ ≤ cubeScaleFactor Q * planarC0 * Real.sqrt (mainFlatSigmaSq β L) := hnorm
    _ = (cubeScaleFactor Q * Real.sqrt (mainFlatSigmaSq β L)) * planarC0 := by ring
    _ ≤ (cubeScaleFactor Q * Real.sqrt (mainFlatSigmaSq β L)) * (440 / 1000) :=
      mul_le_mul_of_nonneg_left hcoef.le
        (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
          (Real.sqrt_nonneg _))
    _ = (440 / 1000 : ℝ) * Real.sqrt ((31.2 : ℝ) * A2) := by
      rw [hscaleroot]
      ring

/-- The q3 plus-field broken quarter-order oscillation is bounded by `o_p`. -/
private theorem mainFlatPlusOscillation_le_of_scale (Q : TriadicCube 2) (β : ℝ)
    (L : {l : ℝ // 0 < l}) (A2 : ℝ)
    (hscale : cubeScaleFactor Q ^ 2 * mainFlatSigmaSq β L =
      (31.2 : ℝ) * A2) :
    Real.sqrt (∑' n : Gaussian.whiteBasisIndex,
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (mainFlatPlusH1 Q β L n).toFun) ^ 2) ≤
      (1 + Real.sqrt 2) * ((440 / 1000 : ℝ) * Real.sqrt ((31.2 : ℝ) * A2)) := by
  have htrace := mainFlatPlusGradientEnergy_tsum Q β L
  have hsigma : 0 ≤ mainFlatSigmaSq β L := by
    unfold mainFlatSigmaSq
    positivity
  have hnorm := mainFlatOscillationNorm_tsum_le Q
    (fun n => mainFlatPlusH1 Q β L n) htrace.1
    ((1 + Real.sqrt 2) ^ 2 * mainFlatSigmaSq β L) htrace.2
  have hfactor : 0 ≤ 1 + Real.sqrt 2 := by positivity
  have hroot :
      Real.sqrt ((1 + Real.sqrt 2) ^ 2 * mainFlatSigmaSq β L) =
        (1 + Real.sqrt 2) * Real.sqrt (mainFlatSigmaSq β L) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hfactor]
  have hscaleroot :
      Real.sqrt ((31.2 : ℝ) * A2) =
        cubeScaleFactor Q * Real.sqrt (mainFlatSigmaSq β L) := by
    rw [← hscale, Real.sqrt_mul (sq_nonneg (cubeScaleFactor Q)),
      Real.sqrt_sq_eq_abs,
      abs_of_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le]
  have hcoef := main_planarC0_lt_044
  calc
    _ ≤ cubeScaleFactor Q * planarC0 *
        Real.sqrt ((1 + Real.sqrt 2) ^ 2 * mainFlatSigmaSq β L) := hnorm
    _ = (cubeScaleFactor Q * (1 + Real.sqrt 2) *
        Real.sqrt (mainFlatSigmaSq β L)) * planarC0 := by
      rw [hroot]
      ring
    _ ≤ (cubeScaleFactor Q * (1 + Real.sqrt 2) *
        Real.sqrt (mainFlatSigmaSq β L)) * (440 / 1000) :=
      mul_le_mul_of_nonneg_left hcoef.le
        (mul_nonneg
          (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
            hfactor) (Real.sqrt_nonneg _))
    _ = (1 + Real.sqrt 2) *
        ((440 / 1000 : ℝ) * Real.sqrt ((31.2 : ℝ) * A2)) := by
      rw [hscaleroot]
      ring

/-- The source shell to parent side ratio, `L = 3⁶ r`. -/
noncomputable def mainFlatQ3Length (Q : TriadicCube 2) : {l : ℝ // 0 < l} :=
  ⟨cubeScaleFactor Q * (3 : ℝ) ^ 6,
    mul_pos (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q) (by positivity)⟩

/-- The exact relation `r² σ² = 31.2 A₂` for the q3 shell scale and
`A₂ = b² 3⁻¹²`. -/
theorem mainFlatSigmaSq_q3_shell_scale (Q : TriadicCube 2) (b : ℝ) :
    cubeScaleFactor Q ^ 2 * mainFlatSigmaSq b (mainFlatQ3Length Q) =
      (31.2 : ℝ) * mainA2 (b ^ 2) := by
  have hcoef : mainFlatSigmaSq b (mainFlatQ3Length Q) =
      (156 / 5 : ℝ) * b ^ 2 /
        (cubeScaleFactor Q * (3 : ℝ) ^ 6) ^ 2 := by
    unfold mainFlatSigmaSq mainFlatQ3Length
    change 2 * (b ^ 2 / (cubeScaleFactor Q * (3 : ℝ) ^ 6) ^ 2 *
      (78 / 5 : ℝ)) = _
    ring
  have hR : cubeScaleFactor Q ≠ 0 :=
    (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).ne'
  have hnorm : cubeScaleFactor Q ^ 2 *
      ((156 / 5 : ℝ) * b ^ 2 /
        (cubeScaleFactor Q * (3 : ℝ) ^ 6) ^ 2) =
      (156 / 5 : ℝ) * mainA2 (b ^ 2) := by
    unfold mainA2
    norm_num
    field_simp [hR]
    ring
  calc
    cubeScaleFactor Q ^ 2 * mainFlatSigmaSq b (mainFlatQ3Length Q) =
        cubeScaleFactor Q ^ 2 *
          ((156 / 5 : ℝ) * b ^ 2 /
            (cubeScaleFactor Q * (3 : ℝ) ^ 6) ^ 2) := by rw [hcoef]
    _ = (156 / 5 : ℝ) * mainA2 (b ^ 2) := hnorm
    _ = (31.2 : ℝ) * mainA2 (b ^ 2) := by norm_num

/-- The source-scaled q3 minus-field oscillation bound, with no scaling
identity left as a premise. -/
theorem mainFlatMinusOscillation_q3_shell (Q : TriadicCube 2) (b : ℝ) :
    Real.sqrt (∑' n : Gaussian.whiteBasisIndex,
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (mainFlatMinusH1 Q b (mainFlatQ3Length Q) n).toFun) ^ 2) ≤
      (440 / 1000 : ℝ) * Real.sqrt ((31.2 : ℝ) * mainA2 (b ^ 2)) := by
  exact mainFlatMinusOscillation_le_of_scale Q b (mainFlatQ3Length Q)
    (mainA2 (b ^ 2)) (mainFlatSigmaSq_q3_shell_scale Q b)

/-- The source-scaled q3 plus-field oscillation bound, with no scaling
identity left as a premise. -/
theorem mainFlatPlusOscillation_q3_shell (Q : TriadicCube 2) (b : ℝ) :
    Real.sqrt (∑' n : Gaussian.whiteBasisIndex,
      (hilbertPositiveCircHaarNorm Q
        ((3 : ℝ) ^ (2 * (1 / 4 : ℝ)))
        (mainFlatPlusH1 Q b (mainFlatQ3Length Q) n).toFun) ^ 2) ≤
      (1 + Real.sqrt 2) * ((440 / 1000 : ℝ) *
        Real.sqrt ((31.2 : ℝ) * mainA2 (b ^ 2))) := by
  exact mainFlatPlusOscillation_le_of_scale Q b (mainFlatQ3Length Q)
    (mainA2 (b ^ 2)) (mainFlatSigmaSq_q3_shell_scale Q b)

end

end ASDExplicitGamma.Main
