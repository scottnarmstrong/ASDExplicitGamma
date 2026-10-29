module

public import ASDExplicitGamma.Triadic.SensitivityWeakEnergy
public import ASDExplicitGamma.Triadic.SensitivityProduct
public import ASDExplicitGamma.Triadic.PlanarPositiveProductBounds
public import ASDExplicitGamma.Triadic.PlanarDirichletBridge
public import ASDExplicitGamma.Triadic.DiagEnergyCongr
public import ASDExplicitGamma.Response.FrameAlgebra
public import ASDExplicitGamma.Variational.LemmaVSobolev
public import Homogenization.Multiscale.NormalizedDomainCube

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The exact response-pair Haar budget and polarized integration-by-parts
identity used in the explicit coarse sensitivity derivative. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Homogenization.Book.Ch02 Homogenization.Book.Ch04
open scoped BigOperators ENNReal

noncomputable section

/-- The explicit source constant in the first-variation estimate. -/
def sensitivityA2 : ℝ := Real.sqrt (planarC0 ^ 2 + sensitivityB2 ^ 2)

private theorem sensitivity_polarization_pointwise (c : ℝ) (u v : Vec 2) :
    vecDot v (matVecMul (c • responsePlanarJ) u) =
      vecDot ((1 / 2 : ℝ) • (u + v))
        (matVecMul (c • responsePlanarJ) (u - v)) := by
  simp [vecDot, matVecMul, responsePlanarJ, Fin.sum_univ_two,
    Matrix.smul_apply, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  ring

private theorem sensitivity_skew_transfer_pointwise (c : ℝ) (p g m : Vec 2) :
    vecDot (-p + g) (matVecMul (c • responsePlanarJ) m) =
      vecDot (matVecMul (c • responsePlanarJ) p -
        matVecMul (c • responsePlanarJ) g) m := by
  simp [vecDot, matVecMul, responsePlanarJ, Fin.sum_univ_two,
    Matrix.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
  ring

private theorem sensitivity_blockQuadratic_neg (A : BlockMat 2) (p q : Vec 2) :
    blockVecDot (-p, -q) (blockMatVecMul A (-p, -q)) =
      blockVecDot (p, q) (blockMatVecMul A (p, q)) := by
  simp [blockVecDot, blockMatVecMul, matVecMul, vecDot, Fin.sum_univ_two]
  ring

private theorem sensitivity_bookAverage_eq_cubeAverage (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) :
    Book.Ch02.average (Book.Ch02.cubeDomain Q) f = cubeAverage Q f := by
  rw [Book.Ch02.average, Book.Ch02.cubeDomain_coe]
  change integralAverage (openCubeSet Q) f = cubeAverage Q f
  exact (cubeAverage_eq_integralAverage_openCubeSet Q f).symm

private theorem sensitivity_rawMeasure_eq_smul_normalized (Q : TriadicCube 2) :
    volumeMeasureOn (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
  rw [volumeMeasureOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  rw [normalizedCubeMeasure, cubeMeasure, smul_smul]
  have hcoeff : ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (cubeVolume_pos Q).le]
    rw [mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)), ENNReal.ofReal_one]
  rw [hcoeff, one_smul]

private theorem sensitivity_memLp_top_raw_of_normalized (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} (hf : MemLp f ⊤ (normalizedCubeMeasure Q)) :
    MemLp f ⊤ (volumeMeasureOn (openCubeSet Q)) := by
  rw [sensitivity_rawMeasure_eq_smul_normalized]
  exact hf.smul_measure ENNReal.ofReal_ne_top

private theorem sensitivity_cubeAverage_eq_volumeAverage (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) :
    cubeAverage Q f = volumeAverage (openCubeSet Q) f := by
  rw [cubeAverage_eq_integralAverage_openCubeSet]
  rfl

private theorem sensitivity_volumeAverage_congr_raw_ae {U : Set (Vec 2)}
    {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact integral_congr_ae hfg

private theorem sensitivity_cubeAverage_congr_raw_ae (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) :
    cubeAverage Q f = cubeAverage Q g := by
  rw [sensitivity_cubeAverage_eq_volumeAverage,
    sensitivity_cubeAverage_eq_volumeAverage]
  exact sensitivity_volumeAverage_congr_raw_ae hfg

private theorem sensitivity_vectorPairing_eq_cubeAverage (Q : TriadicCube 2)
    {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    vectorPairing Q F G = cubeAverage Q (fun x => vecDot (F x) (G x)) := by
  unfold vectorPairing
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  simp_rw [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  simpa [vecDot] using
    (integral_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hG i))).symm

private theorem sensitivity_pairing_add_left (Q : TriadicCube 2)
    {f g h : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    pairing Q (fun x => f x + g x) h = pairing Q f h + pairing Q g h := by
  unfold pairing
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure, add_mul]
  change (∫ x, (fun x => f x * h x) x + (fun x => g x * h x) x ∂
      normalizedCubeMeasure Q) = _
  exact integral_add (hf.integrable_mul hh) (hg.integrable_mul hh)

private theorem sensitivity_vectorPairing_add_left (Q : TriadicCube 2)
    {F G H : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    vectorPairing Q (fun x i => F x i + G x i) H =
      vectorPairing Q F H + vectorPairing Q G H := by
  unfold vectorPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact sensitivity_pairing_add_left Q (hF i) (hG i) (hH i)

private theorem sensitivity_vectorPairing_sub_left (Q : TriadicCube 2)
    {F G H : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    vectorPairing Q (fun x i => F x i - G x i) H =
      vectorPairing Q F H - vectorPairing Q G H := by
  unfold vectorPairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact pairing_sub_left Q (hF i) (hG i) (hH i)

private theorem sensitivity_energy_smul_local (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (c : ℝ) :
    energy Q (fun x => c * f x) = c ^ 2 * energy Q f := by
  rw [energy_eq_integral_sq, energy_eq_integral_sq]
  simp only [mul_pow]
  rw [integral_const_mul]

private theorem sensitivity_cubeIncrement_smul_local (Q : TriadicCube 2) (n : ℕ)
    (f : Vec 2 → ℝ) (c : ℝ) :
    cubeIncrement Q n (fun x => c * f x) =
      fun x => c * cubeIncrement Q n f x := by
  cases n with
  | zero => simp [cubeIncrement_zero, projection_smul]
  | succ n =>
      simp only [cubeIncrement_succ, projection_smul]
      funext x
      ring

private theorem sensitivity_constantMode_increment_summable (Q : TriadicCube 2)
    (h : PlanarW2Infinity Q) (c : ℝ) :
    Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => h.value.toFun x * c))) := by
  have hbase := positiveHaarIncrementSeries_summable Q
    h.value.memL2_normalizedCubeMeasure h.value.grad_memL2_normalizedCubeMeasure
    h.value.hasWeakGradient
  have hterm (k : ℕ) :
      (Real.sqrt 3) ^ (k + 1) *
          energy Q (cubeIncrement Q (k + 1) (fun x => h.value.toFun x * c)) =
        c ^ 2 * ((Real.sqrt 3) ^ (k + 1) *
          energy Q (cubeIncrement Q (k + 1) h.value.toFun)) := by
    have hfun : (fun x => h.value.toFun x * c) = fun x => c * h.value.toFun x := by
      funext x
      ring
    rw [hfun, sensitivity_cubeIncrement_smul_local,
      sensitivity_energy_smul_local]
    ring
  exact (hbase.mul_left (c ^ 2)).congr fun k => (hterm k).symm

private theorem sensitivity_fin2_eq_one {i : Fin 2} (hi : i ≠ 0) : i = 1 := by
  apply Fin.ext
  have hval : i.val ≠ 0 := by
    intro hval
    apply hi
    exact Fin.ext hval
  omega

private noncomputable def sensitivityJGradientW1 {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) : PlanarW1Infinity Q where
  component := fun i => if i = 0 then -(h.gradient.component 1) else h.gradient.component 0
  component_memLp_top := by
    intro i
    by_cases hi : i = 0
    · subst i
      have hEq : (-(h.gradient.component 1).toFun) =ᵐ[normalizedCubeMeasure Q]
          (fun x => -(h.gradient.component 1).toFun x) :=
        Filter.Eventually.of_forall fun x => rfl
      simpa [H1Function.neg_toFun] using
        (MeasureTheory.memLp_congr_ae hEq).mp
          ((h.gradient.component_memLp_top 1).neg)
    · have hi1 := sensitivity_fin2_eq_one hi
      subst i
      exact h.gradient.component_memLp_top 0
  derivative_memLp_top := by
    intro i j
    by_cases hi : i = 0
    · subst i
      have hEq : (-fun x => (h.gradient.component 1).grad x j) =ᵐ[
          normalizedCubeMeasure Q] (fun x => -(h.gradient.component 1).grad x j) :=
        Filter.Eventually.of_forall fun x => rfl
      simpa [H1Function.neg_grad] using
        (MeasureTheory.memLp_congr_ae hEq).mp
          ((h.gradient.derivative_memLp_top 1 j).neg)
    · have hi1 := sensitivity_fin2_eq_one hi
      subst i
      exact h.gradient.derivative_memLp_top 0 j

private theorem sensitivityJGradientW1_value {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    planarW1Value (sensitivityJGradientW1 h) = planarJGradient h := by
  funext x i
  by_cases hi : i = 0
  · subst i
    simp [planarW1Value, sensitivityJGradientW1, planarJGradient,
      planarQuarterTurn, h.gradient_eq]
  · have hi1 := sensitivity_fin2_eq_one hi
    subst i
    simp [planarW1Value, sensitivityJGradientW1, planarJGradient,
      planarQuarterTurn, h.gradient_eq]

private theorem sensitivityJGradientW1_valueLInf {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    planarW1ValueLInf (sensitivityJGradientW1 h) = planarGradientLInf h := by
  have hfun : (fun x => planarEuclideanNorm
      (planarW1Value (sensitivityJGradientW1 h) x)) =
      (fun x => planarEuclideanNorm (planarW1Value h.gradient x)) := by
    funext x
    rw [sensitivityJGradientW1_value]
    have hj : planarJGradient h x =
        planarQuarterTurn (planarW1Value h.gradient x) := by
      funext i
      by_cases hi : i = 0
      · subst i
        simp [planarJGradient, planarW1Value, planarQuarterTurn, h.gradient_eq]
      · have hi1 := sensitivity_fin2_eq_one hi
        subst i
        simp [planarJGradient, planarW1Value, planarQuarterTurn, h.gradient_eq]
    rw [hj]
    unfold planarEuclideanNorm planarQuarterTurn
    congr 1
    simp [Fin.sum_univ_two]
    ring
  rw [planarW1ValueLInf, planarGradientLInf, planarW1ValueLInf, hfun]

private theorem sensitivityJGradientW1_derivative_rows {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) (x : Vec 2) :
    planarW1Derivative (sensitivityJGradientW1 h) x =
      fun i j => planarQuarterTurn
        (fun k => planarW1Derivative h.gradient x k j) i := by
  funext i j
  by_cases hi : i = 0
  · subst i
    simp [planarW1Derivative, sensitivityJGradientW1, planarQuarterTurn,
      Pi.neg_apply]
  · have hi1 := sensitivity_fin2_eq_one hi
    subst i
    simp [planarW1Derivative, sensitivityJGradientW1, planarQuarterTurn]

private theorem sensitivity_frobenius_quarterTurnRows
    (A : Fin 2 → Fin 2 → ℝ) :
    planarFrobeniusNorm
        (fun i j => planarQuarterTurn (fun k => A k j) i) =
      planarFrobeniusNorm A := by
  unfold planarFrobeniusNorm planarQuarterTurn
  congr 1
  simp [Fin.sum_univ_two]
  ring

private theorem sensitivityJGradientW1_derivativeLInf {Q : TriadicCube 2}
    (h : PlanarW2Infinity Q) :
    planarW1DerivativeFrobeniusLInf (sensitivityJGradientW1 h) =
      planarHessianFrobeniusLInf h := by
  have hfun : (fun x => planarFrobeniusNorm
      (planarW1Derivative (sensitivityJGradientW1 h) x)) =
      (fun x => planarFrobeniusNorm (planarW1Derivative h.gradient x)) := by
    funext x
    rw [sensitivityJGradientW1_derivative_rows,
      sensitivity_frobenius_quarterTurnRows]
  rw [planarW1DerivativeFrobeniusLInf,
    planarHessianFrobeniusLInf, planarW1DerivativeFrobeniusLInf, hfun]


private theorem sensitivity_halfPair_residual_ae (Q : TriadicCube 2)
    (p : Vec 2) (r : H10Function (openCubeSet Q))
    (u v : H1Function (openCubeSet Q)) :
    (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (-p) r).grad =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      (fun x i => (u.grad x i + v.grad x i) / 2) →
    (fun x i => (u.grad x i + v.grad x i) / 2 + p i) =ᵐ[
        volume.restrict (cubeSet Q)]
      (fun x i => r.toH1Function.grad x i) := by
  intro hmid
  let V := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (-p) r
  have hVgrad : V.grad = fun x => -p + r.toH1Function.grad x := by
    funext x i
    simp [V, lemmaVAffinePotential, H1Function.add_grad,
      H1Function.affineOnIsSobolevRegularDomain_grad]
  have hraw : (fun x i => (u.grad x i + v.grad x i) / 2 + p i) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] (fun x i => r.toH1Function.grad x i) := by
    filter_upwards [hmid] with x hx
    funext i
    have hxi := congrFun hx i
    rw [hVgrad] at hxi
    change -p i + r.toH1Function.grad x i =
      (u.grad x i + v.grad x i) / 2 at hxi
    change (u.grad x i + v.grad x i) / 2 + p i =
      r.toH1Function.grad x i
    linarith
  have hopen : (fun x i => (u.grad x i + v.grad x i) / 2 + p i) =ᵐ[
      volume.restrict (openCubeSet Q)] (fun x i => r.toH1Function.grad x i) := by
    simpa [volumeMeasureOn] using hraw
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact hopen

private theorem sensitivity_derivative_pairing_split (Q : TriadicCube 2)
    (h : PlanarW2Infinity Q) (p : Vec 2)
    (r : H10Function (openCubeSet Q)) (u v : H1Function (openCubeSet Q))
    (huGrad : ∀ i, MemLp (fun x => u.grad x i) 2 (normalizedCubeMeasure Q))
    (hvGrad : ∀ i, MemLp (fun x => v.grad x i) 2 (normalizedCubeMeasure Q))
    (hmid : (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q)
        (-p) r).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x i => (u.grad x i + v.grad x i) / 2)) :
    Book.Ch02.average (Book.Ch02.cubeDomain Q) (fun x =>
      vecDot (v.grad x)
        (matVecMul ((sensitivityMatrixDirection h).1 x) (u.grad x))) =
      vectorPairing Q (fun x i => h.value.toFun x *
          matVecMul responsePlanarJ p i)
          (fun x i => u.grad x i - v.grad x i) +
        vectorPairing Q (fun x i =>
          planarJGradient h x i * r.toH1Function.toFun x)
          (fun x i => u.grad x i - v.grad x i) := by
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let V := lemmaVAffinePotential hU (-p) r
  let Gm : Vec 2 → Fin 2 → ℝ := fun x i => u.grad x i - v.grad x i
  let F0 : Vec 2 → Fin 2 → ℝ := fun x i =>
    h.value.toFun x * matVecMul responsePlanarJ p i
  let Fr : Vec 2 → Fin 2 → ℝ := fun x i =>
    h.value.toFun x * matVecMul responsePlanarJ (r.toH1Function.grad x) i
  let F1 : Vec 2 → Fin 2 → ℝ := fun x i =>
    planarJGradient h x i * r.toH1Function.toFun x
  have hVgrad : V.grad = fun x => -p + r.toH1Function.grad x := by
    funext x i
    simp [V, lemmaVAffinePotential, H1Function.add_grad,
      H1Function.affineOnIsSobolevRegularDomain_grad]
  have hGm (i : Fin 2) : MemLp (fun x => Gm x i) 2
      (normalizedCubeMeasure Q) := by
    exact (huGrad i).sub (hvGrad i)
  have hF0 (i : Fin 2) : MemLp (fun x => F0 x i) 2
      (normalizedCubeMeasure Q) := by
    simpa [F0, mul_comm] using h.value.memL2_normalizedCubeMeasure.const_mul
      (matVecMul responsePlanarJ p i)
  let b := sensitivityJGradientW1 h
  have hF1 (i : Fin 2) : MemLp (fun x => F1 x i) 2
      (normalizedCubeMeasure Q) := by
    have hb : MemLp (fun x => planarW1Value b x i) ⊤
        (normalizedCubeMeasure Q) := by
      simpa [b, planarW1Value] using b.component_memLp_top i
    have hr : MemLp r.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
      r.toH1Function.memL2_normalizedCubeMeasure
    have hm : MemLp (fun x => r.toH1Function.toFun x *
        planarW1Value b x i) 2 (normalizedCubeMeasure Q) := hr.mul hb
    simpa [F1, b, sensitivityJGradientW1_value, mul_comm] using hm
  have hJr (i : Fin 2) : MemLp
      (fun x => matVecMul responsePlanarJ (r.toH1Function.grad x) i) 2
      (normalizedCubeMeasure Q) := by
    fin_cases i
    · have hneg : (-(fun x => r.toH1Function.grad x 1)) =ᵐ[
          normalizedCubeMeasure Q] (fun x => -r.toH1Function.grad x 1) :=
        Filter.Eventually.of_forall fun _ => rfl
      have hmem := (r.toH1Function.grad_memL2_normalizedCubeMeasure 1).neg
      have hmem' := (memLp_congr_ae hneg).mp hmem
      simpa [matVecMul, responsePlanarJ, Fin.sum_univ_two] using hmem'
    · simpa [matVecMul, responsePlanarJ, Fin.sum_univ_two] using
        r.toH1Function.grad_memL2_normalizedCubeMeasure 0
  have hFr (i : Fin 2) : MemLp (fun x => Fr x i) 2
      (normalizedCubeMeasure Q) := by
    exact h.value_memLp_top_normalized.mul (hJr i)
  have hpolAE : (fun x => vecDot (v.grad x)
      (matVecMul ((sensitivityMatrixDirection h).1 x) (u.grad x))) =ᵐ[
        volumeMeasureOn U] (fun x => vecDot (V.grad x)
          (matVecMul ((sensitivityMatrixDirection h).1 x) (Gm x))) := by
    filter_upwards [hmid] with x hx
    have hv : V.grad x = (1 / 2 : ℝ) • (u.grad x + v.grad x) := by
      funext i
      have hi := congrFun hx i
      change V.grad x i = _ at hi
      rw [hi]
      simp [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hv]
    change vecDot (v.grad x)
        (matVecMul (h.value.toFun x • responsePlanarJ) (u.grad x)) =
      vecDot ((1 / 2 : ℝ) • (u.grad x + v.grad x))
        (matVecMul (h.value.toFun x • responsePlanarJ)
          (u.grad x - v.grad x))
    exact sensitivity_polarization_pointwise (h.value.toFun x)
      (u.grad x) (v.grad x)
  have htransAE : (fun x => vecDot (V.grad x)
      (matVecMul ((sensitivityMatrixDirection h).1 x) (Gm x))) =ᵐ[
        volumeMeasureOn U] (fun x => vecDot (fun i => F0 x i - Fr x i) (Gm x)) := by
    filter_upwards [] with x
    rw [hVgrad]
    change vecDot (-p + r.toH1Function.grad x)
        (matVecMul (h.value.toFun x • responsePlanarJ) (Gm x)) =
      vecDot (fun i => h.value.toFun x * matVecMul responsePlanarJ p i -
        h.value.toFun x * matVecMul responsePlanarJ
          (r.toH1Function.grad x) i) (Gm x)
    have hrow : matVecMul (h.value.toFun x • responsePlanarJ) p -
        matVecMul (h.value.toFun x • responsePlanarJ) (r.toH1Function.grad x) =
          fun i => h.value.toFun x * matVecMul responsePlanarJ p i -
            h.value.toFun x * matVecMul responsePlanarJ
              (r.toH1Function.grad x) i := by
      funext i
      fin_cases i <;>
        simp [matVecMul, responsePlanarJ, Fin.sum_univ_two,
          smul_eq_mul]
    rw [← hrow]
    exact sensitivity_skew_transfer_pointwise (h.value.toFun x) p
      (r.toH1Function.grad x) (Gm x)
  have hsol : IsSolenoidalZeroNormalTraceOn U (fun x =>
      h.value.toFun x • matVecMul responsePlanarJ (r.toH1Function.grad x) -
        r.toH1Function.toFun x • lemmaVPlanarWeakColumnDivergence h.value x) := by
    apply lemmaVPlanar_lift_cancellation hU r h.value
    · exact h.value_memLp_top
    · intro i
      exact sensitivity_memLp_top_raw_of_normalized Q
        (h.grad_memLp_top_normalized i)
  let S : Vec 2 → Vec 2 := fun x =>
    h.value.toFun x • matVecMul responsePlanarJ (r.toH1Function.grad x) -
      r.toH1Function.toFun x • lemmaVPlanarWeakColumnDivergence h.value x
  have hS : S = fun x => fun i => Fr x i + F1 x i := by
    funext x i
    fin_cases i <;>
      simp [S, Fr, F1, lemmaVPlanarWeakColumnDivergence,
        planarJGradient, planarQuarterTurn, matVecMul, responsePlanarJ,
        Fin.sum_univ_two, Pi.smul_apply,
        smul_eq_mul] <;> ring
  have hwgrad : (u - v).grad = fun x => Gm x := by
    funext x i
    simp [Gm, H1Function.sub_grad]
  have hzint : (∫ x in U, vecDot (S x) ((u - v).grad x) ∂volume) = 0 := by
    exact hsol (u - v)
  have hzvol : volumeAverage U (fun x => vecDot (fun i => Fr x i + F1 x i)
      (Gm x)) = 0 := by
    have heq : (fun x => vecDot (fun i => Fr x i + F1 x i) (Gm x)) =ᵐ[
        volumeMeasureOn U] (fun x => vecDot (S x) ((u - v).grad x)) := by
      filter_upwards [] with x
      have hxS : S x = fun i => Fr x i + F1 x i := congrFun hS x
      rw [← hxS, hwgrad]
    rw [sensitivity_volumeAverage_congr_raw_ae heq]
    exact volumeAverage_eq_zero_of_integral_eq_zero hzint
  have hzCube : cubeAverage Q (fun x => vecDot (fun i => Fr x i + F1 x i)
      (Gm x)) = 0 := by
    rw [sensitivity_cubeAverage_eq_volumeAverage]
    exact hzvol
  have hzeroPair : vectorPairing Q Fr Gm + vectorPairing Q F1 Gm = 0 := by
    calc
      _ = vectorPairing Q (fun x i => Fr x i + F1 x i) Gm := by
        symm
        exact sensitivity_vectorPairing_add_left Q hFr hF1 hGm
      _ = cubeAverage Q (fun x => vecDot (fun i => Fr x i + F1 x i)
          (Gm x)) := sensitivity_vectorPairing_eq_cubeAverage Q
            (fun i => (hFr i).add (hF1 i)) hGm
      _ = 0 := hzCube
  have hderivAvg : Book.Ch02.average (Book.Ch02.cubeDomain Q) (fun x =>
      vecDot (v.grad x)
        (matVecMul ((sensitivityMatrixDirection h).1 x) (u.grad x))) =
      vectorPairing Q F0 Gm + vectorPairing Q F1 Gm := by
    rw [sensitivity_bookAverage_eq_cubeAverage]
    have hAE := hpolAE.trans htransAE
    have hleft : cubeAverage Q (fun x => vecDot (v.grad x)
        (matVecMul ((sensitivityMatrixDirection h).1 x) (u.grad x))) =
        cubeAverage Q (fun x => vecDot (fun i => F0 x i - Fr x i) (Gm x)) :=
      sensitivity_cubeAverage_congr_raw_ae Q hAE
    calc
      _ = vectorPairing Q (fun x i => F0 x i - Fr x i) Gm := by
        rw [hleft]
        exact (sensitivity_vectorPairing_eq_cubeAverage Q
          (fun i => (hF0 i).sub (hFr i)) hGm).symm
      _ = vectorPairing Q F0 Gm - vectorPairing Q Fr Gm :=
        sensitivity_vectorPairing_sub_left Q hF0 hFr hGm
      _ = vectorPairing Q F0 Gm + vectorPairing Q F1 Gm := by
        linarith [hzeroPair]
  exact hderivAvg

/-- The constant-load multiplier `h Jp` has the exact Euclidean load factor
and the source mean-zero positive-Haar bound. -/
theorem sensitivity_constantMode_positive_bound (Q : TriadicCube 2)
    (h : PlanarW2Infinity Q) (hmean : cubeAverage Q h.value.toFun = 0)
    (p : Vec 2) :
    vectorPositiveHaarNorm Q
        (fun x i => h.value.toFun x * matVecMul responsePlanarJ p i) ≤
      planarC0 * sensitivityD1 Q h * Real.sqrt (vecNormSq p) := by
  let c : Fin 2 → ℝ := matVecMul responsePlanarJ p
  have hcoord (i : Fin 2) :
      positiveHaarNorm Q (fun x => h.value.toFun x * c i) ^ 2 =
        (c i) ^ 2 * positiveHaarNorm Q h.value.toFun ^ 2 := by
    have hfun : (fun x => h.value.toFun x * c i) =
        fun x => c i * h.value.toFun x := by
      funext x
      ring
    rw [hfun, sensitivity_positiveHaarNorm_smul_sq]
  have hnormsq : vectorPositiveHaarNorm Q
      (fun x i => h.value.toFun x * c i) ^ 2 =
        vecNormSq p * positiveHaarNorm Q h.value.toFun ^ 2 := by
    rw [vectorPositiveHaarNorm_sq]
    calc
      (∑ i, positiveHaarNorm Q (fun x => h.value.toFun x * c i) ^ 2) =
          ∑ i, (c i) ^ 2 * positiveHaarNorm Q h.value.toFun ^ 2 :=
        Finset.sum_congr rfl fun i _ => hcoord i
      _ = (∑ i, (c i) ^ 2) * positiveHaarNorm Q h.value.toFun ^ 2 := by
        rw [Finset.sum_mul]
      _ = vecNormSq c * positiveHaarNorm Q h.value.toFun ^ 2 := by
        have hcSq : (∑ i, c i ^ 2) = vecNormSq c := by
          simp only [Fin.sum_univ_two, vecNormSq, vecDot]
          ring
        rw [hcSq]
      _ = vecNormSq p * positiveHaarNorm Q h.value.toFun ^ 2 := by
        dsimp [c]
        rw [responsePlanarJ_vecNormSq]
  have hpos := sensitivity_meanZero_positive_bound Q h hmean
  have hroot : 1 ≤ Real.sqrt (2 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hR := (cubeScaleFactor_pos' Q).le
  have hc0 : 0 ≤ planarC0 := Real.sqrt_nonneg _
  have hgrad : 0 ≤ planarGradientLInf h := by
    unfold planarGradientLInf planarW1ValueLInf
    positivity
  have hD : cubeScaleFactor Q * planarC0 * planarGradientLInf h ≤
      planarC0 * sensitivityD1 Q h := by
    unfold sensitivityD1
    nlinarith [mul_nonneg (mul_nonneg hR hc0) hgrad, hroot]
  have hmag : 0 ≤ Real.sqrt (vecNormSq p) := Real.sqrt_nonneg _
  have hbase : 0 ≤ planarC0 * sensitivityD1 Q h := by
    unfold sensitivityD1
    exact mul_nonneg hc0
      (mul_nonneg (mul_nonneg hR (Real.sqrt_nonneg _)) hgrad)
  have hposNonneg : 0 ≤ positiveHaarNorm Q h.value.toFun := Real.sqrt_nonneg _
  have hposSq : positiveHaarNorm Q h.value.toFun ^ 2 ≤
      (planarC0 * sensitivityD1 Q h) ^ 2 := by
    have hright0 : 0 ≤ planarC0 * sensitivityD1 Q h := hbase
    exact (sq_le_sq₀ hposNonneg hright0).2 (hpos.trans hD)
  have hsq : vectorPositiveHaarNorm Q
      (fun x i => h.value.toFun x * c i) ^ 2 ≤
        (planarC0 * sensitivityD1 Q h * Real.sqrt (vecNormSq p)) ^ 2 := by
    rw [hnormsq]
    calc
      vecNormSq p * positiveHaarNorm Q h.value.toFun ^ 2 =
          Real.sqrt (vecNormSq p) ^ 2 * positiveHaarNorm Q h.value.toFun ^ 2 := by
        rw [Real.sq_sqrt (vecNormSq_nonneg p)]
      _ ≤ Real.sqrt (vecNormSq p) ^ 2 * (planarC0 * sensitivityD1 Q h) ^ 2 :=
        mul_le_mul_of_nonneg_left hposSq (sq_nonneg _)
      _ = (planarC0 * sensitivityD1 Q h * Real.sqrt (vecNormSq p)) ^ 2 := by
        ring
  have hleft : 0 ≤ vectorPositiveHaarNorm Q
      (fun x i => h.value.toFun x * c i) := Real.sqrt_nonneg _
  have hright : 0 ≤ planarC0 * sensitivityD1 Q h * Real.sqrt (vecNormSq p) :=
    mul_nonneg hbase hmag
  exact (sq_le_sq₀ hleft hright).1 hsq

/-- The response pair's full gradient sum and difference spend at most four
inverse histories times the actual coarse quadratic. -/
theorem sensitivity_response_pair_derivative_budget (Q : TriadicCube 2) (ν : ℝ)
    (hν : 0 < ν) (k : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (uExp : ℝ) (hu : 0 < uExp) (hu4 : uExp ≤ 1 / 4) (p q : Vec 2) :
    ∃ r : H10Function (openCubeSet Q),
      ∃ u : AHarmonicFunction (responseFramePlanarCoefficientField ν 1 k) (openCubeSet Q),
      ∃ v : AHarmonicFunction
          (adjointCoeffField (responseFramePlanarCoefficientField ν 1 k)) (openCubeSet Q),
        IsResponseMaximizer (openCubeSet Q) p (-q)
          (responseFramePlanarCoefficientField ν 1 k) u ∧
        IsResponseMaximizer (openCubeSet Q) p q
          (adjointCoeffField (responseFramePlanarCoefficientField ν 1 k)) v ∧
        ((lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) (-p) r).grad =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
          (fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2)) ∧
        vectorWeakHaarEnergy Q (fun x i => u.toH1.grad x i + v.toH1.grad x i) +
          vectorWeakHaarEnergy Q (fun x i => u.toH1.grad x i - v.toH1.grad x i) ≤
          4 * (Book.Ch02.lambdaSqFinite Q uExp 2
            (sensitivityCoefficientFamily ν hν k))⁻¹ *
            blockVecDot (p, q) (blockMatVecMul
              (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
                (sensitivityBookCoeffOn Q ν hν k)) (p, q)) ∧
        blockVecDot (p, q)
            (blockMatVecMul
              (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
                (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q ν hν k)
                (sensitivityMatrixDirection h)) (p, q)) =
          Book.Ch02.average (Book.Ch02.cubeDomain Q) (fun x =>
            vecDot (v.toH1.grad x)
              (matVecMul ((sensitivityMatrixDirection h).1 x) (u.toH1.grad x))) := by
  let a := responseFramePlanarCoefficientField ν 1 k
  let aReg := sensitivityBaseRegField (Q₀ := Q) ν k
  let family := sensitivityCoefficientFamily ν hν k
  let hEll : IsEllipticFieldOn ν ((ν ^ 2 + ‖k‖ ^ 2) / ν) (openCubeSet Q) a := by
    simpa [a, div_one] using
      responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        ν 1 hν one_pos k
  have hAEL : Book.Ch04.AELocallyUniformlyEllipticField aReg :=
    sensitivityBaseRegField_aelocal (Q₀ := Q) ν hν k
  have hHist := sensitivity_inverse_lambda_ge_quarter Q aReg hAEL uExp hu hu4
  obtain ⟨r, u, v, hmid, hEv, hEu, huMax, hvMax, _⟩ :=
    sensitivity_response_load_pair Q ν 1 hν one_pos k (-p, -q)
  have huWeak := lemmaV_harmonic_vectorWeakHaarEnergy_le Q hEll u
  have hvWeak := lemmaV_adjoint_vectorWeakHaarEnergy_le Q hEll v
  have huEnergy : 0 ≤ cubeAverage Q (scalarVariationEnergyIntegrand a u) := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      (openCubeSet Q) a hEll u
  have hvEnergy : 0 ≤ cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v) := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
      (openCubeSet Q) (adjointCoeffField a)
      (isEllipticFieldOn_adjointCoeffField hEll) v
  have hEuCube : cubeAverage Q (scalarVariationEnergyIntegrand a u) =
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν 1 hν one_pos (-p, -q) k + 2 * vecDot p q := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    change volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a u) = _
    calc
      _ = responseFrameEnergyObservable (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν 1 hν one_pos (-p, -q) k + 2 * vecDot (-p) (-q) := hEu.symm
      _ = _ := by congr 1; simp [vecDot, Fin.sum_univ_two]
  have hEvCube : cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v) =
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
        ν 1 hν one_pos (-p, -q) k - 2 * vecDot p q := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    change volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand (adjointCoeffField a) v) = _
    calc
      _ = responseFrameEnergyObservable (measurableSet_openCubeSet Q)
          (by rw [volume_openCubeSet_toReal]; exact cubeVolume_pos Q)
          ν 1 hν one_pos (-p, -q) k - 2 * vecDot (-p) (-q) := hEv.symm
      _ = _ := by congr 1; simp [vecDot, Fin.sum_univ_two]
  have huWeak' : vectorWeakHaarEnergy Q u.toH1.grad ≤
      (Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ *
        cubeAverage Q (scalarVariationEnergyIntegrand a u) := by
    have hh : lemmaVInverseHistory Q a (Real.sqrt 3) ≤
        (Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ := by
      simpa [a, aReg, family, sensitivityCoefficientFamily, sensitivityBaseRegField] using hHist
    calc
      vectorWeakHaarEnergy Q u.toH1.grad ≤
          lemmaVInverseHistory Q a (Real.sqrt 3) *
            cubeAverage Q (scalarVariationEnergyIntegrand a u) := by
        simpa [a] using huWeak
      _ ≤ (Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ *
          cubeAverage Q (scalarVariationEnergyIntegrand a u) :=
        mul_le_mul_of_nonneg_right hh huEnergy
  have hvWeak' : vectorWeakHaarEnergy Q v.toH1.grad ≤
      (Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ *
        cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v) := by
    have hh : lemmaVInverseHistory Q a (Real.sqrt 3) ≤
        (Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ := by
      simpa [a, aReg, family, sensitivityCoefficientFamily, sensitivityBaseRegField] using hHist
    calc
      vectorWeakHaarEnergy Q v.toH1.grad ≤
          lemmaVInverseHistory Q a (Real.sqrt 3) *
            cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v) := by
        simpa [a] using hvWeak
      _ ≤ (Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ *
          cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v) :=
        mul_le_mul_of_nonneg_right hh hvEnergy
  have hObs := sensitivity_response_observable_eq_coarseQuadratic Q ν hν k (-p, -q)
  let A := Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
    (sensitivityBookCoeffOn Q ν hν k)
  have hEnergySum :
      cubeAverage Q (scalarVariationEnergyIntegrand a u) +
        cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v) =
          2 * blockVecDot (p, q) (blockMatVecMul A (p, q)) := by
    rw [hEuCube, hEvCube, hObs]
    dsimp [A]
    rw [sensitivity_blockQuadratic_neg]
    ring
  have hpara := sensitivity_vectorWeakEnergy_parallelogram Q
    (fun x i => u.toH1.grad x i) (fun x i => v.toH1.grad x i)
    (fun i => u.toH1.grad_memL2_normalizedCubeMeasure i)
    (fun i => v.toH1.grad_memL2_normalizedCubeMeasure i)
  refine ⟨r, u, v, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using huMax
  · simpa using hvMax
  · exact hmid
  · rw [hpara]
    calc
      2 * vectorWeakHaarEnergy Q u.toH1.grad + 2 * vectorWeakHaarEnergy Q v.toH1.grad ≤
        2 * ((Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ *
          cubeAverage Q (scalarVariationEnergyIntegrand a u)) +
        2 * ((Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ *
          cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v)) := by
            exact add_le_add (mul_le_mul_of_nonneg_left huWeak' (by norm_num))
              (mul_le_mul_of_nonneg_left hvWeak' (by norm_num))
      _ = 2 * (Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ *
          (cubeAverage Q (scalarVariationEnergyIntegrand a u) +
            cubeAverage Q (scalarVariationEnergyIntegrand (adjointCoeffField a) v)) := by ring
      _ = 4 * (Book.Ch02.lambdaSqFinite Q uExp 2 family)⁻¹ *
          blockVecDot (p, q) (blockMatVecMul A (p, q)) := by rw [hEnergySum]; ring
  · let aBook := sensitivityBookCoeffOn Q ν hν k
    have hu' : IsResponseMaximizer (openCubeSet Q) p (-q)
        (responseFramePlanarCoefficientField ν 1 k) u := by
      simpa using huMax
    have hv' : IsResponseMaximizer (openCubeSet Q) p q
        (adjointCoeffField (responseFramePlanarCoefficientField ν 1 k)) v := by
      simpa using hvMax
    have huBook : Book.Ch02.IsResponseMaximizer
        (Book.Ch02.cubeDomain Q) aBook p (-q) u := by
      apply Homogenization.Internal.Ch02.BookCh02.public_isResponseMaximizer_of_old
      exact hu'
    have hvBook : Book.Ch02.IsResponseMaximizer
        (Book.Ch02.cubeDomain Q) aBook.transpose p q v := by
      apply Homogenization.Internal.Ch02.BookCh02.public_isResponseMaximizer_of_old
      change IsResponseMaximizer (openCubeSet Q) p q
        (Homogenization.adjointCoeffField
          (responseFramePlanarCoefficientField ν 1 k)) v
      exact hv'
    have hformula :=
      (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative_characterization
        (Book.Ch02.cubeDomain Q) aBook (sensitivityMatrixDirection h)).2.1
        p q v u hvBook huBook
    simpa [aBook] using hformula

private theorem sensitivity_vectorWeakEnergy_congr_ae (Q : TriadicCube 2)
    {F G : Vec 2 → Fin 2 → ℝ}
    (hFG : F =ᵐ[volume.restrict (cubeSet Q)] G) :
    vectorWeakHaarEnergy Q F = vectorWeakHaarEnergy Q G := by
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  have hcoord : (fun x => F x i) =ᵐ[volume.restrict (cubeSet Q)]
      (fun x => G x i) := by
    filter_upwards [hFG] with x hx
    exact congrFun hx i
  unfold dualEnergy
  exact diagPrimalEnergy_congr_ae Q (Real.sqrt 3)⁻¹ hcoord

private theorem sensitivity_response_pair_haar_budget (Q : TriadicCube 2)
    (ν : ℝ) (hν : 0 < ν) (k : ResponseCoefficient (openCubeSet Q))
    (uExp : ℝ) (p q : Vec 2)
    (r : H10Function (openCubeSet Q))
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν 1 k)
      (openCubeSet Q))
    (v : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν 1 k))
      (openCubeSet Q))
    (hmid : (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q)
        (-p) r).grad =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2))
    (hbudget : vectorWeakHaarEnergy Q
        (fun x i => u.toH1.grad x i + v.toH1.grad x i) +
      vectorWeakHaarEnergy Q
        (fun x i => u.toH1.grad x i - v.toH1.grad x i) ≤
      4 * (Book.Ch02.lambdaSqFinite Q uExp 2
        (sensitivityCoefficientFamily ν hν k))⁻¹ *
        blockVecDot (p, q) (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
            (sensitivityBookCoeffOn Q ν hν k)) (p, q))) :
    vectorWeakHaarNorm Q
        (fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2) ^ 2 =
        vecNormSq p + vectorWeakHaarNorm Q
          (fun x i => r.toH1Function.grad x i) ^ 2 ∧
      vectorWeakHaarNorm Q
          (fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2) *
        vectorWeakHaarNorm Q
          (fun x i => u.toH1.grad x i - v.toH1.grad x i) ≤
        (Book.Ch02.lambdaSqFinite Q uExp 2
          (sensitivityCoefficientFamily ν hν k))⁻¹ *
          blockVecDot (p, q) (blockMatVecMul
            (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
              (sensitivityBookCoeffOn Q ν hν k)) (p, q)) := by
  let Gplus : Vec 2 → Fin 2 → ℝ := fun x i =>
    u.toH1.grad x i + v.toH1.grad x i
  let Gminus : Vec 2 → Fin 2 → ℝ := fun x i =>
    u.toH1.grad x i - v.toH1.grad x i
  let Ghalf : Vec 2 → Fin 2 → ℝ := fun x i =>
    (u.toH1.grad x i + v.toH1.grad x i) / 2
  let Ggrad : Vec 2 → Fin 2 → ℝ := fun x i => r.toH1Function.grad x i
  let K := (Book.Ch02.lambdaSqFinite Q uExp 2
      (sensitivityCoefficientFamily ν hν k))⁻¹ *
    blockVecDot (p, q) (blockMatVecMul
      (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q ν hν k)) (p, q))
  have huGrad (i : Fin 2) : MemLp (fun x => u.toH1.grad x i) 2
      (normalizedCubeMeasure Q) := u.toH1.grad_memL2_normalizedCubeMeasure i
  have hvGrad (i : Fin 2) : MemLp (fun x => v.toH1.grad x i) 2
      (normalizedCubeMeasure Q) := v.toH1.grad_memL2_normalizedCubeMeasure i
  have hplusLp (i : Fin 2) : MemLp (fun x => Gplus x i) 2
      (normalizedCubeMeasure Q) := (huGrad i).add (hvGrad i)
  have hminusLp (i : Fin 2) : MemLp (fun x => Gminus x i) 2
      (normalizedCubeMeasure Q) := (huGrad i).sub (hvGrad i)
  have hhalfFun : Ghalf = fun x i => (1 / 2 : ℝ) * Gplus x i := by
    funext x i
    dsimp [Ghalf, Gplus]
    ring
  have hscale := sensitivity_vectorWeakEnergy_smul Q Gplus hplusLp (1 / 2 : ℝ)
  have hhalfEnergy : vectorWeakHaarEnergy Q Ghalf =
      (1 / 2 : ℝ) ^ 2 * vectorWeakHaarEnergy Q Gplus := by
    rw [hhalfFun]
    exact hscale
  have hres := sensitivity_halfPair_residual_ae Q p r u.toH1 v.toH1 hmid
  have hhalfAE : Ghalf =ᵐ[volume.restrict (cubeSet Q)]
      (fun x i => Ggrad x i - p i) := by
    filter_upwards [hres] with x hx
    funext i
    have hi := congrFun hx i
    dsimp [Ghalf, Ggrad] at hi ⊢
    linarith
  have hEnergyAE := sensitivity_vectorWeakEnergy_congr_ae Q hhalfAE
  have hgradMean (i : Fin 2) : cubeAverage Q (fun x => Ggrad x i) = 0 := by
    dsimp [Ggrad]
    exact cubeAverage_h10_gradient_eq_zero Q r i
  have hconst := sensitivity_vectorWeakEnergy_sub_const_meanZero Q Ggrad p
    (fun i => r.toH1Function.grad_memL2_normalizedCubeMeasure i) hgradMean
  have hsumP : (∑ i : Fin 2, (p i) ^ 2) = vecNormSq p := by
    simp [vecNormSq, vecDot]
    ring
  have hhalfEnergyExact : vectorWeakHaarEnergy Q Ghalf =
      vectorWeakHaarEnergy Q Ggrad + vecNormSq p := by
    calc
      vectorWeakHaarEnergy Q Ghalf =
          vectorWeakHaarEnergy Q (fun x i => Ggrad x i - p i) := hEnergyAE
      _ = vectorWeakHaarEnergy Q Ggrad + ∑ i, (p i) ^ 2 := hconst
      _ = vectorWeakHaarEnergy Q Ggrad + vecNormSq p := by rw [hsumP]
  have hZnorm : vectorWeakHaarNorm Q Ggrad ^ 2 =
      vectorWeakHaarEnergy Q Ggrad := by
    simp [vectorWeakHaarNorm, Real.sq_sqrt,
      vectorWeakHaarEnergy_nonneg]
  have hXnorm : vectorWeakHaarNorm Q Ghalf ^ 2 =
      vectorWeakHaarEnergy Q Ghalf := by
    simp [vectorWeakHaarNorm, Real.sq_sqrt,
      vectorWeakHaarEnergy_nonneg]
  have hYnorm : vectorWeakHaarNorm Q Gminus ^ 2 =
      vectorWeakHaarEnergy Q Gminus := by
    simp [vectorWeakHaarNorm, Real.sq_sqrt,
      vectorWeakHaarEnergy_nonneg]
  have hXsq : vectorWeakHaarNorm Q Ghalf ^ 2 =
      vecNormSq p + vectorWeakHaarNorm Q Ggrad ^ 2 := by
    rw [hXnorm, hhalfEnergyExact, ← hZnorm]
    ring
  have hplusEq : vectorWeakHaarEnergy Q Gplus =
      4 * vectorWeakHaarEnergy Q Ghalf := by
    nlinarith [hhalfEnergy]
  have hbudget' : vectorWeakHaarEnergy Q Gplus +
      vectorWeakHaarEnergy Q Gminus ≤ 4 * K := by
    simpa [Gplus, Gminus, K, mul_assoc] using hbudget
  have henergyBound : 4 * vectorWeakHaarNorm Q Ghalf ^ 2 +
      vectorWeakHaarNorm Q Gminus ^ 2 ≤ 4 * K := by
    calc
      _ = 4 * vectorWeakHaarEnergy Q Ghalf +
          vectorWeakHaarEnergy Q Gminus := by
        rw [hXnorm, hYnorm]
      _ = vectorWeakHaarEnergy Q Gplus + vectorWeakHaarEnergy Q Gminus := by
        rw [hplusEq]
      _ ≤ 4 * K := hbudget'
  constructor
  · exact hXsq
  · have hsq : 0 ≤ (2 * vectorWeakHaarNorm Q Ghalf -
        vectorWeakHaarNorm Q Gminus) ^ 2 := sq_nonneg _
    nlinarith [henergyBound, hsq]

private theorem sensitivity_block_lowerRight_quadratic (A : BlockMat 2)
    (q : Vec 2) :
    blockVecDot (0, q) (blockMatVecMul A (0, q)) =
      vecDot q (matVecMul A.lowerRight q) := by
  simp only [blockVecDot, blockMatVecMul, matVecMul_zero, zero_add,
    vecDot_zero_left]

/-- The gauge-invariant lower-right inverse-block derivative estimate. This
uses the `p = 0` response pair, so it requires no mean-zero hypothesis on H. -/
theorem sensitivity_coarse_derivative_inverseBlock_bound (Q : TriadicCube 2)
    (ν : ℝ) (hν : 0 < ν) (k : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (uExp : ℝ) (hu : 0 < uExp) (hu4 : uExp ≤ 1 / 4) (q : Vec 2) :
    |vecDot q (matVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q ν hν k)
          (sensitivityMatrixDirection h)).lowerRight q)| ≤
      sensitivityB2 * sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q uExp 2
          (sensitivityCoefficientFamily ν hν k))⁻¹ *
        vecDot q (matVecMul
          (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
            (sensitivityBookCoeffOn Q ν hν k)).lowerRight q) := by
  obtain ⟨r, u, v, huMax, hvMax, hmid, hbudget, hderiv⟩ :=
    sensitivity_response_pair_derivative_budget Q ν hν k h uExp hu hu4 0 q
  let Gminus : Vec 2 → Fin 2 → ℝ := fun x i => u.toH1.grad x i - v.toH1.grad x i
  let F1 : Vec 2 → Fin 2 → ℝ := fun x i =>
    planarJGradient h x i * r.toH1Function.toFun x
  let b := sensitivityJGradientW1 h
  have hGm (i : Fin 2) : MemLp (fun x => Gminus x i) 2
      (normalizedCubeMeasure Q) :=
    (u.toH1.grad_memL2_normalizedCubeMeasure i).sub
      (v.toH1.grad_memL2_normalizedCubeMeasure i)
  have hF1 (i : Fin 2) : MemLp (fun x => F1 x i) 2
      (normalizedCubeMeasure Q) := by
    have hb : MemLp (fun x => planarW1Value b x i) ⊤
        (normalizedCubeMeasure Q) := by
      simpa [b, planarW1Value] using b.component_memLp_top i
    have hr : MemLp r.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
      r.toH1Function.memL2_normalizedCubeMeasure
    have hm : MemLp (fun x => r.toH1Function.toFun x *
        planarW1Value b x i) 2 (normalizedCubeMeasure Q) := hr.mul hb
    simpa [F1, b, sensitivityJGradientW1_value, mul_comm] using hm
  have hM : 0 ≤ planarW1ValueLInf b := by
    rw [sensitivityJGradientW1_valueLInf]
    unfold planarGradientLInf planarW1ValueLInf
    positivity
  have hD : 0 ≤ planarW1DerivativeFrobeniusLInf b := by
    rw [sensitivityJGradientW1_derivativeLInf]
    unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
    positivity
  have hmul := vectorPositiveHaarNorm_mul_of_caps Q b r.toH1Function
    hM hD (ae_planarW1Value_le_linf b) (ae_planarW1Derivative_le_linf b)
  have hF1pos (i : Fin 2) : Summable (fun n : ℕ => (Real.sqrt 3) ^ (n + 1) *
      energy Q (cubeIncrement Q (n + 1) (fun x => F1 x i))) := by
    have hbvalue : planarW1Value b = planarJGradient h := by
      simpa [b] using sensitivityJGradientW1_value h
    have hpos := hmul.1 i
    rw [hbvalue] at hpos
    simpa [F1] using hpos
  have hsplit := sensitivity_derivative_pairing_split Q h 0 r u.toH1 v.toH1
    (fun i => u.toH1.grad_memL2_normalizedCubeMeasure i)
    (fun i => v.toH1.grad_memL2_normalizedCubeMeasure i) hmid
  have hzeroF0 : (fun x i => h.value.toFun x *
      matVecMul responsePlanarJ (0 : Vec 2) i) = fun _ _ => 0 := by
    funext x i
    simp [matVecMul, responsePlanarJ]
  have hzeroPair : vectorPairing Q
      (fun x i => h.value.toFun x * matVecMul responsePlanarJ (0 : Vec 2) i)
      Gminus = 0 := by
    rw [hzeroF0]
    simp [vectorPairing, pairing, cubeAverage_const]
  have hsplit1 : Book.Ch02.average (Book.Ch02.cubeDomain Q) (fun x =>
      vecDot (v.toH1.grad x)
        (matVecMul ((sensitivityMatrixDirection h).1 x) (u.toH1.grad x))) =
      vectorPairing Q F1 Gminus := by
    calc
      _ = vectorPairing Q (fun x i => h.value.toFun x *
            matVecMul responsePlanarJ (0 : Vec 2) i) Gminus +
          vectorPairing Q F1 Gminus := hsplit
      _ = vectorPairing Q F1 Gminus := by rw [hzeroPair]; ring
  have hpair1 := abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
    Q hF1 hGm hF1pos
  have hnorm1 := sensitivity_product_poincare Q r h
  let X := vectorWeakHaarNorm Q
    (fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2)
  let Z := vectorWeakHaarNorm Q (fun x i => r.toH1Function.grad x i)
  let Y := vectorWeakHaarNorm Q Gminus
  have hhaar := sensitivity_response_pair_haar_budget Q ν hν k uExp 0 q
    r u v hmid hbudget
  have hXsq : X ^ 2 = Z ^ 2 := by
    simpa [X, Z, vecNormSq, vecDot] using hhaar.1
  have hXnonneg : 0 ≤ X := Real.sqrt_nonneg _
  have hZnonneg : 0 ≤ Z := Real.sqrt_nonneg _
  have hYnonneg : 0 ≤ Y := Real.sqrt_nonneg _
  have hXeqZ : X = Z := by nlinarith [hXsq]
  have hXY : Z * Y ≤
      (Book.Ch02.lambdaSqFinite Q uExp 2
        (sensitivityCoefficientFamily ν hν k))⁻¹ *
        blockVecDot (0, q) (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
            (sensitivityBookCoeffOn Q ν hν k)) (0, q)) := by
    simpa [X, Y, hXeqZ] using hhaar.2
  have hc0 : 0 ≤ planarC0 := by unfold planarC0; positivity
  have hB2 : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
  have hgrad : 0 ≤ planarGradientLInf h := by
    unfold planarGradientLInf planarW1ValueLInf
    positivity
  have hhess : 0 ≤ planarHessianFrobeniusLInf h := by
    unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
    positivity
  have hD1 : 0 ≤ sensitivityD1 Q h := by
    unfold sensitivityD1
    exact mul_nonneg
      (mul_nonneg (cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)) hgrad
  have hD2 : 0 ≤ sensitivityD2 Q h := by
    unfold sensitivityD2
    exact mul_nonneg
      (mul_nonneg (sq_nonneg (cubeScaleFactor Q)) (Real.sqrt_nonneg _)) hhess
  have hKappa : 0 ≤ sensitivityKappaH := by
    unfold sensitivityKappaH planarC0 planarC1
    positivity
  have hDsharp : 0 ≤ sensitivityDsharp Q h := by
    unfold sensitivityDsharp
    exact add_nonneg hD1 (mul_nonneg hKappa hD2)
  have hpairBound : |vectorPairing Q F1 Gminus| ≤
      (sensitivityB2 * sensitivityDsharp Q h) * (Z * Y) := by
    calc
      _ ≤ vectorPositiveHaarNorm Q F1 * Y := hpair1
      _ ≤ (sensitivityB2 * sensitivityDsharp Q h * Z) * Y :=
        mul_le_mul_of_nonneg_right hnorm1 hYnonneg
      _ = (sensitivityB2 * sensitivityDsharp Q h) * (Z * Y) := by ring
  let D := Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
    (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q ν hν k)
    (sensitivityMatrixDirection h)
  let A := Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
    (sensitivityBookCoeffOn Q ν hν k)
  have hDerivativeLower : vecDot q (matVecMul D.lowerRight q) =
      Book.Ch02.average (Book.Ch02.cubeDomain Q) (fun x =>
        vecDot (v.toH1.grad x)
          (matVecMul ((sensitivityMatrixDirection h).1 x) (u.toH1.grad x))) := by
    calc
      _ = blockVecDot (0, q) (blockMatVecMul D (0, q)) :=
        (sensitivity_block_lowerRight_quadratic D q).symm
      _ = _ := by simpa [D] using hderiv
  have hCoarseLower : blockVecDot (0, q) (blockMatVecMul A (0, q)) =
      vecDot q (matVecMul A.lowerRight q) :=
    sensitivity_block_lowerRight_quadratic A q
  have hXY' : Z * Y ≤
      (Book.Ch02.lambdaSqFinite Q uExp 2
        (sensitivityCoefficientFamily ν hν k))⁻¹ *
        vecDot q (matVecMul A.lowerRight q) := by
    rw [hCoarseLower] at hXY
    exact hXY
  calc
    _ = |Book.Ch02.average (Book.Ch02.cubeDomain Q) (fun x =>
        vecDot (v.toH1.grad x)
          (matVecMul ((sensitivityMatrixDirection h).1 x) (u.toH1.grad x)))| := by
      rw [hDerivativeLower]
    _ = |vectorPairing Q F1 Gminus| := by rw [hsplit1]
    _ ≤ (sensitivityB2 * sensitivityDsharp Q h) * (Z * Y) := hpairBound
    _ ≤ (sensitivityB2 * sensitivityDsharp Q h) *
        ((Book.Ch02.lambdaSqFinite Q uExp 2
          (sensitivityCoefficientFamily ν hν k))⁻¹ *
          vecDot q (matVecMul A.lowerRight q)) := by
      exact mul_le_mul_of_nonneg_left hXY'
        (mul_nonneg hB2 hDsharp)
    _ = _ := by ring

/-- The mean-zero polarized first-variation estimate, with the required
cube-mean normalization on the skew direction. -/
theorem sensitivity_coarse_derivative_A_bound (Q : TriadicCube 2)
    (ν : ℝ) (hν : 0 < ν) (k : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q) (hmean : cubeAverage Q h.value.toFun = 0)
    (uExp : ℝ) (hu : 0 < uExp) (hu4 : uExp ≤ 1 / 4) (p q : Vec 2) :
    |blockVecDot (p, q) (blockMatVecMul
        (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
          (Book.Ch02.cubeDomain Q) (sensitivityBookCoeffOn Q ν hν k)
          (sensitivityMatrixDirection h)) (p, q))| ≤
      sensitivityA2 * sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q uExp 2
          (sensitivityCoefficientFamily ν hν k))⁻¹ *
        blockVecDot (p, q) (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
            (sensitivityBookCoeffOn Q ν hν k)) (p, q)) := by
  obtain ⟨r, u, v, huMax, hvMax, hmid, hbudget, hderiv⟩ :=
    sensitivity_response_pair_derivative_budget Q ν hν k h uExp hu hu4 p q
  let Gminus : Vec 2 → Fin 2 → ℝ := fun x i => u.toH1.grad x i - v.toH1.grad x i
  let F0 : Vec 2 → Fin 2 → ℝ := fun x i =>
    h.value.toFun x * matVecMul responsePlanarJ p i
  let F1 : Vec 2 → Fin 2 → ℝ := fun x i =>
    planarJGradient h x i * r.toH1Function.toFun x
  let b := sensitivityJGradientW1 h
  have hGm (i : Fin 2) : MemLp (fun x => Gminus x i) 2
      (normalizedCubeMeasure Q) :=
    (u.toH1.grad_memL2_normalizedCubeMeasure i).sub
      (v.toH1.grad_memL2_normalizedCubeMeasure i)
  have hF0 (i : Fin 2) : MemLp (fun x => F0 x i) 2
      (normalizedCubeMeasure Q) := by
    simpa [F0, mul_comm] using
      (h.value.memL2_normalizedCubeMeasure.const_mul
        (matVecMul responsePlanarJ p i))
  have hF0pos (i : Fin 2) : Summable (fun n : ℕ => (Real.sqrt 3) ^ (n + 1) *
      energy Q (cubeIncrement Q (n + 1) (fun x =>
        h.value.toFun x * matVecMul responsePlanarJ p i))) :=
    sensitivity_constantMode_increment_summable Q h
      (matVecMul responsePlanarJ p i)
  have hF1 (i : Fin 2) : MemLp (fun x => F1 x i) 2
      (normalizedCubeMeasure Q) := by
    have hb : MemLp (fun x => planarW1Value b x i) ⊤
        (normalizedCubeMeasure Q) := by
      simpa [b, planarW1Value] using b.component_memLp_top i
    have hr : MemLp r.toH1Function.toFun 2 (normalizedCubeMeasure Q) :=
      r.toH1Function.memL2_normalizedCubeMeasure
    have hm : MemLp (fun x => r.toH1Function.toFun x *
        planarW1Value b x i) 2 (normalizedCubeMeasure Q) := hr.mul hb
    simpa [F1, b, sensitivityJGradientW1_value, mul_comm] using hm
  have hM : 0 ≤ planarW1ValueLInf b := by
    rw [sensitivityJGradientW1_valueLInf]
    unfold planarGradientLInf planarW1ValueLInf
    positivity
  have hD : 0 ≤ planarW1DerivativeFrobeniusLInf b := by
    rw [sensitivityJGradientW1_derivativeLInf]
    unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
    positivity
  have hmul := vectorPositiveHaarNorm_mul_of_caps Q b r.toH1Function
    hM hD (ae_planarW1Value_le_linf b) (ae_planarW1Derivative_le_linf b)
  have hF1pos (i : Fin 2) : Summable (fun n : ℕ => (Real.sqrt 3) ^ (n + 1) *
      energy Q (cubeIncrement Q (n + 1) (fun x => F1 x i))) := by
    have hbvalue : planarW1Value b = planarJGradient h := by
      simpa [b] using sensitivityJGradientW1_value h
    have hpos := hmul.1 i
    rw [hbvalue] at hpos
    simpa [F1] using hpos
  have hsplit := sensitivity_derivative_pairing_split Q h p r u.toH1 v.toH1
    (fun i => u.toH1.grad_memL2_normalizedCubeMeasure i)
    (fun i => v.toH1.grad_memL2_normalizedCubeMeasure i) hmid
  have hpair0 := abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
    Q hF0 hGm hF0pos
  have hpair1 := abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
    Q hF1 hGm hF1pos
  have hnorm0 := sensitivity_constantMode_positive_bound Q h hmean p
  have hnorm1 := sensitivity_product_poincare Q r h
  let Pmag := Real.sqrt (vecNormSq p)
  let Z := vectorWeakHaarNorm Q (fun x i => r.toH1Function.grad x i)
  let X := vectorWeakHaarNorm Q
    (fun x i => (u.toH1.grad x i + v.toH1.grad x i) / 2)
  let Y := vectorWeakHaarNorm Q Gminus
  have hhaar := sensitivity_response_pair_haar_budget Q ν hν k uExp p q
    r u v hmid hbudget
  have hXsq : X ^ 2 = vecNormSq p + Z ^ 2 := by
    simpa [X, Z] using hhaar.1
  have hXY : X * Y ≤
      (Book.Ch02.lambdaSqFinite Q uExp 2
        (sensitivityCoefficientFamily ν hν k))⁻¹ *
        blockVecDot (p, q) (blockMatVecMul
          (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
            (sensitivityBookCoeffOn Q ν hν k)) (p, q)) := by
    simpa [X, Y] using hhaar.2
  have hPmag : 0 ≤ Pmag := Real.sqrt_nonneg _
  have hZnonneg : 0 ≤ Z := Real.sqrt_nonneg _
  have hYnonneg : 0 ≤ Y := Real.sqrt_nonneg _
  have hXnonneg : 0 ≤ X := Real.sqrt_nonneg _
  have hc0 : 0 ≤ planarC0 := by unfold planarC0; positivity
  have hB2 : 0 ≤ sensitivityB2 := by unfold sensitivityB2; positivity
  have hgrad : 0 ≤ planarGradientLInf h := by
    unfold planarGradientLInf planarW1ValueLInf
    positivity
  have hhess : 0 ≤ planarHessianFrobeniusLInf h := by
    unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
    positivity
  have hD1 : 0 ≤ sensitivityD1 Q h := by
    unfold sensitivityD1
    exact mul_nonneg
      (mul_nonneg (cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)) hgrad
  have hD2 : 0 ≤ sensitivityD2 Q h := by
    unfold sensitivityD2
    exact mul_nonneg
      (mul_nonneg (sq_nonneg (cubeScaleFactor Q)) (Real.sqrt_nonneg _)) hhess
  have hKappa : 0 ≤ sensitivityKappaH := by
    unfold sensitivityKappaH planarC0 planarC1
    positivity
  have hDsharp : 0 ≤ sensitivityDsharp Q h := by
    unfold sensitivityDsharp
    exact add_nonneg hD1 (mul_nonneg hKappa hD2)
  have hD1le : sensitivityD1 Q h ≤ sensitivityDsharp Q h := by
    unfold sensitivityDsharp
    nlinarith [mul_nonneg hKappa hD2]
  have hPmagSq : Pmag ^ 2 = vecNormSq p := by
    dsimp [Pmag]
    exact Real.sq_sqrt (vecNormSq_nonneg p)
  have hA2nonneg : 0 ≤ sensitivityA2 := by
    unfold sensitivityA2
    exact Real.sqrt_nonneg _
  have hA2sq : sensitivityA2 ^ 2 = planarC0 ^ 2 + sensitivityB2 ^ 2 := by
    unfold sensitivityA2
    exact Real.sq_sqrt (add_nonneg (sq_nonneg planarC0) (sq_nonneg sensitivityB2))
  have hCSsq : (planarC0 * Pmag + sensitivityB2 * Z) ^ 2 ≤
      (sensitivityA2 * X) ^ 2 := by
    rw [mul_pow, hA2sq, hXsq]
    nlinarith [hPmagSq,
      sq_nonneg (planarC0 * Z - sensitivityB2 * Pmag)]
  have hCS : planarC0 * Pmag + sensitivityB2 * Z ≤ sensitivityA2 * X :=
    (sq_le_sq₀ (add_nonneg (mul_nonneg hc0 hPmag)
      (mul_nonneg hB2 hZnonneg))
      (mul_nonneg hA2nonneg hXnonneg)).1 hCSsq
  have hD1term : planarC0 * sensitivityD1 Q h * Pmag ≤
      planarC0 * sensitivityDsharp Q h * Pmag := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hD1le hc0) hPmag
  have hsumNorm : vectorPositiveHaarNorm Q F0 +
      vectorPositiveHaarNorm Q F1 ≤ sensitivityA2 * sensitivityDsharp Q h * X := by
    calc
      _ ≤ planarC0 * sensitivityD1 Q h * Pmag +
          sensitivityB2 * sensitivityDsharp Q h * Z := add_le_add hnorm0 hnorm1
      _ ≤ sensitivityDsharp Q h *
          (planarC0 * Pmag + sensitivityB2 * Z) := by
        calc
          _ ≤ planarC0 * sensitivityDsharp Q h * Pmag +
              sensitivityB2 * sensitivityDsharp Q h * Z :=
            add_le_add hD1term le_rfl
          _ = _ := by ring
      _ ≤ sensitivityDsharp Q h * (sensitivityA2 * X) :=
        mul_le_mul_of_nonneg_left hCS hDsharp
      _ = sensitivityA2 * sensitivityDsharp Q h * X := by ring
  have hpairSum : |vectorPairing Q F0 Gminus + vectorPairing Q F1 Gminus| ≤
      (sensitivityA2 * sensitivityDsharp Q h) * (X * Y) := by
    calc
      _ ≤ |vectorPairing Q F0 Gminus| + |vectorPairing Q F1 Gminus| :=
        abs_add_le _ _
      _ ≤ vectorPositiveHaarNorm Q F0 * Y +
          vectorPositiveHaarNorm Q F1 * Y := add_le_add hpair0 hpair1
      _ = (vectorPositiveHaarNorm Q F0 + vectorPositiveHaarNorm Q F1) * Y := by ring
      _ ≤ (sensitivityA2 * sensitivityDsharp Q h * X) * Y :=
        mul_le_mul_of_nonneg_right hsumNorm hYnonneg
      _ = (sensitivityA2 * sensitivityDsharp Q h) * (X * Y) := by ring
  calc
    _ = |vectorPairing Q F0 Gminus + vectorPairing Q F1 Gminus| := by
      rw [hderiv, hsplit]
    _ ≤ (sensitivityA2 * sensitivityDsharp Q h) * (X * Y) := by
      simpa [mul_assoc] using hpairSum
    _ ≤ sensitivityA2 * sensitivityDsharp Q h *
        ((Book.Ch02.lambdaSqFinite Q uExp 2
          (sensitivityCoefficientFamily ν hν k))⁻¹ *
          blockVecDot (p, q) (blockMatVecMul
            (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
              (sensitivityBookCoeffOn Q ν hν k)) (p, q))) :=
      mul_le_mul_of_nonneg_left hXY
        (mul_nonneg hA2nonneg hDsharp)
    _ = _ := by ring

end

end ASDExplicitGamma.Triadic
