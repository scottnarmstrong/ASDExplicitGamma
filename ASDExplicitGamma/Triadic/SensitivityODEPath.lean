module

public import ASDExplicitGamma.Triadic.SensitivityPathCoefficient
public import ASDExplicitGamma.Triadic.SensitivityLambda
public import ASDExplicitGamma.Triadic.SensitivityDescendantBounds
public import Algsuperdiff.Section24.Sensitivity.Provider.Multiscale.DescendantRatio
public import Algsuperdiff.Section24.Sensitivity.Provider.Response.PathDerivative
public import Algsuperdiff.Section24.Sensitivity.Provider.Lambda.CubeRatio

/-! Coefficient-family bookkeeping for the coarse-sensitivity path. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory ASDExplicitGamma.Response
open Homogenization.Book.Ch02 Homogenization.Book.Ch04
open Algsuperdiff.Frozen.Section24

noncomputable section

/-- The canonical derivative matrix is unchanged by modifying a coefficient
representative on a null set. -/
theorem sensitivity_coarseMatrixDerivative_eq_of_aeeq
    {U : Book.Ch02.Domain 2} (a b : Book.Ch02.CoeffOn U)
    (hab : Book.Ch02.CoeffOn.AEEq a b)
    (g : Algsuperdiff.Frozen.Section24.LInfMatrixFieldOn U) :
    Algsuperdiff.Frozen.Section24.coarseMatrixDerivative U a g =
      Algsuperdiff.Frozen.Section24.coarseMatrixDerivative U b g := by
  have hba := Book.Ch02.CoeffOn.AEEq.transpose hab
  have hcharA := Algsuperdiff.Frozen.Section24.coarseMatrixDerivative_characterization U a g
  have hcharB := Algsuperdiff.Frozen.Section24.coarseMatrixDerivative_characterization U b g
  apply hcharB.2.2 _ hcharA.1
  intro p q vAdj v hvAdj hv
  let vAdjA : Book.Ch02.Solution U a.transpose :=
    Book.Ch02.Solution.ofAEEq hba.symm vAdj
  let vA : Book.Ch02.Solution U a :=
    Book.Ch02.Solution.ofAEEq hab.symm v
  have hvAdjA : Book.Ch02.IsResponseMaximizer U a.transpose p q vAdjA :=
    hvAdj.ofAEEq hba.symm
  have hvA : Book.Ch02.IsResponseMaximizer U a p (-q) vA :=
    hv.ofAEEq hab.symm
  have hform := hcharA.2.1 p q vAdjA vA hvAdjA hvA
  simpa [vAdjA, vA] using hform

/-- The elliptic Chapter 2 family associated with the actual bounded-continuous
coefficient at path time `t`. -/
def sensitivityPathFamily {Q : TriadicCube 2} (ν : ℝ) (hν : 0 < ν)
    (k kH : ResponseCoefficient (openCubeSet Q)) (t : ℝ) :
    TriadicCoeffFamily 2 :=
  sensitivityCoefficientFamily ν hν (sensitivityResponseCoefficientPath k kH t)

/-- Restricting a coefficient path to a descendant commutes with forming the
bounded-continuous affine path. -/
theorem sensitivityResponseCoefficientRestrict_path
    {Q R : TriadicCube 2} {j : ℕ}
    (k kH : ResponseCoefficient (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) (t : ℝ) :
    sensitivityResponseCoefficientRestrict
        (sensitivityResponseCoefficientPath k kH t) hR =
      sensitivityResponseCoefficientPath
        (sensitivityResponseCoefficientRestrict k hR)
        (sensitivityResponseCoefficientRestrict kH hR) t := by
  ext x
  simp [sensitivityResponseCoefficientPath, sensitivityResponseCoefficientRestrict,
    BoundedContinuousFunction.compContinuous_apply]

/-- The restricted bounded-continuous representative still represents the
restricted Sobolev direction. -/
theorem sensitivityResponseCoefficientRestrict_represents
    {Q R : TriadicCube 2} {j : ℕ}
    (kH : ResponseCoefficient (openCubeSet Q)) (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    (hR : R ∈ descendantsAtDepth Q j) :
    responseCoefficientExtension (sensitivityResponseCoefficientRestrict kH hR) =ᵐ[
      volume.restrict (openCubeSet R)] (h.restrict hR).value.toFun := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hkHchild := ae_restrict_of_ae_restrict_of_subset hsub hkH
  have hrestrict := sensitivityResponseCoefficientRestrict_extension_ae kH hR
  filter_upwards [hrestrict, hkHchild] with x hxrep hxvalue
  rw [hxrep]
  simpa [PlanarW2Infinity.restrict] using hxvalue

/-- At any descendant, the root family coefficient agrees with the actual
restricted response coefficient. -/
theorem sensitivityPathFamily_descendant_coeffOn_aeeq
    {Q R : TriadicCube 2} {j : ℕ}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q j) (t : ℝ) :
    Book.Ch02.CoeffOn.AEEq
      ((sensitivityPathFamily ν hν k kH t).coeffOn R)
      (sensitivityBookCoeffOn R ν hν
        (sensitivityResponseCoefficientPath
          (sensitivityResponseCoefficientRestrict k hR)
          (sensitivityResponseCoefficientRestrict kH hR) t)) := by
  have hext := sensitivityResponseCoefficientRestrict_extension_ae
    (sensitivityResponseCoefficientPath k kH t) hR
  rw [sensitivityResponseCoefficientRestrict_path k kH hR t] at hext
  change responseFramePlanarCoefficientField ν 1
      (sensitivityResponseCoefficientPath k kH t) =ᵐ[
        volumeMeasureOn (openCubeSet R)]
    responseFramePlanarCoefficientField ν 1
      (sensitivityResponseCoefficientPath
        (sensitivityResponseCoefficientRestrict k hR)
        (sensitivityResponseCoefficientRestrict kH hR) t)
  filter_upwards [hext] with x hx
  rw [responseFramePlanarCoefficientField_apply,
    responseFramePlanarCoefficientField_apply, hx]

/-- The response on each restricted affine coefficient path is differentiable;
the derivative matrix is evaluated at that same path coefficient. -/
theorem sensitivity_descendant_responseJ_hasDerivAt
    {Q R : TriadicCube 2} {j : ℕ}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q)
    (hkH : responseCoefficientExtension kH =ᵐ[
      volume.restrict (openCubeSet Q)] h.value.toFun)
    (hR : R ∈ descendantsAtDepth Q j) (q : Vec 2) (t : ℝ) :
    HasDerivAt
      (fun τ => responseJ (Book.Ch02.cubeDomain R)
        (sensitivityBookCoeffOn R ν hν
          (sensitivityResponseCoefficientPath
            (sensitivityResponseCoefficientRestrict k hR)
            (sensitivityResponseCoefficientRestrict kH hR) τ)) 0 q)
      ((1 / 2 : ℝ) * blockVecDot (0, -q)
        (blockMatVecMul
          (Algsuperdiff.Frozen.Section24.coarseMatrixDerivative
            (Book.Ch02.cubeDomain R)
            (sensitivityBookCoeffOn R ν hν
              (sensitivityResponseCoefficientPath
                (sensitivityResponseCoefficientRestrict k hR)
                (sensitivityResponseCoefficientRestrict kH hR) t))
            (sensitivitySkewMatrixDirection (h.restrict hR)).1) (0, -q))) t := by
  let kR := sensitivityResponseCoefficientRestrict k hR
  let kHR := sensitivityResponseCoefficientRestrict kH hR
  let hlocal := h.restrict hR
  have hkHR : responseCoefficientExtension kHR =ᵐ[
      volume.restrict (openCubeSet R)] hlocal.value.toFun := by
    simpa [kHR, hlocal] using
      sensitivityResponseCoefficientRestrict_represents kH h hkH hR
  let g := sensitivitySkewMatrixDirection hlocal
  have hpath (τ : ℝ) : Book.Ch02.CoeffOn.AEEq
      (sensitivityBookCoeffOn R ν hν (sensitivityResponseCoefficientPath kR kHR τ))
      (Algsuperdiff.Frozen.Section24.perturbCoeffOn
        (Book.Ch02.cubeDomain R) (sensitivityBookCoeffOn R ν hν kR) g τ) := by
    exact sensitivityBookCoeffOn_path_aeeq R ν hν kR hlocal kHR hkHR τ
  have hfun :
      (fun τ => responseJ (Book.Ch02.cubeDomain R)
        (sensitivityBookCoeffOn R ν hν (sensitivityResponseCoefficientPath kR kHR τ)) 0 q) =
      (fun τ => responseJ (Book.Ch02.cubeDomain R)
        (Algsuperdiff.Frozen.Section24.perturbCoeffOn
          (Book.Ch02.cubeDomain R) (sensitivityBookCoeffOn R ν hν kR) g τ) 0 q) := by
    funext τ
    exact Book.Ch02.responseJ_eq_ofAEEq (hpath τ) 0 q
  have hderiv :=
    Algsuperdiff.Section24.Sensitivity.Provider.Response.hasDerivAt_responseJ_perturbCoeffOn_pair
      (by norm_num : 2 ≤ 2) (Book.Ch02.cubeDomain R)
      (sensitivityBookCoeffOn R ν hν kR) g 0 q t
  rw [← hfun] at hderiv
  have hD := sensitivity_coarseMatrixDerivative_eq_of_aeeq
    (sensitivityBookCoeffOn R ν hν (sensitivityResponseCoefficientPath kR kHR t))
    (Algsuperdiff.Frozen.Section24.perturbCoeffOn
      (Book.Ch02.cubeDomain R) (sensitivityBookCoeffOn R ν hν kR) g t)
    (hpath t) g.1
  rw [← hD] at hderiv
  exact hderiv

/-- A finite lambda history depends only on the coefficient representatives on
the descendants of its root cube. -/
theorem sensitivity_lambdaSqFinite_eq_of_descendant_aeeq
    {Q : TriadicCube 2} {F G : TriadicCoeffFamily 2} {u : ℝ}
    (hFG : ∀ (j : ℕ) (R : TriadicCube 2), R ∈ descendantsAtDepth Q j →
      Book.Ch02.CoeffOn.AEEq (F.coeffOn R) (G.coeffOn R)) :
    Book.Ch02.lambdaSqFinite Q u 2 F = Book.Ch02.lambdaSqFinite Q u 2 G := by
  have hmax (j : ℕ) :
      Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (j : ℤ)) F =
        Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (j : ℤ)) G := by
    unfold Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    have hk : Q.scale - (j : ℤ) ≤ Q.scale := by omega
    have hdepth : R ∈ descendantsAtDepth Q j := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
      simpa using hR
    unfold Book.Ch02.coarseSigmaStarInvMatrixNorm
    rw [Homogenization.Book.Ch02.sigmaStarInvCoarse_eq_ofAEEq (hFG j R hdepth)]
  unfold Book.Ch02.lambdaSqFinite
  simp only [show (2 : ℝ) / 2 = 1 by norm_num]
  congr 1
  apply tsum_congr
  intro j
  rw [hmax j]

/-- The root and restricted coefficient families have the same lambda history
when the latter history is based at a descendant cube. -/
theorem sensitivityPathFamily_descendant_lambda_eq
    {Q R : TriadicCube 2} {d : ℕ}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (hR : R ∈ descendantsAtDepth Q d) (u t : ℝ) :
    Book.Ch02.lambdaSqFinite R u 2
        (sensitivityPathFamily ν hν
          (sensitivityResponseCoefficientRestrict k hR)
          (sensitivityResponseCoefficientRestrict kH hR) t) =
      Book.Ch02.lambdaSqFinite R u 2
        (sensitivityPathFamily ν hν k kH t) := by
  apply sensitivity_lambdaSqFinite_eq_of_descendant_aeeq
  intro j S hS
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hS
  have hext := sensitivityResponseCoefficientRestrict_extension_ae
    (sensitivityResponseCoefficientPath k kH t) hR
  rw [sensitivityResponseCoefficientRestrict_path k kH hR t] at hext
  have hextS : responseCoefficientExtension
      (sensitivityResponseCoefficientPath
        (sensitivityResponseCoefficientRestrict k hR)
        (sensitivityResponseCoefficientRestrict kH hR) t) =ᵐ[
          volume.restrict (openCubeSet S)]
      responseCoefficientExtension (sensitivityResponseCoefficientPath k kH t) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hext
  change responseFramePlanarCoefficientField ν 1
      (sensitivityResponseCoefficientPath
        (sensitivityResponseCoefficientRestrict k hR)
        (sensitivityResponseCoefficientRestrict kH hR) t) =ᵐ[
          volumeMeasureOn (openCubeSet S)]
    responseFramePlanarCoefficientField ν 1
      (sensitivityResponseCoefficientPath k kH t)
  filter_upwards [hextS] with x hx
  rw [responseFramePlanarCoefficientField_apply,
    responseFramePlanarCoefficientField_apply, hx]

/-- The source descendant scale factor cancels the sensitivity loss whenever
`0 < u ≤ 1/4`. -/
theorem sensitivity_descendant_weight_cancel (Q : TriadicCube 2) (j : ℕ)
    {u : ℝ} (hu4 : u ≤ 1 / 4) :
    (3 : ℝ) ^ (-(j : ℤ)) *
        Book.Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) u ≤ 1 := by
  have hweight : Book.Ch02.multiscaleDescendantWeight Q
      (Q.scale - (j : ℤ)) u = Real.rpow (3 : ℝ) (2 * u * (j : ℝ)) := by
    unfold Book.Ch02.multiscaleDescendantWeight
    congr 1
    push_cast
    ring
  have hzpow : (3 : ℝ) ^ (-(j : ℤ)) = Real.rpow (3 : ℝ) (-(j : ℝ)) := by
    rw [← Real.rpow_intCast]
    congr 1
    simp
  rw [hweight, hzpow]
  change Real.rpow (3 : ℝ) (-(j : ℝ)) *
      Real.rpow (3 : ℝ) (2 * u * (j : ℝ)) ≤ 1
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hu2 : 2 * u ≤ (1 / 2 : ℝ) := by nlinarith [hu4]
  have hmul : 2 * u * (j : ℝ) ≤ (1 / 2 : ℝ) * (j : ℝ) :=
    mul_le_mul_of_nonneg_right hu2 hj
  linarith

/-- After restriction, the product of the sensitivity size and the local
inverse-lambda is controlled by the root inverse-lambda, uniformly in depth. -/
theorem sensitivityDsharp_mul_descendant_lambda_inv_le
    {Q R : TriadicCube 2} {j : ℕ}
    (ν : ℝ) (hν : 0 < ν) (k kH : ResponseCoefficient (openCubeSet Q))
    (h : PlanarW2Infinity Q) (hR : R ∈ descendantsAtDepth Q j)
    (u : ℝ) (hu : 0 < u) (hu4 : u ≤ 1 / 4) (t : ℝ) :
    sensitivityDsharp R (h.restrict hR) *
        (Book.Ch02.lambdaSqFinite R u 2
          (sensitivityCoefficientFamily ν hν
            (sensitivityResponseCoefficientPath
              (sensitivityResponseCoefficientRestrict k hR)
              (sensitivityResponseCoefficientRestrict kH hR) t)))⁻¹ ≤
      sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q u 2
          (sensitivityPathFamily ν hν k kH t))⁻¹ := by
  let F := sensitivityPathFamily ν hν k kH t
  have hk : Q.scale - (j : ℤ) ≤ Q.scale := by omega
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
    simpa using hR
  have hD := sensitivityDsharp_descendant_le h hR
  have hK : 0 ≤ sensitivityKappaH := by
    unfold sensitivityKappaH planarC0 planarC1
    positivity
  have hDroot : 0 ≤ sensitivityDsharp Q h := by
    unfold sensitivityDsharp sensitivityD1 sensitivityD2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le
        (Real.sqrt_nonneg _)) (by
          unfold planarGradientLInf planarW1ValueLInf
          exact ENNReal.toReal_nonneg))
      (mul_nonneg hK
        (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) (by
          unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
          exact ENNReal.toReal_nonneg)))
  have hDlocal : 0 ≤ sensitivityDsharp R (h.restrict hR) := by
    unfold sensitivityDsharp sensitivityD1 sensitivityD2
    exact add_nonneg
      (mul_nonneg (mul_nonneg (cubeScaleFactor_pos' R).le
        (Real.sqrt_nonneg _)) (by
          unfold planarGradientLInf planarW1ValueLInf
          exact ENNReal.toReal_nonneg))
      (mul_nonneg hK
        (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)) (by
          unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
          exact ENNReal.toReal_nonneg)))
  have hrootInv : 0 ≤ (Book.Ch02.lambdaSqFinite Q u 2 F)⁻¹ :=
    inv_nonneg.mpr (Book.Ch02.lambdaSq_finite_nonneg Q F hu (by norm_num))
  have hweight : 0 ≤
      Book.Ch02.multiscaleDescendantWeight Q (Q.scale - (j : ℤ)) u := by
    unfold Book.Ch02.multiscaleDescendantWeight
    exact Real.rpow_nonneg (by norm_num) _
  have hlocalEq := sensitivityPathFamily_descendant_lambda_eq
    ν hν k kH hR u t
  have hlocalEq' : Book.Ch02.lambdaSqFinite R u 2
      (sensitivityCoefficientFamily ν hν
        (sensitivityResponseCoefficientPath
          (sensitivityResponseCoefficientRestrict k hR)
          (sensitivityResponseCoefficientRestrict kH hR) t)) =
      Book.Ch02.lambdaSqFinite R u 2 F := hlocalEq
  have hloc := Book.Ch02.descendant_lambdaSq_finite_inv_le F hRscale hu
    (by norm_num : (1 : ℝ) ≤ 2)
  have hloc' :
      (Book.Ch02.lambdaSqFinite R u 2 F)⁻¹ ≤
        Book.Ch02.multiscaleDescendantWeight Q
          (Q.scale - (j : ℤ)) u * (Book.Ch02.lambdaSqFinite Q u 2 F)⁻¹ := by
    simpa [Book.Ch02.lambdaSqFinite] using hloc
  rw [hlocalEq']
  calc
    sensitivityDsharp R (h.restrict hR) *
        (Book.Ch02.lambdaSqFinite R u 2 F)⁻¹ ≤
      sensitivityDsharp R (h.restrict hR) *
        (Book.Ch02.multiscaleDescendantWeight Q
          (Q.scale - (j : ℤ)) u *
            (Book.Ch02.lambdaSqFinite Q u 2 F)⁻¹) :=
          mul_le_mul_of_nonneg_left hloc' hDlocal
    _ ≤ ((3 : ℝ) ^ (-(j : ℤ)) * sensitivityDsharp Q h) *
        (Book.Ch02.multiscaleDescendantWeight Q
          (Q.scale - (j : ℤ)) u *
            (Book.Ch02.lambdaSqFinite Q u 2 F)⁻¹) :=
          mul_le_mul_of_nonneg_right hD
            (mul_nonneg hweight hrootInv)
    _ = (sensitivityDsharp Q h *
          (Book.Ch02.lambdaSqFinite Q u 2 F)⁻¹) *
          ((3 : ℝ) ^ (-(j : ℤ)) *
            Book.Ch02.multiscaleDescendantWeight Q
              (Q.scale - (j : ℤ)) u) := by ring
    _ ≤ sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q u 2 F)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left
            (sensitivity_descendant_weight_cancel Q j hu4)
            (mul_nonneg hDroot hrootInv)
    _ = sensitivityDsharp Q h *
        (Book.Ch02.lambdaSqFinite Q u 2 F)⁻¹ := by ring

end

end ASDExplicitGamma.Triadic
