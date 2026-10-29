module

public import ASDExplicitGamma.Main.HotCovPrincipal

/-! MA-E-COVARIANCE, step 7: the affine receivers are linear in their
cell-constant datum, almost everywhere on the cell. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational

noncomputable section

theorem hotCov_canon_add_ae (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P R : BlockVec 2) :
    (fun x => (oldSignedCanonicalAffineField Q a hEll (P + R) : Vec 2 → BlockVec 2) x) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
    fun x => (oldSignedCanonicalAffineField Q a hEll P : Vec 2 → BlockVec 2) x +
      (oldSignedCanonicalAffineField Q a hEll R : Vec 2 → BlockVec 2) x := by
  have h : oldSignedCanonicalAffineField Q a hEll (P + R) =
      oldSignedCanonicalAffineField Q a hEll P + oldSignedCanonicalAffineField Q a hEll R := by
    simp only [oldSignedCanonicalAffineField, map_add]
  exact (Lp.ext_iff.mp h).trans (Lp.coeFn_add _ _)

theorem hotCov_canon_smul_ae (Q : TriadicCube 2) (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (c : ℝ) (P : BlockVec 2) :
    (fun x => (oldSignedCanonicalAffineField Q a hEll (c • P) : Vec 2 → BlockVec 2) x) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
    fun x => c • (oldSignedCanonicalAffineField Q a hEll P : Vec 2 → BlockVec 2) x := by
  have h : oldSignedCanonicalAffineField Q a hEll (c • P) =
      c • oldSignedCanonicalAffineField Q a hEll P := by
    simp only [oldSignedCanonicalAffineField, map_smul]
  exact (Lp.ext_iff.mp h).trans (Lp.coeFn_smul c _)

/-- A datum `(0,ν)` splits along the two basis loads. -/
theorem hotCov_block_decomp_bottom (ν : Vec 2) :
    ((0 : Vec 2), ν) = ν 0 • ((0 : Vec 2), basisVec 0) + ν 1 • ((0 : Vec 2), basisVec 1) := by
  ext i
  · simp
  · fin_cases i <;> simp [basisVec, Pi.single_apply]

theorem hotCov_block_decomp_top (ν : Vec 2) :
    (ν, (0 : Vec 2)) = ν 0 • (basisVec 0, (0 : Vec 2)) + ν 1 • (basisVec 1, (0 : Vec 2)) := by
  ext i
  · fin_cases i <;> simp [basisVec, Pi.single_apply]
  · simp

theorem hotCov_topRcv_linear (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (ν : Vec 2) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)),
      hotCovTopRcv Q d nu sigma hnu hsigma k U ν x =
        ν 0 • hotCovTopRcv Q d nu sigma hnu hsigma k U (basisVec 0) x +
          ν 1 • hotCovTopRcv Q d nu sigma hnu hsigma k U (basisVec 1) x := by
  let a := responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
    nu sigma hnu hsigma (hotCovCellCoef Q d k U)
  let C := fun P : BlockVec 2 =>
    (oldSignedCanonicalAffineField U.val a hEll P : Vec 2 → BlockVec 2)
  have h1 := hotCov_canon_add_ae U.val a hEll (ν 0 • ((0 : Vec 2), basisVec 0))
    (ν 1 • ((0 : Vec 2), basisVec 1))
  have h2 := hotCov_canon_smul_ae U.val a hEll (ν 0) ((0 : Vec 2), basisVec 0)
  have h3 := hotCov_canon_smul_ae U.val a hEll (ν 1) ((0 : Vec 2), basisVec 1)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hC : C ((0 : Vec 2), ν) x = ν 0 • C ((0 : Vec 2), basisVec 0) x +
      ν 1 • C ((0 : Vec 2), basisVec 1) x := by
    rw [hotCov_block_decomp_bottom ν]
    change (oldSignedCanonicalAffineField U.val a hEll
      (ν 0 • ((0 : Vec 2), basisVec 0) + ν 1 • ((0 : Vec 2), basisVec 1)) : Vec 2 → BlockVec 2) x = _
    rw [hx1]
    change (oldSignedCanonicalAffineField U.val a hEll (ν 0 • ((0 : Vec 2), basisVec 0)) :
      Vec 2 → BlockVec 2) x + (oldSignedCanonicalAffineField U.val a hEll
        (ν 1 • ((0 : Vec 2), basisVec 1)) : Vec 2 → BlockVec 2) x = _
    rw [hx2, hx3]
  have hflux : (scalarCoefficientFlux a (C ((0 : Vec 2), ν)) x).2 =
      ν 0 • (scalarCoefficientFlux a (C ((0 : Vec 2), basisVec 0)) x).2 +
        ν 1 • (scalarCoefficientFlux a (C ((0 : Vec 2), basisVec 1)) x).2 := by
    simp only [scalarCoefficientFlux]
    rw [hC, blockMatVecMul_add, blockMatVecMul_smul, blockMatVecMul_smul]
    simp
  change -((scalarCoefficientFlux a (C ((0 : Vec 2), ν)) x).2 - ν) =
    ν 0 • -((scalarCoefficientFlux a (C ((0 : Vec 2), basisVec 0)) x).2 - basisVec 0) +
      ν 1 • -((scalarCoefficientFlux a (C ((0 : Vec 2), basisVec 1)) x).2 - basisVec 1)
  rw [hflux]
  ext i
  fin_cases i <;> simp [basisVec, Pi.single_apply] <;> ring

theorem hotCov_botRcv_linear (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (ν : Vec 2) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)),
      hotCovBotRcv Q d nu sigma hnu hsigma k U ν x =
        ν 0 • hotCovBotRcv Q d nu sigma hnu hsigma k U (basisVec 0) x +
          ν 1 • hotCovBotRcv Q d nu sigma hnu hsigma k U (basisVec 1) x := by
  let a := responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
    nu sigma hnu hsigma (hotCovCellCoef Q d k U)
  let C := fun P : BlockVec 2 =>
    (oldSignedCanonicalAffineField U.val a hEll P : Vec 2 → BlockVec 2)
  have h1 := hotCov_canon_add_ae U.val a hEll (ν 0 • (basisVec 0, (0 : Vec 2)))
    (ν 1 • (basisVec 1, (0 : Vec 2)))
  have h2 := hotCov_canon_smul_ae U.val a hEll (ν 0) (basisVec 0, (0 : Vec 2))
  have h3 := hotCov_canon_smul_ae U.val a hEll (ν 1) (basisVec 1, (0 : Vec 2))
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  have hC : C (ν, (0 : Vec 2)) x = ν 0 • C (basisVec 0, (0 : Vec 2)) x +
      ν 1 • C (basisVec 1, (0 : Vec 2)) x := by
    rw [hotCov_block_decomp_top ν]
    change (oldSignedCanonicalAffineField U.val a hEll
      (ν 0 • (basisVec 0, (0 : Vec 2)) + ν 1 • (basisVec 1, (0 : Vec 2))) : Vec 2 → BlockVec 2) x = _
    rw [hx1]
    change (oldSignedCanonicalAffineField U.val a hEll (ν 0 • (basisVec 0, (0 : Vec 2))) :
      Vec 2 → BlockVec 2) x + (oldSignedCanonicalAffineField U.val a hEll
        (ν 1 • (basisVec 1, (0 : Vec 2))) : Vec 2 → BlockVec 2) x = _
    rw [hx2, hx3]
  have hflux : (scalarCoefficientFlux a (C (ν, (0 : Vec 2))) x).2 =
      ν 0 • (scalarCoefficientFlux a (C (basisVec 0, (0 : Vec 2))) x).2 +
        ν 1 • (scalarCoefficientFlux a (C (basisVec 1, (0 : Vec 2))) x).2 := by
    simp only [scalarCoefficientFlux]
    rw [hC, blockMatVecMul_add, blockMatVecMul_smul, blockMatVecMul_smul]
    simp
  change -((scalarCoefficientFlux a (C (ν, (0 : Vec 2))) x).2) =
    ν 0 • -((scalarCoefficientFlux a (C (basisVec 0, (0 : Vec 2))) x).2) +
      ν 1 • -((scalarCoefficientFlux a (C (basisVec 1, (0 : Vec 2))) x).2)
  rw [hflux]
  ext i
  fin_cases i <;> simp <;> ring

theorem hotCov_topRcv_memL2 (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (ν : Vec 2) :
    MemVectorL2 (openCubeSet U.val) (hotCovTopRcv Q d nu sigma hnu hsigma k U ν) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
    nu sigma hnu hsigma (hotCovCellCoef Q d k U)
  have hC := Lp.memLp (oldSignedCanonicalAffineField U.val
    (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)) hEll (0, ν))
  have hf := memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 U.val _ hEll hC)
  have := (hf.sub (memVectorL2_const ν)).neg
  exact this

theorem hotCov_botRcv_memL2 (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (ν : Vec 2) :
    MemVectorL2 (openCubeSet U.val) (hotCovBotRcv Q d nu sigma hnu hsigma k U ν) := by
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U.val)
    nu sigma hnu hsigma (hotCovCellCoef Q d k U)
  have hC := Lp.memLp (oldSignedCanonicalAffineField U.val
    (responseFramePlanarCoefficientField nu sigma (hotCovCellCoef Q d k U)) hEll (ν, 0))
  have hf := memVectorL2_snd_of_memBlockL2 (scalar_coefficient_flux_memL2 U.val _ hEll hC)
  exact hf.neg

end

end ASDExplicitGamma.Main
