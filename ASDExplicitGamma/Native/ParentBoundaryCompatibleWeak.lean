module

public import ASDExplicitGamma.Native.OldSignedCompatibleMeans
public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing
public import ASDExplicitGamma.Inverse.PureFluxGeneratorMinimizerEnergy

/-! Fine-cell inverse-history coercivity for actual compatible fields.
Restrictions are compatible fields, with no extra local boundary condition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The half-discount coercivity history is bounded by the OLD
quarter-discount history on the same physical cube. -/
theorem parent_boundary_compatible_history_le (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    compatibleInverseHistory Q a≤lemmaVInverseHistory Q a ((3:ℝ)^(1/4:ℝ)) := by
  have hq : 1<Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤3 by norm_num),Real.sqrt_nonneg (3:ℝ)]
  have hquarter : 1<(3:ℝ)^(1/4:ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hcomp : (3:ℝ)^(1/4:ℝ)≤Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact lemmaVInverseHistory_le_of_inverse_discount Q hEll hq hquarter
    ((inv_le_inv₀ (by positivity) (by positivity)).mpr hcomp)

/-- The literal first component of every compatible field has the fine-cell
weak budget paid by the same complete inverse history and its actual energy. -/
theorem parent_boundary_compatible_tiled_weak (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (B : ℝ)
    {F : Vec 2 → BlockVec 2} (hF : ScalarCompatible (openCubeSet Q) F)
    (hhist : ∀ U∈descendantsAtDepth Q depth,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
        ((3:ℝ)^(1/4:ℝ))≤B) :
    lemmaVTiledWeakEnergy Q depth (fun x => (F x).1)≤
      B*oldSignedEnergyPairing Q nu sigma k F F := by
  let a := responseFramePlanarCoefficientField nu sigma k
  let W : BlockState 2 := ⟨fun x => (F x).1,fun x => (F x).2⟩
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have hlocal (U : TriadicCube 2) (hU : U∈descendantsAtDepth Q depth) :
      vectorWeakHaarEnergy U (fun x => (F x).1)≤
        B*cubeAverage U (blockPairingIntegrand a W W) := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    have hEllU := hEll.mono (measurableSet_openCubeSet U) hsub
    have hFU := old_signed_compatible_restrict Q U hsub hF
    have hh := compatible_coercivity hEllU W hFU.2.1 hFU.2.2 hFU.1
    have hH := (parent_boundary_compatible_history_le U hEllU).trans (hhist U hU)
    have he := compatible_blockPairingAverage_nonneg hEllU W
    have hb := hh.trans (mul_le_mul_of_nonneg_right hH he)
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    exact hb
  have hint : IntegrableOn (blockPairingIntegrand a W W) (openCubeSet Q) :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hF.1 hF.1 hEll
  have havg : descendantsAverage Q depth (fun U => cubeAverage U (blockPairingIntegrand a W W))=
      oldSignedEnergyPairing Q nu sigma k F F := by
    rw [←cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q depth _
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hint)]
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    rfl
  change descendantsAverage Q depth _≤_
  calc
    _ ≤ descendantsAverage Q depth (fun U => B*cubeAverage U (blockPairingIntegrand a W W)) :=
      descendantsAverage_le hlocal
    _ = B*oldSignedEnergyPairing Q nu sigma k F F := by
      rw [descendantsAverage_mul_left,havg]

end
end ASDExplicitGamma.Native
