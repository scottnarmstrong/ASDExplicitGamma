module

public import ASDExplicitGamma.Native.OldSignedResidualDualCompatible
public import ASDExplicitGamma.Variational.CompatibleCoercivity
public import ASDExplicitGamma.Variational.LemmaVTiles
public import ASDExplicitGamma.Variational.ProjectedSource

/-! The actual reciprocal residual uses inverse compatible coercivity. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Compatible first-component weak energy is controlled by the complete
inverse history and the literal physical energy. -/
theorem old_signed_compatible_weak_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {Z : Vec 2 → BlockVec 2} (hZ : ScalarCompatible (openCubeSet Q) Z) :
    vectorWeakHaarEnergy Q (fun x i => (Z x).1 i) ≤
      lemmaVInverseHistory Q (responseFramePlanarCoefficientField nu sigma k)
        (Real.sqrt 3) * oldSignedEnergyPairing Q nu sigma k Z Z := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField nu sigma k
  let W : BlockState 2 := ⟨fun x => (Z x).1, fun x => (Z x).2⟩
  have hWfield : W.eval = Z := by
    funext x
    exact Prod.eta _
  have hWmem : MemBlockL2 U W.eval := by
    rw [hWfield]
    exact hZ.1
  have hWpot : IsBlockPotentialOn U W := by
    change IsPotentialOn U (fun x => (W.eval x).1)
    simpa [W, BlockState.eval] using hZ.2.1
  have hWsol : IsBlockSolenoidalOn U W := by
    change IsSolenoidalOn U (fun x => (W.eval x).2)
    simpa [W, BlockState.eval] using hZ.2.2
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hcoercive := Variational.compatible_coercivity hEll W hWpot hWsol hWmem
  have hPair : blockPairingAverage U a W W = oldSignedEnergyPairing Q nu sigma k Z Z := by
    change volumeAverage U (fun x => blockVecDot (Z x)
      (blockMatVecMul (blockCoeffField a x) (Z x))) = _
    rfl
  calc
    _ ≤ lemmaVInverseHistory Q a (Real.sqrt 3) * blockPairingAverage U a W W := by
      simpa [Variational.compatibleInverseHistory, W, BlockState.eval, a] using hcoercive
    _ = lemmaVInverseHistory Q a (Real.sqrt 3) * oldSignedEnergyPairing Q nu sigma k Z Z := by
      rw [hPair]


/-- Projection orthogonality makes the reflected residual compatible,
so its reciprocal energy has the inverse-history coefficient. -/
theorem old_signed_residual_reciprocal_weak_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (H : HilbertBlockL2 (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k H
    vectorWeakHaarEnergy Q (fun x => (scalarCoefficientFlux a Z x).2) ≤
      oldSignedInverseHistory Q a*oldSignedEnergyPairing Q nu sigma k Z Z := by
  intro a Z
  have hh := old_signed_compatible_weak_energy Q nu sigma hnu hsigma k
    (old_signed_reflected_residual_compatible Q nu sigma hnu hsigma k H)
  rw [old_signed_dual_reflection_isometry Q nu sigma hnu hsigma k] at hh
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hroot : 1<Real.sqrt 3 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hquarter : 1<(3:ℝ)^(1/4:ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hquarterLe : (3:ℝ)^(1/4:ℝ)≤Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hInvLe : (Real.sqrt 3)⁻¹≤((3:ℝ)^(1/4:ℝ))⁻¹ :=
    (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num)) (by positivity)).2 hquarterLe
  have hHistory := lemmaVInverseHistory_le_of_inverse_discount Q hEll hroot hquarter hInvLe
  have hE : 0≤oldSignedEnergyPairing Q nu sigma k Z Z := by
    rw [←old_signed_energy_inner_fields Q nu sigma hnu hsigma k (Lp.memLp Z) (Lp.memLp Z)]
    exact real_inner_self_nonneg
  have hb := hh.trans (mul_le_mul_of_nonneg_right hHistory hE)
  simpa only [oldSignedDualReflection,Prod.fst_swap,scalarCoefficientFlux,oldSignedInverseHistory,a,Z] using hb


/-- A centered source's reciprocal residual costs sqrt(B M) times its
positive-Haar oscillation, with no added input weak norm. -/
theorem old_signed_centered_reciprocal_norm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (G : Vec 2 → BlockVec 2)
    (hG : MemBlockL2 (openCubeSet Q) G)
    (hPfst : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (G x).1 i))))
    (hPsnd : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (G x).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hG)
    vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux a Z x).2) ≤
      Real.sqrt (oldSignedInverseHistory Q a*oldSignedResponseHistory Q a)*
        oldSignedBlockPositiveNorm Q G := by
  intro a Z
  have he := old_signed_residual_reciprocal_weak_energy Q nu sigma hnu hsigma k
    (toHilbertBlockL2OfBlockField hG)
  have hs := old_signed_flat_source_energy Q nu sigma hnu hsigma k G hG hPfst hPsnd
  have hB : 0≤oldSignedInverseHistory Q a :=
    lemmaVInverseHistory_nonneg Q a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hM : 0≤oldSignedResponseHistory Q a := ENNReal.toReal_nonneg
  have hh := he.trans (mul_le_mul_of_nonneg_left hs hB)
  have hr := Real.sqrt_le_sqrt hh
  change vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux a Z x).2) ≤
    Real.sqrt (oldSignedInverseHistory Q a*(oldSignedResponseHistory Q a*
      oldSignedBlockPositiveNorm Q G^2)) at hr
  rw [←mul_assoc,Real.sqrt_mul (mul_nonneg hB hM),
    Real.sqrt_sq (show 0≤oldSignedBlockPositiveNorm Q G from Real.sqrt_nonneg _)] at hr
  exact hr

end
end ASDExplicitGamma.Native
