module

public import ASDExplicitGamma.Native.OldSignedAffineResidualSplit
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport

/-! Constant-one affine/centered triangle in the actual weighted energy. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
open scoped RealInnerProductSpace
noncomputable section

/-- Genuine weighted Cauchy for arbitrary physical square-integrable fields. -/
theorem old_hessian_energy_pairing_sqrt (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    |oldSignedEnergyPairing Q nu sigma k F G|≤
      Real.sqrt (oldSignedEnergyPairing Q nu sigma k F F)*
        Real.sqrt (oldSignedEnergyPairing Q nu sigma k G G) := by
  rw [←old_signed_energy_inner_fields Q nu sigma hnu hsigma k hF hG,
    ←old_signed_energy_inner_fields Q nu sigma hnu hsigma k hF hF,
    ←old_signed_energy_inner_fields Q nu sigma hnu hsigma k hG hG,
    real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _),Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

/-- The literal residual of an arbitrary physical input pays the affine
coarse energy plus a single centered projection root. -/
theorem old_hessian_flat_projection_energy_triangle (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F)
    (hPfst : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => (F x).1 i-(oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => (F x).2 i-(oldSignedBlockMean Q F).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let m := oldSignedBlockMean Q F
    let Z := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    oldSignedEnergyPairing Q nu sigma k Z Z≤
      (Real.sqrt (blockVecDot m (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) m))+
        Real.sqrt (oldSignedResponseHistory Q a)*oldSignedBlockPositiveNorm Q (fun x => F x-m))^2 := by
  intro a m Z
  let HM := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField m
  let G := fun x => F x-m
  have hG : MemBlockL2 (openCubeSet Q) G := hF.sub (memLp_const m)
  let HG := toHilbertBlockL2OfBlockField hG
  let ZM := scalarResidualField Q nu sigma hnu hsigma k HM
  let ZG := scalarResidualField Q nu sigma hnu hsigma k HG
  let A := oldSignedEnergyPairing Q nu sigma k ZM ZM
  let C := oldSignedEnergyPairing Q nu sigma k ZG ZG
  have ha : 0≤A := by
    dsimp only [A]
    rw [←old_signed_energy_inner_fields Q nu sigma hnu hsigma k (Lp.memLp _) (Lp.memLp _)]
    exact real_inner_self_nonneg
  have hc : 0≤C := by
    dsimp only [C]
    rw [←old_signed_energy_inner_fields Q nu sigma hnu hsigma k (Lp.memLp _) (Lp.memLp _)]
    exact real_inner_self_nonneg
  have hs := old_signed_block_field_mean_split Q nu sigma hnu hsigma k F hF
  have he := old_signed_residual_energy_split Q nu sigma hnu hsigma k HM HG
  rw [←hs] at he
  have hp := (le_abs_self (oldSignedEnergyPairing Q nu sigma k ZM ZG)).trans
    (old_hessian_energy_pairing_sqrt Q nu sigma hnu hsigma k (Lp.memLp _) (Lp.memLp _))
  have htri : oldSignedEnergyPairing Q nu sigma k Z Z≤(Real.sqrt A+Real.sqrt C)^2 := by
    have ha2 := Real.sq_sqrt ha
    have hc2 := Real.sq_sqrt hc
    nlinarith only [he,hp,ha2,hc2]
  have hcenter := old_signed_flat_source_energy Q nu sigma hnu hsigma k G hG hPfst hPsnd
  have hroot := Real.sqrt_le_sqrt hcenter
  have hM0 : 0≤oldSignedResponseHistory Q (responseFramePlanarCoefficientField nu sigma k) := ENNReal.toReal_nonneg
  have hO : 0≤oldSignedBlockPositiveNorm Q G := Real.sqrt_nonneg _
  rw [Real.sqrt_mul hM0,Real.sqrt_sq hO] at hroot
  have hAff := old_signed_affine_energy Q nu sigma hnu hsigma k m
  exact (htri.trans (pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (add_le_add le_rfl hroot) 2)).trans_eq (by rw [←hAff])

end
end ASDExplicitGamma.Scalar
