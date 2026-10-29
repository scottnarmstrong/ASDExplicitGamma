module

public import ASDExplicitGamma.Native.OldSignedFlatTangent
public import ASDExplicitGamma.Native.OldSignedShearFieldTransport
public import ASDExplicitGamma.Native.OldSignedBottomFlatCovariance
public import ASDExplicitGamma.Native.OldSignedAveragePairing

/-! The actual bottom flat feedback splits into the negative Dirichlet
tangent and the signed reciprocal-error covariance before any absolute value. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- One actual bottom flat feedback has exactly the negative Dirichlet
energy and reciprocal covariance terms, retaining the physical sign. -/
theorem old_signed_actual_bottom_flat_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k;
    -oldSignedEnergyPairing Q nu sigma k
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (oldSignedFlatMinusBlock Q b L n i))=
      -(∑ j : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,j) x))+
      ∑ j : Fin 2,∫ x,oldSignedBottomReciprocalError Q a hEll i x j*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) j
          ∂normalizedCubeMeasure Q := by
  intro a hEll
  let V := fun x => q3Convolution b L h3Zero (whiteBasis n) x •
    matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x)
  let e := oldSignedBottomReciprocalError Q a hEll i
  have hC := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n
    (old_signed_flat_minus_block_memL2 Q b L n i)
  have hV : MemVectorL2 (openCubeSet Q) V := by
    have hh := (memVectorL2_snd_of_memBlockL2 hC).neg
    change MemVectorL2 (openCubeSet Q) (fun x => -(-V x)) at hh
    simpa only [neg_neg] using hh
  have he : MemVectorL2 (openCubeSet Q) e :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q
      (memLp_pi_iff.mpr (fun j => old_signed_reciprocal_error_memLp Q a hEll (0,basisVec i) j))
  have hpair := old_signed_vector_average_pairing Q V e hV he
  have hp : volumeAverage (openCubeSet Q) (fun x => vecDot (V x) (e x))=
      ∑ j : Fin 2,∫ x,e x j*q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) j
          ∂normalizedCubeMeasure Q := by
    rw [hpair]
    apply Finset.sum_congr rfl
    intro j _
    rw [pairing,cubeAverage_eq_integral_normalizedCubeMeasure]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by change _*_= _; simp only [V,Pi.smul_apply,smul_eq_mul]; ring)
  have hsum : (fun x => vecDot (V x)
      (blockMatVecMul (blockCoeffField a x)
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i) x)).2)=
      fun x => vecDot (V x) (e x)+vecDot (V x) (basisVec i) := by
    funext x
    dsimp only [e,oldSignedBottomReciprocalError,oldSignedFrameCanonicalField]
    simp only [vecDot,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
    ring
  rw [old_signed_energy_physical_shear_pairing Q nu sigma hnu hsigma k b L n
    (Lp.memLp (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i)))
    (old_signed_flat_minus_block_memL2 Q b L n i),neg_neg]
  change volumeAverage (openCubeSet Q) (fun x => vecDot (V x)
    (blockMatVecMul (blockCoeffField a x)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i) x)).2)=_
  have hadd : volumeAverage (openCubeSet Q) (fun x => vecDot (V x) (e x)+vecDot (V x) (basisVec i))=
      volumeAverage (openCubeSet Q) (fun x => vecDot (V x) (e x))+
      volumeAverage (openCubeSet Q) (fun x => vecDot (V x) (basisVec i)) :=
    volumeAverage_add (integrableOn_vecDot_of_memVectorL2 hV he)
      (integrableOn_vecDot_of_memVectorL2 hV (memLp_const (basisVec i)))
  have haff : volumeAverage (openCubeSet Q) (fun x => vecDot (V x) (basisVec i))=
      -(∑ j : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,j) x)) :=
    old_signed_flat_minus_affine_pairing Q b L n i
  rw [hsum,hadd,hp,haff]
  exact add_comm _ _

end
end ASDExplicitGamma.Native
