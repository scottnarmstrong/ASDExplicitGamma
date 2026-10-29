module

public import ASDExplicitGamma.Native.ParentBoundaryBandAffineUpper
public import ASDExplicitGamma.Native.ParentRowInverseMean
public import ASDExplicitGamma.Native.ParentBoundaryBandInverseMeanCap
public import ASDExplicitGamma.Native.ParentBoundaryFlatMeanLoss
public import ASDExplicitGamma.Native.ParentBoundaryInverseBulk

/-! The own-native affine expectation bound, including the genuine cell
variance floor and exact total local inverse-bank cap. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The actual annealed affine term obeys the own-native Y/2 trace bill,
2v(b-1) inverse charge and sharp cell variance floor. Every bank and
integrability input is discharged from strict-past native states. -/
theorem parent_row_affine_upper
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (r : ℕ) (hr : r≤5)
    (U0 : TriadicCube 2) (hU0 : U0∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : t≤1) (hpast : ∀ k<n,nativeInductionState M h k)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∫ omega,oldSignedFlatAffineContribution (originCube 2 n) r
      (parentBoundaryBandFrameField M n height t omega) b L ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      (parentBoundaryDirichletEnergy (originCube 2 n) b L/2)*
        (∫ omega,traceDefect (cubeSet U0)
          (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
          (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
      2*b^2*((3683/2500:ℝ)-1)+
      (4+2*Real.sqrt 2)*(cubeScaleFactor (originCube 2 n)/(Real.pi*(3:ℝ)^r))^2*mainFlatSigmaSq b L := by
  let Q := originCube 2 n
  let Y := parentBoundaryDirichletEnergy Q b L
  let cp := parentBoundaryBandBlockMean M n height t U0 true
  let cm := parentBoundaryBandBlockMean M n height t U0 false
  let cap : ℝ := (3683/2500:ℝ)
  let xp := descendantsAverage Q r (fun U => oldSignedFlatMeanSize Q U b L true^2)
  let ym := descendantsAverage Q r (fun U => oldSignedFlatMeanSize Q U b L false^2)
  let dx := oldSignedFlatL2Size Q Q b L true^2-xp
  let dy := oldSignedFlatL2Size Q Q b L false^2-ym
  have hpos (plus : Bool) : 0≤parentBoundaryFlatVariance Q r b L plus := by
    unfold parentBoundaryFlatVariance descendantsAverage
    apply tsum_nonneg
    intro i
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun U _ => hilbertEnergy_nonneg U _))
  have hdx : 0≤dx := by dsimp only [dx,xp]; rw [parent_boundary_flat_mean_loss]; exact hpos true
  have hdy : 0≤dy := by dsimp only [dy,ym]; rw [parent_boundary_flat_mean_loss]; exact hpos false
  have hcp : 0≤cp := (parent_boundary_band_block_mean M h hM n height hheight r U0 hU0 t true).1
  have hcm : 0≤cm := (parent_boundary_band_block_mean M h hM n height hheight r U0 hU0 t false).1
  have hcap : cm≤cap := parent_row_inverse_block_mean M h hM hg n height hheight r hr U0 hU0 t ht hpast
  have hcap1 : 1≤cap := by norm_num [cap,inverseBankCap,inverseBankReserve]
  have hY := parent_boundary_dirichlet_energy_bounds Q b L
  have hy : oldSignedFlatL2Size Q Q b L false^2=Y := by
    rw [old_signed_flat_l2_size_sq]
    simp only [oldSignedFlatInput,Bool.false_eq_true,ite_false,old_signed_flat_minus_l2_mode]
    rfl
  have hx : oldSignedFlatL2Size Q Q b L true^2=2*b^2-Y := by
    have hh := old_signed_joint_flat_l2_identity Q b L
    rw [hy] at hh
    linarith only [hh]
  have ha := parent_boundary_band_affine_expected_coefficients M h hM n height hheight r t b L U0 hU0
  have htrace := parent_boundary_band_trace_block_means M h hM n height hheight r U0 hU0 t
  rw [htrace]
  have hbound := mul_le_mul_of_nonneg_left (sub_le_sub_right hcap 1)
    (by linarith only [hY.2] : 0≤2*b^2-2*Y)
  have hbase := mul_le_mul_of_nonneg_right (by linarith only [hY.1] : 2*b^2-2*Y≤2*b^2)
    (sub_nonneg.mpr hcap1)
  have hde := parent_boundary_joint_flat_mean_loss_bound Q r b L
  change dx+dy≤_ at hde
  have heq : (∫ omega,oldSignedFlatAffineContribution Q r
      (parentBoundaryBandFrameField M n height t omega) b L ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      Y*(cp+cm-2)+(2*b^2-2*Y)*(cm-1)-cm*dx-cp*dy+dx+dy := by
    rw [ha]
    dsimp only [dx,dy,xp,ym,cp,cm]
    rw [hy,hx]
    ring
  rw [heq]
  dsimp only [cap] at hbound hbase
  nlinarith only [hbound,hbase,hde,mul_nonneg hcm hdx,mul_nonneg hcp hdy]

end
end ASDExplicitGamma.Native
