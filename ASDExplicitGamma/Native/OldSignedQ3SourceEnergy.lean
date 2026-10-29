module

public import ASDExplicitGamma.Native.OldSignedQ3SourceAdmissibility
public import ASDExplicitGamma.Inverse.PureFluxGeneratorSharpTrace

/-! Qualitative complete-mode convergence of the actual uncentered OLD
source energy, reusing the full q3 row covariance trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
noncomputable section

/-- A nonnegative summable finite partition average controls every
actual cell series; its positive averaging weight is not dropped. -/
theorem old_signed_summable_of_descendant_average {I : Type*}
    (Q : TriadicCube 2) (mesh : ℕ) (f : I → TriadicCube 2 → ℝ)
    (hf : ∀ n,∀ U ∈ descendantsAtDepth Q mesh,0≤f n U)
    (hs : Summable (fun n => descendantsAverage Q mesh (f n)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q mesh) :
    Summable (fun n => f n U) := by
  classical
  have hc : ((descendantsAtDepth Q mesh).card : ℝ)≠0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q mesh)
  apply (hs.mul_left ((descendantsAtDepth Q mesh).card : ℝ)).of_nonneg_of_le (fun n => hf n U hU)
  intro n
  dsimp only [descendantsAverage]
  rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
  exact Finset.single_le_sum (fun V hV => hf n V hV) hU

/-- The uncentered q3 row's complete positive energy converges on every
finite DIAG partition; no parent Haar modes or value column are removed. -/
theorem old_signed_q3_row_energy_summable (n : ℤ) (b : ℝ) (L : {l : ℝ // 0<l})
    (mesh : ℕ) (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n))) :
    Summable (pureFluxMainQ3RowEnergy n b 1 L mesh p u) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let Y := pureFluxMainQ3RowEnergy n b 1 L mesh p u
  let C := (Real.sqrt (b^2)+diagMeshRadius Q mesh*(36/25)*Real.sqrt ((156/5)*b^2/L.1^2)+
    (diagMeshRadius Q mesh)^2*(57/200)*Real.sqrt ((46488/25)*b^2/L.1^4))*
      Real.sqrt (lemmaVTiledWeakEnergy Q mesh v.grad)
  have hcap (s : Finset whiteBasisIndex) : Real.sqrt (∑ l ∈ s,Y l)≤C :=
    pureFluxMainQ3Row_trace_finset_sharp n b L mesh p u s
  have hC : 0≤C := by
    simpa only [Finset.sum_empty,Real.sqrt_zero] using hcap ∅
  have hY (l : whiteBasisIndex) : 0≤Y l :=
    descendantsAverage_nonneg Q mesh _ (fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  apply summable_of_sum_le hY
  intro s
  have hs : 0≤∑ l ∈ s,Y l := Finset.sum_nonneg (fun l _ => hY l)
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg (∑ l ∈ s,Y l)) hC).mpr (hcap s)
  simpa only [Real.sq_sqrt hs] using hh

/-- The actual canonical OLD-error source has a genuine summable complete
positive-norm energy on the chosen partition. This is a convergence fact,
not an assumed source-energy estimate in the final signed generator. -/
theorem old_signed_old_error_source_energy_summable (n : ℤ) (mesh : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube 2 n)) a)
    (P : BlockVec 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Summable (fun l : whiteBasisIndex => descendantsAverage (originCube 2 n) mesh
      (fun U => vectorPositiveHaarNorm U
        (fun x => (oldSignedOldErrorSource (originCube 2 n) mesh a hEll b L l P x).2)^2)) := by
  have h := old_signed_q3_row_energy_summable n b L mesh 0
    (oldSignedCanonicalFirstCorrector (originCube 2 n) a hEll P)
  apply h.congr
  intro l
  simp only [pureFluxMainQ3RowEnergy,pureFluxMainQ3BasisFrameMultiplier,inv_one,one_smul,
    old_signed_zero_affine_potential]
  apply congrArg (descendantsAverage (originCube 2 n) mesh)
  funext U
  rw [vectorPositiveHaarNorm,Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg U _)]
  simp only [oldSignedOldErrorSource,oldSignedLocalizedPotentialShear,
    vectorPositiveHaarEnergy,Pi.neg_apply,primalEnergy_neg]

/-- In particular every actual cell's complete OLD-source positive-norm
square series converges, as required by the complete mixed feedback. -/
theorem old_signed_old_error_source_cell_energy_summable (n : ℤ) (mesh : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube 2 n)) a)
    (P : BlockVec 2) (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) mesh) :
    Summable (fun l : whiteBasisIndex => vectorPositiveHaarNorm U
      (fun x => (oldSignedOldErrorSource (originCube 2 n) mesh a hEll b L l P x).2)^2) :=
  old_signed_summable_of_descendant_average (originCube 2 n) mesh _
    (fun _ _ _ => sq_nonneg _) (old_signed_old_error_source_energy_summable n mesh a hEll P b L) U hU

end
end ASDExplicitGamma.Native
