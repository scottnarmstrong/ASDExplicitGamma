module

public import ASDExplicitGamma.Native.OldSignedShearGauge
public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Triadic.DiagAffine
public import ASDExplicitGamma.Native.BoundaryChargeSignedTrial
public import ASDExplicitGamma.Main.InverseHessianSourceComponents
public import ASDExplicitGamma.Main.PartialInsertion
public import ASDExplicitGamma.Main.Q3HeatIdentity
public import ASDExplicitGamma.Response.Analytic

/-! The source-only coarse-potential change with the unchanged fine
interpolant. The product term and its global boundary cancellation are literal. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Variational Response Triadic
noncomputable section

/-- Signed pure-second mixed source: localize v-phi on the fine interpolant,
then add the coarse cell-zero potential times the column divergence. -/
def oldHessianMixedSource {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (eta v phi : H1Function U) : Vec 2 → BlockVec 2 :=
  fun x => oldSignedLocalizedPotentialShear I eta (v-phi) x+
    (0,-(phi x • lemmaVPlanarWeakColumnDivergence eta x))

/-- Exact source change: its fine-interface contribution is a global curl
of I(phi), not an asserted zero fine-cell residual. -/
theorem old_hessian_mixed_source_difference {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (eta v phi : H1Function U) :
    (fun x => oldHessianMixedSource I eta v phi x-
      oldSignedLocalizedPotentialShear I eta v x) =
    (fun x => (0,-localizedColumnProductDivergence eta (I phi) x)) := by
  funext x
  apply Prod.ext
  · funext i
    simp [oldHessianMixedSource,oldSignedLocalizedPotentialShear]
  · funext i
    fin_cases i <;>
      simp [oldHessianMixedSource,oldSignedLocalizedPotentialShear,lemmaVPlanarRowField,
        localizedColumnProductDivergence,H1Function.sub_grad,map_sub,
        lemmaVPlanarWeakColumnDivergence,matVecMul,responsePlanarJ,Fin.sum_univ_two] <;> ring

/-- The retained coarse product is genuinely L2 on the physical cell. -/
theorem old_hessian_product_source_memL2 (Q : TriadicCube 2)
    (eta phi : H1Function (openCubeSet Q))
    (heta : MemLp eta.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hdeta : ∀ i, MemLp (fun x => eta.grad x i) ⊤ (volume.restrict (openCubeSet Q))) :
    MemBlockL2 (openCubeSet Q) (fun x => (0,-(phi x • lemmaVPlanarWeakColumnDivergence eta x))) := by
  have hp : MemVectorL2 (openCubeSet Q) (fun x => phi x • lemmaVPlanarWeakColumnDivergence eta x) := by
    have hh := (localizedColumnProductDivergence_memL2 eta phi heta hdeta).add
      (lemmaVPlanar_skewGradient_memL2 phi heta)
    convert hh using 1
    funext x
    change phi x • lemmaVPlanarWeakColumnDivergence eta x =
      (phi x • lemmaVPlanarWeakColumnDivergence eta x-
        eta x • matVecMul responsePlanarJ (phi.grad x))+
        eta x • matVecMul responsePlanarJ (phi.grad x)
    exact (sub_add_cancel _ _).symm
  exact memBlockL2_blockField MemLp.zero hp.neg

theorem old_hessian_mixed_source_memL2 (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (eta v phi : H1Function (openCubeSet Q))
    (heta : MemLp eta.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hdeta : ∀ i, MemLp (fun x => eta.grad x i) ⊤ (volume.restrict (openCubeSet Q))) :
    MemBlockL2 (openCubeSet Q) (oldHessianMixedSource I eta v phi) := by
  exact (old_signed_localized_potential_shear_memL2 Q I eta (v-phi) heta hdeta).add
    (old_hessian_product_source_memL2 Q eta phi heta hdeta)

/-- Fine interpolation of the coarse zero-trace potential supplies the
actual global source-change variation. No fine-cell annihilation is used. -/
theorem old_hessian_mixed_source_change_variation (Q : TriadicCube 2) (mesh : ℕ)
    (eta v : H1Function (openCubeSet Q)) (phi : H10Function (openCubeSet Q))
    (heta : MemLp eta.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hdeta : ∀ i, MemLp (fun x => eta.grad x i) ⊤ (volume.restrict (openCubeSet Q))) :
    ScalarVariation (openCubeSet Q) (fun x =>
      oldHessianMixedSource (diagInterpolant Q mesh) eta v phi.toH1Function x-
        oldSignedLocalizedPotentialShear (diagInterpolant Q mesh) eta v x) := by
  rw [old_hessian_mixed_source_difference]
  let mixedSourceFiniteVolume : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hm := localizedColumnProductDivergence_memL2 eta
    (diagInterpolant Q mesh phi.toH1Function) heta hdeta
  have hs := localizedColumnProductDivergence_solenoidal
    (isOpenBoundedConvexDomain_openCubeSet Q) eta (diagInterpolant Q mesh phi.toH1Function)
    (diagInterpolant_h10_memH10 Q mesh phi) heta hdeta
  refine ⟨memBlockL2_blockField MemLp.zero hm.neg,isPotentialZeroTraceOn_zero,?_⟩
  have hn : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (fun x =>
      (-1:ℝ) • localizedColumnProductDivergence eta (diagInterpolant Q mesh phi.toH1Function) x) :=
    isSolenoidalZeroNormalTraceOn_smul hs (-1)
  simpa only [neg_one_smul] using hn

/-- The entire mixed source has the same parent shear gauge as the old
localized source, with both genuine zero-trace potentials constructed first. -/
theorem old_hessian_mixed_source_physical_variation (Q : TriadicCube 2) (mesh : ℕ)
    (eta : H1Function (openCubeSet Q)) (v phi : H10Function (openCubeSet Q))
    (heta : MemLp eta.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hdeta : ∀ i, MemLp (fun x => eta.grad x i) ⊤ (volume.restrict (openCubeSet Q))) :
    ScalarVariation (openCubeSet Q) (fun x =>
      oldHessianMixedSource (diagInterpolant Q mesh) eta v.toH1Function phi.toH1Function x-
        oldSignedPhysicalPotentialShear eta v.toH1Function x) := by
  have hc := old_hessian_mixed_source_change_variation Q mesh eta v.toH1Function phi heta hdeta
  have hf := old_signed_localized_physical_shear_variation Q (diagInterpolant Q mesh)
    eta v.toH1Function (by
      simpa only [H1Function.sub_toFun] using memH10_sub v.memH10
        (diagInterpolant_h10_memH10 Q mesh v)) heta hdeta
  have hh := scalar_variation_add hc hf
  convert hh using 1
  funext x
  change oldHessianMixedSource (diagInterpolant Q mesh) eta v.toH1Function phi.toH1Function x-
    oldSignedPhysicalPotentialShear eta v.toH1Function x =
    (oldHessianMixedSource (diagInterpolant Q mesh) eta v.toH1Function phi.toH1Function x-
      oldSignedLocalizedPotentialShear (diagInterpolant Q mesh) eta v.toH1Function x)+
    (oldSignedLocalizedPotentialShear (diagInterpolant Q mesh) eta v.toH1Function x-
      oldSignedPhysicalPotentialShear eta v.toH1Function x)
  abel

end
end ASDExplicitGamma.Scalar
