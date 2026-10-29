module

public import ASDExplicitGamma.Variational.LocalizedShearWeak
public import ASDExplicitGamma.Scalar.DualSpaces

/-! Actual physical and localized shear fields differ by a genuine
zero-normal variation. The gauge correction is retained in trial membership. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Variational
noncomputable section

private instance oldSignedShearGaugeFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The physical pointwise skew shear acting on a genuine first potential. -/
def oldSignedPhysicalPotentialShear {U : Set (Vec 2)} (eta v : H1Function U)
    (x : Vec 2) : BlockVec 2 := (0,-(eta x • matVecMul responsePlanarJ (v.grad x)))

/-- The actual localized shear, using the same source interpolant and potential. -/
def oldSignedLocalizedPotentialShear {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (eta v : H1Function U)
    (x : Vec 2) : BlockVec 2 := (0,-lemmaVPlanarRowField I eta v x)

/-- The actual localized pure-second source is square integrable. -/
theorem old_signed_localized_potential_shear_memL2 (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (eta v : H1Function (openCubeSet Q))
    (heta : MemLp eta.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hdeta : ∀ i,MemLp (fun x => eta.grad x i) ⊤ (volume.restrict (openCubeSet Q))) :
    MemBlockL2 (openCubeSet Q) (oldSignedLocalizedPotentialShear I eta v) :=
  memBlockL2_blockField MemLp.zero (lemmaVPlanarRowField_memL2 I eta v heta hdeta).neg

/-- Exact shear gauge difference is an admissible parent variation. This
keeps the full boundary flux, rather than identifying the two fields pointwise. -/
theorem old_signed_localized_physical_shear_variation (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (eta v : H1Function (openCubeSet Q))
    (hres : MemH10 (openCubeSet Q) (v-I v).toFun)
    (heta : MemLp eta.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hdeta : ∀ i,MemLp (fun x => eta.grad x i) ⊤ (volume.restrict (openCubeSet Q))) :
    ScalarVariation (openCubeSet Q) (fun x => oldSignedLocalizedPotentialShear I eta v x-
      oldSignedPhysicalPotentialShear eta v x) := by
  have hdiv := localizedColumnProductDivergence_memL2 eta (v-I v) heta hdeta
  have hs := isSolenoidalZeroNormalTraceOn_smul
    (localizedColumnProductDivergence_solenoidal (isOpenBoundedConvexDomain_openCubeSet Q)
      eta (v-I v) hres heta hdeta) (-1)
  have he : (fun x => oldSignedLocalizedPotentialShear I eta v x-
      oldSignedPhysicalPotentialShear eta v x)=
      fun x => (0,(-1:ℝ) • localizedColumnProductDivergence eta (v-I v) x) := by
    have hi := localizedColumnProductDivergence_row_identity I eta v
    funext x
    apply Prod.ext
    · simp only [oldSignedLocalizedPotentialShear,oldSignedPhysicalPotentialShear,Prod.fst_sub,sub_zero]
    · have hx := congrFun hi x
      change -lemmaVPlanarRowField I eta v x-(-(eta x • matVecMul responsePlanarJ (v.grad x)))=_
      rw [←hx]
      module
  rw [he]
  have hn : MemVectorL2 (openCubeSet Q) (fun x => (-1:ℝ) •
      localizedColumnProductDivergence eta (v-I v) x) := by
    convert hdiv.const_smul (-1) using 1
    funext x
    simp only [Pi.smul_apply,neg_one_smul]
  refine ⟨memBlockL2_blockField MemLp.zero hn,isPotentialZeroTraceOn_zero,?_⟩
  convert hs using 1

end
end ASDExplicitGamma.Native
