module

public import ASDExplicitGamma.Variational.LocalizedShearWeak

/-! The interpolant lift with the weak column divergence. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section

/-- For any linear interpolant, the zero-trace residual produces the weak
column-divergence lift and the exact all-test pairing identity. -/
theorem lemmaV_interpolant_lift_source {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpenBoundedConvexDomain U)
    (I : H1Function U →ₗ[ℝ] H1Function U) (v η w : H1Function U)
    (hres : MemH10 U (v-I v).toFun)
    (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal) (volume.restrict U)) :
    MemVectorL2 U (localizedColumnProductDivergence η (v-I v)) ∧
    IsSolenoidalZeroNormalTraceOn U (localizedColumnProductDivergence η (v-I v)) ∧
    (∀ x, localizedColumnProductDivergence η (v-I v) x =
      (v-I v).toFun x • lemmaVPlanarWeakColumnDivergence η x -
        η.toFun x • matVecMul responsePlanarJ ((v-I v).grad x)) ∧
    volumeAverage U (fun x => vecDot
      (η.toFun x • matVecMul responsePlanarJ (v.grad x)) (w.grad x)) =
    volumeAverage U (fun x => vecDot (lemmaVPlanarRowField I η v x) (w.grad x)) := by
  refine ⟨localizedColumnProductDivergence_memL2 η (v-I v) hη hDη,
    localizedColumnProductDivergence_solenoidal hU η (v-I v) hres hη hDη, ?_, ?_⟩
  · intro x
    rfl
  · exact lemmaV_pairing_lift_of_interpolant hU I v η w hres hη hDη

end
end ASDExplicitGamma.Variational
