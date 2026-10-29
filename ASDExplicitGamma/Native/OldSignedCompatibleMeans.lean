module

public import ASDExplicitGamma.Native.OldSignedCanonicalFullMean
public import ASDExplicitGamma.Variational.CompatibleCoercivity

/-! Compatible physical fields on actual child cells and their mean bound.
No zero boundary condition is imposed on a parent restriction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational
noncomputable section

/-- Restrict a genuine compatible field to an open child cell. -/
theorem old_signed_compatible_restrict (Q U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet Q) {F : Vec 2 → BlockVec 2}
    (hF : ScalarCompatible (openCubeSet Q) F) : ScalarCompatible (openCubeSet U) F := by
  have hm := hF.1.mono_measure (Measure.restrict_mono_set volume hU)
  exact ⟨hm,hF.2.1.restrict_of_isOpen_of_memVectorL2
    (isOpen_openCubeSet Q) (isOpen_openCubeSet U) hU (memVectorL2_fst_of_memBlockL2 hm),
    hF.2.2.restrict_of_isOpen_of_memVectorL2
    (isOpen_openCubeSet Q) (isOpen_openCubeSet U) hU (memVectorL2_snd_of_memBlockL2 hm)⟩

/-- Differences remain compatible, without any assertion about boundary traces. -/
theorem old_signed_compatible_sub {U : Set (Vec 2)} {F G : Vec 2 → BlockVec 2}
    (hF : ScalarCompatible U F) (hG : ScalarCompatible U G) : ScalarCompatible U (F-G) := by
  refine ⟨hF.1.sub hG.1,?_,?_⟩
  · simpa only [neg_one_smul,sub_eq_add_neg,Pi.add_def,Pi.neg_def,Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg] using
      isPotentialOn_add hF.2.1 (isPotentialOn_smul hG.2.1 (-1))
  · simpa only [neg_one_smul,sub_eq_add_neg,Pi.add_def,Pi.neg_def,Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg] using
      isSolenoidalOn_add_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF.1)
        ((memVectorL2_snd_of_memBlockL2 hG.1).const_smul (-1 : ℝ))
        hF.2.2 (isSolenoidalOn_smul hG.2.2 (-1))

end
end ASDExplicitGamma.Native
