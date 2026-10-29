module

public import ASDExplicitGamma.Native.OldSignedFlatL2Profiles
public import ASDExplicitGamma.Native.OldSignedCellAverage
public import ASDExplicitGamma.Native.OldSignedFlatBoundaryEnergy

/-! The full physical flat L2 baseline partitions exactly. This is the
baseline which cancels with the negative Dirichlet tangent in AN (5.3). -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Triadic Main
noncomputable section

/-- Exact equal-volume decomposition of the physical doubled L2 energy. -/
theorem old_signed_block_l2_partition (Q : TriadicCube 2) (depth : ℕ)
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) :
    oldSignedBlockL2Energy Q F=
      descendantsAverage Q depth (fun U => oldSignedBlockL2Energy U F) := by
  have hf (j : Fin 2) := energy_eq_descendantsAverage Q depth
    (memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hF) j))
  have hg (j : Fin 2) := energy_eq_descendantsAverage Q depth
    (memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) j))
  unfold oldSignedBlockL2Energy
  simp_rw [hf,hg]
  rw [descendantsAverage_add,Homogenization.descendantsAverage_sum,
    Homogenization.descendantsAverage_sum]

/-- The actual full plus input is precisely the all-gradient flat energy. -/
theorem old_signed_flat_plus_l2_mode (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2,oldSignedBlockL2Energy Q (oldSignedFlatPlusBlock Q b L n i))=
      oldSignedFlatPlusModeEnergy Q b L n := by
  simp [oldSignedBlockL2Energy,oldSignedFlatPlusBlock,oldSignedFlatPlusModeEnergy,energy_const,energy_neg]

/-- The actual full minus input is precisely the Dirichlet flat energy. -/
theorem old_signed_flat_minus_l2_mode (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2,oldSignedBlockL2Energy Q (oldSignedFlatMinusBlock Q b L n i))=
      oldSignedFlatDirichletModeEnergy Q b L n := by
  simp [oldSignedBlockL2Energy,oldSignedFlatMinusBlock,oldSignedFlatDirichletModeEnergy,energy_const]

/-- The full L2 baseline of either flat family commutes with the physical
partition, before taking its complete fresh-mode sum. -/
theorem old_signed_flat_l2_mode_partition (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (n : whiteBasisIndex) :
    (∑ i : Fin 2,oldSignedBlockL2Energy Q (oldSignedFlatInput Q b L plus n i))=
      descendantsAverage Q depth (fun U => ∑ i : Fin 2,
        oldSignedBlockL2Energy U (oldSignedFlatInput Q b L plus n i)) := by
  have hF (i : Fin 2) : MemBlockL2 (openCubeSet Q) (oldSignedFlatInput Q b L plus n i) := by
    cases plus
    · exact old_signed_flat_minus_block_memL2 Q b L n i
    · exact old_signed_flat_plus_block_memL2 Q b L n i
  simp_rw [old_signed_block_l2_partition Q depth _ (hF _)]
  rw [Homogenization.descendantsAverage_sum]

end
end ASDExplicitGamma.Native
