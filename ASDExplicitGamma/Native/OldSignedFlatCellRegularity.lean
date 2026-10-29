module

public import ASDExplicitGamma.Native.OldSignedFlatProfiles

/-! Both blocks of each actual flat input supply the centered Haar
summability needed by the weighted cell projection estimates. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic
noncomputable section

/-- Either physical flat input remains L2 on each chosen child cell. -/
theorem old_signed_flat_input_cell_memL2 (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    MemBlockL2 (openCubeSet U) (oldSignedFlatInput Q b L plus n i) := by
  have hs := Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  cases plus
  · exact (old_signed_flat_minus_block_memL2 Q b L n i).mono_measure hs
  · exact (old_signed_flat_plus_block_memL2 Q b L n i).mono_measure hs

/-- Every first-block coordinate has its genuine centered positive
Haar increments, including the identically zero plus block. -/
theorem old_signed_flat_input_cell_first_positive (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) (c : Vec 2) (j : Fin 2) :
    Summable (fun d : ℕ => (Real.sqrt 3)^(d+1)*energy U
      (cubeIncrement U (d+1) (fun x => (oldSignedFlatInput Q b L plus n i x).1 j-c j))) := by
  cases plus
  · exact old_signed_flat_minus_cell_centered_positive Q depth b L n i U hU c j
  · have hz := old_signed_centered_h1_vector_positive_summable U (fun _ => 0) c 0 j
    simpa [oldSignedFlatInput,oldSignedFlatPlusBlock] using hz

/-- Every second-block coordinate has the source's centered positive
Haar increments, including the identically zero minus block. -/
theorem old_signed_flat_input_cell_second_positive (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) (n : whiteBasisIndex) (i : Fin 2)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) (c : Vec 2) (j : Fin 2) :
    Summable (fun d : ℕ => (Real.sqrt 3)^(d+1)*energy U
      (cubeIncrement U (d+1) (fun x => (oldSignedFlatInput Q b L plus n i x).2 j-c j))) := by
  cases plus
  · have hz := old_signed_centered_h1_vector_positive_summable U (fun _ => 0) c 0 j
    simpa [oldSignedFlatInput,oldSignedFlatMinusBlock] using hz
  · exact old_signed_flat_plus_cell_centered_positive Q depth b L n i U hU c j

end
end ASDExplicitGamma.Native
