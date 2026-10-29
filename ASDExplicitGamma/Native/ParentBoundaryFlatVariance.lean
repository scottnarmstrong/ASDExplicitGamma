module

public import ASDExplicitGamma.Main.FlatFieldCellGeometry
public import ASDExplicitGamma.Native.OldSignedFlatJointL2
public import ASDExplicitGamma.Triadic.HilbertHaarOrthogonal

/-! Actual flat-source cell variances at arbitrary shell wavelength,
with the complete mode trace and sharp cell Poincare factor retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic
noncomputable section

/-- The genuine four-coordinate flat H1 field, before applying the source sign. -/
def parentBoundaryFlatH1 (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l})
    (plus : Bool) (i : whiteBasisIndex) :
    HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ (Fin 2 × Fin 2)) :=
  if plus then mainFlatPlusH1 Q b L i else mainFlatMinusH1 Q b L i

/-- The actual complete spatial variance loss of one signed flat family. -/
def parentBoundaryFlatVariance (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) : ℝ :=
  ∑' i : whiteBasisIndex,descendantsAverage Q depth (fun U =>
    hilbertEnergy U (fun x => (parentBoundaryFlatH1 Q b L plus i).toFun x-
      hilbertCubeAverage U (parentBoundaryFlatH1 Q b L plus i).toFun))

/-- Both complete physical variance losses are summable and obey their
sharp H1 traces at ANY positive shell wavelength. -/
theorem parent_boundary_flat_variance_bound (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool) :
    Summable (fun i : whiteBasisIndex => descendantsAverage Q depth (fun U =>
      hilbertEnergy U (fun x => (parentBoundaryFlatH1 Q b L plus i).toFun x-
        hilbertCubeAverage U (parentBoundaryFlatH1 Q b L plus i).toFun))) ∧
    parentBoundaryFlatVariance Q depth b L plus≤
      (cubeScaleFactor Q/(Real.pi*(3:ℝ)^depth))^2*
        ((if plus then (1+Real.sqrt 2)^2 else 1)*mainFlatSigmaSq b L) := by
  cases plus
  · have htrace := mainFlatMinusGradientEnergy_tsum Q b L
    have hh := main_hilbert_cell_variance_le_gradient_tsum Q depth (fun i => mainFlatMinusH1 Q b L i) htrace.1
    rw [htrace.2] at hh
    simpa [parentBoundaryFlatH1,parentBoundaryFlatVariance] using hh
  · have htrace := mainFlatPlusGradientEnergy_tsum Q b L
    have hh := main_hilbert_cell_variance_le_gradient_tsum Q depth (fun i => mainFlatPlusH1 Q b L i) htrace.1
    refine ⟨by simpa [parentBoundaryFlatH1] using hh.1,?_⟩
    exact hh.2.trans (mul_le_mul_of_nonneg_left htrace.2 (sq_nonneg _))

/-- The two physical flat variance losses have exactly the source's
(4+2sqrt(2)) cell charge at arbitrary shell wavelength. -/
theorem parent_boundary_joint_flat_variance_bound (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    parentBoundaryFlatVariance Q depth b L true+parentBoundaryFlatVariance Q depth b L false≤
      (4+2*Real.sqrt 2)*(cubeScaleFactor Q/(Real.pi*(3:ℝ)^depth))^2*mainFlatSigmaSq b L := by
  have hp := (parent_boundary_flat_variance_bound Q depth b L true).2
  have hm := (parent_boundary_flat_variance_bound Q depth b L false).2
  simp only [ite_true,Bool.false_eq_true,ite_false,one_mul] at hp hm
  have he : (1+Real.sqrt 2)^2+1=4+2*Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  apply (add_le_add hp hm).trans_eq
  calc
    _ = ((1+Real.sqrt 2)^2+1)*(cubeScaleFactor Q/(Real.pi*(3:ℝ)^depth))^2*mainFlatSigmaSq b L := by ring
    _ = _ := by rw [he]

/-- Exact Hilbert cell variance identity on the actual normalized cube. -/
theorem parent_boundary_hilbert_cell_variance_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (U : TriadicCube 2) (F : Vec 2 → E) (hF : MemLp F 2 (normalizedCubeMeasure U)) :
    hilbertEnergy U (fun x => F x-hilbertCubeAverage U F)=hilbertEnergy U F-‖hilbertCubeAverage U F‖^2 := by
  have hp := hilbert_projection_residual_energy U 0 hF
  have hproj (x) (hx : x∈cubeSet U) : hilbertCubeProjection U 0 F x=hilbertCubeAverage U F :=
    hilbertCubeProjection_eq_average U 0 F (by simp [descendantsAtDepth_zero]) hx
  have he : hilbertEnergy U (hilbertCubeProjection U 0 F)=‖hilbertCubeAverage U F‖^2 :=
    (hilbertEnergy_congr_on U hproj).trans (hilbertEnergy_const U _)
  have hr : hilbertEnergy U (fun x => F x-hilbertCubeProjection U 0 F x)=
      hilbertEnergy U (fun x => F x-hilbertCubeAverage U F) :=
    hilbertEnergy_congr_on U (fun x hx => by rw [hproj x hx])
  rw [he,hr] at hp
  linarith only [hp]

end
end ASDExplicitGamma.Native
