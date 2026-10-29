module

public import ASDExplicitGamma.Native.ParentBoundaryBandCellIntegrable
public import ASDExplicitGamma.Native.OldSignedDirectionalIntegral

/-! The actual common-band directional half-trace identity on every
translated source cell, with all entry moments proved beforehand. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Actual two-block directional surplus in the unchanged starting frame. -/
def parentBoundaryBandSurplus (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (U : TriadicCube 2) (omega : Cutoff.CutoffSample 2) : Mat 2 :=
  let A := frameMatrix (Annealed.sigmaBar M n) (coarseBlockMatrix (cubeSet U)
    (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega))
  A.upperLeft+A.lowerRight-(2:ℝ) • (1:Mat 2)

private theorem framed_entry_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) depth)
    (alpha beta : BlockCoord 2) (t : ℝ) :
    Integrable (fun omega : Cutoff.CutoffSample 2 => blockMatEntry
      (frameMatrix (Annealed.sigmaBar M n) (coarseBlockMatrix (cubeSet U)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega))) alpha beta)
      (Cutoff.cutoffSampleLaw M).toMeasure :=
  (parent_boundary_band_cell_entry_memLp M h hM n height hheight depth U hU alpha beta t 2
    (by norm_num)).integrable (by norm_num)

/-- Every literal surplus entry is integrable under the actual band law. -/
theorem parent_boundary_band_surplus_entry_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) depth)
    (t : ℝ) (i j : Fin 2) :
    Integrable (fun omega => parentBoundaryBandSurplus M n height t U omega i j)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hp := framed_entry_integrable M h hM n height hheight depth U hU (.inl i) (.inl j) t
  have hm := framed_entry_integrable M h hM n height hheight depth U hU (.inr i) (.inr j) t
  convert (hp.add hm).sub (integrable_const ((2:ℝ)*(1:Mat 2) i j)) using 1
  funext omega
  simp only [parentBoundaryBandSurplus,blockMatEntry,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.add_apply]

/-- The complete physical directional mean is one half of the expected
trace, on the same source cell and simultaneous law. No directional,
integrability, isotropy or independence premise is supplied by a consumer. -/
theorem parent_boundary_band_directional_half_trace
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (hheight : 1≤height) (depth : ℕ)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) depth)
    (t : ℝ) (e : Vec 2) :
    (∫ omega,vecDot e (matVecMul (parentBoundaryBandSurplus M n height t U omega) e)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      (1/2:ℝ)*(∫ omega,traceDefect (cubeSet U)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega)
        (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure)*vecNormSq e := by
  let sigma : ℝ := Annealed.sigmaBar M n
  let A := fun omega : Cutoff.CutoffSample 2 => frameMatrix sigma (coarseBlockMatrix (cubeSet U)
    (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega))
  let N := parentBoundaryBandSurplus M n height t U
  let law := (Cutoff.cutoffSampleLaw M).toMeasure
  have hUL (i j : Fin 2) : Integrable (fun omega => (A omega).upperLeft i j) law :=
    framed_entry_integrable M h hM n height hheight depth U hU (.inl i) (.inl j) t
  have hLR (i j : Fin 2) : Integrable (fun omega => (A omega).lowerRight i j) law :=
    framed_entry_integrable M h hM n height hheight depth U hU (.inr i) (.inr j) t
  obtain ⟨cp,hcp⟩ := parent_boundary_band_expected_cell_block M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) U true
  obtain ⟨cm,hcm⟩ := parent_boundary_band_expected_cell_block M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) U false
  have hmeanUL (i j : Fin 2) : (∫ omega,(A omega).upperLeft i j ∂law)=
      if i=j then sigma⁻¹*cp else 0 := by
    change (∫ omega,sigma⁻¹*parentBoundaryBandDiagonalBlock M n (n+(height:ℤ))
      (fun _ => Real.sqrt t) U true omega i j ∂law)=_
    rw [integral_const_mul,hcp]
    split_ifs <;> simp
  have hmeanLR (i j : Fin 2) : (∫ omega,(A omega).lowerRight i j ∂law)=
      if i=j then sigma*cm else 0 := by
    change (∫ omega,sigma*parentBoundaryBandDiagonalBlock M n (n+(height:ℤ))
      (fun _ => Real.sqrt t) U false omega i j ∂law)=_
    rw [integral_const_mul,hcm]
    split_ifs <;> simp
  let c := sigma⁻¹*cp+sigma*cm-2
  have hmean (i j : Fin 2) : (∫ omega,N omega i j ∂law)=if i=j then c else 0 := by
    simp only [N,parentBoundaryBandSurplus,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    change (∫ omega,(A omega).upperLeft i j+(A omega).lowerRight i j-(2:ℝ)*(1:Mat 2) i j ∂law)=_
    have hsum : Integrable (fun omega => (A omega).upperLeft i j+(A omega).lowerRight i j) law := by
      simpa only [Pi.add_def] using (hUL i j).add (hLR i j)
    rw [integral_sub hsum (integrable_const _),
      integral_add (hUL i j) (hLR i j),hmeanUL,hmeanLR]
    simp only [integral_const,probReal_univ,one_smul]
    by_cases hij : i=j <;> simp [hij,Matrix.one_apply,c]
  have hint (i j : Fin 2) : Integrable (fun omega => N omega i j) law :=
    parent_boundary_band_surplus_entry_integrable M h hM n height hheight depth U hU t i j
  have htrace : (∫ omega,traceDefect (cubeSet U)
      (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega) sigma ∂law)=2*c := by
    have he (omega : Cutoff.CutoffSample 2) : traceDefect (cubeSet U)
        (attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) omega) sigma=
        N omega 0 0+N omega 1 1 := by
      simp [N,parentBoundaryBandSurplus,traceDefect,frameMatrix,Matrix.trace,Fin.sum_univ_two,sigma]
      ring
    simp_rw [he]
    rw [integral_add (hint 0 0) (hint 1 1),hmean,hmean]
    simp
    ring
  rw [old_signed_integral_scalar_quadratic law N hint c hmean e,htrace]
  ring

end
end ASDExplicitGamma.Native
