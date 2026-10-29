module

public import ASDExplicitGamma.Native.OldSignedDirectionalIntegral

/-! Actual-law half-trace identity for the coarse directional majorant.
The scalar frame remains fixed throughout the partial insertion. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Main Algsuperdiff.Section3
noncomputable section

/-- The physical two-block directional surplus in a fixed scalar frame. -/
def oldSignedCoarseDirectionalMatrix (Q : TriadicCube 2) (a : CoeffField 2) (sigma : ℝ) : Mat 2 :=
  let A := coarseBlockMatrix (cubeSet Q) a
  sigma⁻¹ • A.upperLeft+sigma • A.lowerRight-(2 : ℝ) • (1 : Mat 2)

/-- Exact scalar expansion of the physical directional quadratic form. -/
theorem old_signed_coarse_directional_quadratic (Q : TriadicCube 2) (a : CoeffField 2)
    (sigma : ℝ) (e : Vec 2) :
    vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix Q a sigma) e)=
      sigma⁻¹*vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q) a).upperLeft e)+
      sigma*vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q) a).lowerRight e)-2*vecNormSq e := by
  simp [oldSignedCoarseDirectionalMatrix,vecDot,matVecMul,vecNormSq,Fin.sum_univ_two,Matrix.one_apply]
  ring

/-- The actual partial-law expected directional majorant is exactly one
half of the expected four-load trace times the squared deterministic load. -/
theorem old_signed_coarse_directional_mean (M : ABKModel 2) (m n : ℤ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (sigma : ℝ) (e : Vec 2) :
    (∫ a,vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix (originCube 2 n) a.toFun sigma) e)
      ∂mainInsertionCoefficientLaw M m t)=
    (1/2 : ℝ)*(∫ a,traceDefect (cubeSet (originCube 2 n)) a.toFun sigma
      ∂mainInsertionCoefficientLaw M m t)*vecNormSq e := by
  let μ := mainInsertionCoefficientLaw M m t
  let oldSignedDirectionalProbability : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff
      (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable).2 inferInstance
  let Q := originCube 2 n
  let K : RegCoeffField 2 → Mat 2 := fun a => (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft
  let D : RegCoeffField 2 → Mat 2 := fun a => (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight
  have hK (i j : Fin 2) : Integrable (fun a => K a i j) μ :=
    mainInsertionCoefficientLaw_integrable_blockMatEntry M m t ht Q (.inl i) (.inl j)
  have hD (i j : Fin 2) : Integrable (fun a => D a i j) μ :=
    mainInsertionCoefficientLaw_integrable_blockMatEntry M m t ht Q (.inr i) (.inr j)
  obtain ⟨u,v,hu,hv,hTu,hTv⟩ := mainInsertionCoefficientLaw_expectedBlockTrace_scalars M m n t ht
  have hKu := old_signed_integral_scalar_quadratic μ K hK u hu e
  have hDv := old_signed_integral_scalar_quadratic μ D hD v hv e
  have hiK := old_signed_quadratic_integrable μ K hK e
  have hiD := old_signed_quadratic_integrable μ D hD e
  have hKT : Integrable (fun a => Matrix.trace (K a)) μ := by
    simpa only [Matrix.trace_fin_two,Pi.add_def] using (hK 0 0).add (hK 1 1)
  have hDT : Integrable (fun a => Matrix.trace (D a)) μ := by
    simpa only [Matrix.trace_fin_two,Pi.add_def] using (hD 0 0).add (hD 1 1)
  have htrace : (∫ a,traceDefect (cubeSet Q) a.toFun sigma ∂μ)=sigma⁻¹*(2*u)+sigma*(2*v)-4 := by
    change (∫ a,sigma⁻¹*Matrix.trace (K a)+sigma*Matrix.trace (D a)-4 ∂μ)=_
    have hsum : Integrable (fun a => sigma⁻¹*Matrix.trace (K a)+sigma*Matrix.trace (D a)) μ := by
      simpa only [Pi.add_def] using (hKT.const_mul sigma⁻¹).add (hDT.const_mul sigma)
    rw [integral_sub hsum (integrable_const _),
      integral_add (hKT.const_mul _) (hDT.const_mul _),integral_const_mul,integral_const_mul,hTu,hTv]
    simp only [integral_const,probReal_univ,one_smul]
  change (∫ a,vecDot e (matVecMul (oldSignedCoarseDirectionalMatrix Q a.toFun sigma) e) ∂μ)=_
  simp_rw [old_signed_coarse_directional_quadratic]
  change (∫ a,sigma⁻¹*vecDot e (matVecMul (K a) e)+sigma*vecDot e (matVecMul (D a) e)-2*vecNormSq e ∂μ)=_
  have hsum : Integrable (fun a => sigma⁻¹*vecDot e (matVecMul (K a) e)+sigma*vecDot e (matVecMul (D a) e)) μ := by
    simpa only [Pi.add_def] using (hiK.const_mul sigma⁻¹).add (hiD.const_mul sigma)
  rw [integral_sub hsum (integrable_const _),
    integral_add (hiK.const_mul _) (hiD.const_mul _),integral_const_mul,integral_const_mul,hKu,hDv]
  change _=(1/2 : ℝ)*(∫ a,traceDefect (cubeSet Q) a.toFun sigma ∂μ)*vecNormSq e
  rw [htrace]
  simp only [integral_const,probReal_univ,one_smul]
  ring

end
end ASDExplicitGamma.Native
