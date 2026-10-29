module

public import ASDExplicitGamma.Triadic.DiagEstimates
public import ASDExplicitGamma.Variational.LemmaVLoadBounds

/-! DIAG estimates in Lemma V's exact affine-potential and source-load carriers. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic

noncomputable section

/-- Every source affine-data potential has the exact DIAG residual, all three
sharp bounds, and finite tile-gradient positive series. -/
theorem lemmaV_diag_interpolant_estimates (m : ℤ) (j : ℕ) (p : Vec 2)
    (r : H10Function (openCubeSet (originCube 2 m))) :
    let Q := originCube 2 m
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r
    MemH10 (openCubeSet Q) (v-diagInterpolant Q j v).toFun ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j v).grad) ≤
      Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad) ∧
    Real.sqrt (diagTiledScalarPositiveEnergy Q j (v-diagInterpolant Q j v).toFun) ≤
      diagMeshRadius Q j*(2/Real.pi+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad) ∧
    Real.sqrt (energy Q (v-diagInterpolant Q j v).toFun) ≤
      diagMeshRadius Q j*(planarC0+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad) ∧
    ∀ R ∈ descendantsAtDepth Q j, ∀ i,
      Summable (fun n => (Real.sqrt 3)^(n+1)*energy R
        (cubeIncrement R (n+1) (fun x => (diagInterpolant Q j v).grad x i))) := by
  intro Q v
  exact ⟨diagInterpolant_affine_residual_memH10 Q j p r,
    diagInterpolant_gradient_estimate Q j p r,
    diagInterpolant_residual_positive_estimate Q j p r,
    diagInterpolant_residual_L2_estimate Q j p r,
    diagInterpolant_gradient_summable Q j p r⟩

/-- Actual signed source-load potentials retain their response/weak bounds
and obey the three sharp concrete interpolation estimates. -/
theorem lemmaV_load_diag_estimates (m : ℤ) (j : ℕ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (i : Fin 2) (b : Bool) :
    let Q := originCube 2 m
    let U := openCubeSet Q
    let hU := isOpenBoundedConvexDomain_openCubeSet Q
    let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) m
    let a := responseFramePlanarCoefficientField ν σ k
    let P := orthonormalFrameLoad i (lemmaVLoadSign b)
    let E := responseFrameEnergyObservable hU.isOpen.measurableSet hv ν σ hν hσ P
    let B := lemmaVTileHistory Q j a
    ∃ r : H10Function U, ∃ w : H1Function U,
      (lemmaVTiledWeakEnergy Q j w.grad ≤ B*(E k-1)) ∧
      (lemmaVTiledWeakEnergy Q j (lemmaVAffinePotential hU P.1 r).grad ≤ B*E k) ∧
      (0 ≤ E k-1) ∧
      (∀ H : ResponseCoefficient U, fderiv ℝ E k H =
        2*lemmaVLoadSign b*volumeAverage U (fun x => vecDot
          ((responseCoefficientExtension H x/σ) • matVecMul responsePlanarJ
            ((lemmaVAffinePotential hU P.1 r).grad x)) (w.grad x))) ∧
      (let v := lemmaVAffinePotential hU P.1 r;
        Real.sqrt (lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j v).grad) ≤
          Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad)) ∧
      (let v := lemmaVAffinePotential hU P.1 r;
        Real.sqrt (diagTiledScalarPositiveEnergy Q j (v-diagInterpolant Q j v).toFun) ≤
          diagMeshRadius Q j*(2/Real.pi+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad)) ∧
      (let v := lemmaVAffinePotential hU P.1 r;
        Real.sqrt (energy Q (v-diagInterpolant Q j v).toFun) ≤
          diagMeshRadius Q j*(planarC0+1/2)*Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad)) := by
  intro Q U hU hv a P E B
  obtain ⟨r, w, hw, hv, hpos, hder⟩ := lemmaV_load_bounds m j ν σ hν hσ k i b
  exact ⟨r, w, hw, hv, hpos, hder,
    diagInterpolant_gradient_estimate Q j P.1 r,
    diagInterpolant_residual_positive_estimate Q j P.1 r,
    diagInterpolant_residual_L2_estimate Q j P.1 r⟩

end

end ASDExplicitGamma.Variational
