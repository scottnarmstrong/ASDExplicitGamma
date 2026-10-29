module

public import ASDExplicitGamma.Native.OldSignedQ3SourceEnergy

/-! Complete quantitative control of the actual uncentered q3 source row.
The value column and both full derivative trace constants are retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- The OLD source multiplier k_a at the actual DIAG mesh radius. -/
def oldSignedSourceMultiplier (Q : TriadicCube 2) (mesh : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) : ℝ :=
  Real.sqrt (b^2)+diagMeshRadius Q mesh*(36/25)*Real.sqrt ((156/5)*b^2/L.1^2)+
    (diagMeshRadius Q mesh)^2*(57/200)*Real.sqrt ((46488/25)*b^2/L.1^4)

/-- The complete actual q3 row energy is summable and has the sharp
finite-family multiplier bound, with its uncentered value column included. -/
theorem old_signed_q3_row_energy_bound (n : ℤ) (b : ℝ) (L : {l : ℝ // 0<l})
    (mesh : ℕ) (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n))) :
    let Q := originCube 2 n
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Summable (pureFluxMainQ3RowEnergy n b 1 L mesh p u) ∧
      (∑' l,pureFluxMainQ3RowEnergy n b 1 L mesh p u l)≤
        oldSignedSourceMultiplier Q mesh b L^2*lemmaVTiledWeakEnergy Q mesh v.grad := by
  intro Q v
  refine ⟨old_signed_q3_row_energy_summable n b L mesh p u,?_⟩
  let Y := pureFluxMainQ3RowEnergy n b 1 L mesh p u
  have hY (l : whiteBasisIndex) : 0≤Y l :=
    descendantsAverage_nonneg Q mesh _ (fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hE : 0≤lemmaVTiledWeakEnergy Q mesh v.grad :=
    descendantsAverage_nonneg Q mesh _ (fun U _ => vectorWeakHaarEnergy_nonneg U _)
  have hcap (s : Finset whiteBasisIndex) : Real.sqrt (∑ l ∈ s,Y l)≤
      oldSignedSourceMultiplier Q mesh b L*Real.sqrt (lemmaVTiledWeakEnergy Q mesh v.grad) :=
    pureFluxMainQ3Row_trace_finset_sharp n b L mesh p u s
  have hC : 0≤oldSignedSourceMultiplier Q mesh b L*Real.sqrt (lemmaVTiledWeakEnergy Q mesh v.grad) := by
    simpa only [Finset.sum_empty,Real.sqrt_zero] using hcap ∅
  apply Real.tsum_le_of_sum_le hY
  intro s
  have hsum : 0≤∑ l ∈ s,Y l := Finset.sum_nonneg (fun l _ => hY l)
  have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) hC).mpr (hcap s)
  simpa only [Real.sq_sqrt hsum,mul_pow,Real.sq_sqrt hE] using hh

end
end ASDExplicitGamma.Native
