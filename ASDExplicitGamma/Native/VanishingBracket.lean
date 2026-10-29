module

public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Inverse.AnchorAdapter
public import ASDExplicitGamma.Variational.AdapterShearTrace
public import ASDExplicitGamma.Variational.LemmaVH2Band
public import ASDExplicitGamma.Variational.LemmaVH2ClosedBandRemainder
public import ASDExplicitGamma.Variational.LemmaVH2ClosedSingle
public import ASDExplicitGamma.Gaussian.ModelHeatTrace

/-! # Native use of the vanishing remainder bracket -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Model
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

/- The model-facing name for the fixed completed-label trace. This is the
literal cutoff observable in the true frame supplied by the adapter. -/

/-- The frozen trace along a constant physical shear is the exact quadratic
response formula in the same true frame. -/
theorem nativeTraceDefect_constantShear
    {Q : TriadicCube 2} (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (κ : Vec 2 → ℝ) {Λ : ℝ}
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (κ x))) (g : ℝ) :
    traceDefect (cubeSet Q)
      (fun x => responsePlanarCoefficient ν (κ x + g)) σ =
      traceDefect (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x)) σ +
        2 * (g / σ) * Variational.shearTraceLinear
          (coarseBlockMatrix (cubeSet Q) (fun x => responsePlanarCoefficient ν (κ x))) +
        g ^ 2 * (Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (fun x => responsePlanarCoefficient ν (κ x)))).lowerRight / σ ^ 2) := by
  exact Variational.traceDefect_constantSkew_physical ν σ hν hσ κ hEll g

/-- The actual frozen-frame constant-shear rows: the trace defect is
nonnegative, its quadratic shear coefficient is positive, and its signed
linear coefficient satisfies the exact discriminant bound. -/
theorem nativeTraceShearDefectRows (Q : TriadicCube 2) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (cubeSet Q)) :
    let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)
    let T := traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ
    let D := Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2
    let z := Variational.shearTraceLinear A / σ
    0 ≤ T ∧ 0 < D ∧ z ^ 2 ≤ D * T ∧
      (∀ g : ℝ, traceDefect (cubeSet Q)
          (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + g)) σ =
        T + 2 * g * z + g ^ 2 * D) := by
  let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)
  let T := traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ
  let D := Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2
  let z := Variational.shearTraceLinear A / σ
  have hEll := responsePlanarCoefficientField_isElliptic
    (measurableSet_cubeSet Q) ν hν k
  have hT : 0 ≤ T := by
    dsimp [T]
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube hν hEll hσ
  have hApos := Variational.coarseBlockMatrix_posDef hν hEll
  have hdiag0 : 0 < A.lowerRight 0 0 := by
    have h := hApos.diag_pos (i := Sum.inr (0 : Fin 2))
    simpa [A, toFullBlockMat] using h
  have hdiag1 : 0 < A.lowerRight 1 1 := by
    have h := hApos.diag_pos (i := Sum.inr (1 : Fin 2))
    simpa [A, toFullBlockMat] using h
  have htrace : 0 < Matrix.trace A.lowerRight := by
    simpa [Matrix.trace, Fin.sum_univ_two] using add_pos hdiag0 hdiag1
  have hD : 0 < D := by
    dsimp [D, A]
    rw [frameMatrix, Matrix.trace_smul]
    exact div_pos (mul_pos hσ htrace) (sq_pos_of_pos hσ)
  have hlinear := Variational.shearTraceLinear_sq_le Q ν σ hν hσ k
  have hz : z ^ 2 ≤ D * T := by
    have hdiv := div_le_div_of_nonneg_right hlinear (sq_nonneg σ)
    dsimp [z, D]
    rw [div_pow]
    calc
      Variational.shearTraceLinear A ^ 2 / σ ^ 2 ≤
          Matrix.trace (frameMatrix σ A).lowerRight * T / σ ^ 2 := hdiv
      _ = (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) * T := by
          field_simp [hσ.ne']
  have hshear (g : ℝ) :
      traceDefect (cubeSet Q)
        (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + g)) σ =
        T + 2 * g * z + g ^ 2 * D := by
    have h := nativeTraceDefect_constantShear ν σ hν hσ
      (responseCoefficientExtension k) hEll g
    have hfield : responsePlanarCoefficientField ν k =
        (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x)) := rfl
    convert h using 1
    dsimp [T, A, D, z]
    rw [hfield]
    ring_nf
  exact ⟨hT, hD, hz, hshear⟩

/-- The remainder-family form of Lemma V at a fixed completed true frame.
It gives the finite directional estimate and the complete Gaussian square
bracket, with its vanishing factor equal to the frozen trace defect. The
coefficient `k` is arbitrary, so the same theorem applies at every
constant-sheared coefficient used by the backward-heat consumer. -/
theorem nativeRemainderTraceBracket (m : ℤ) (j : ℕ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (H : ℕ → ResponseCoefficient (openCubeSet (originCube 2 m)))
    (η : ℕ → PlanarW2Infinity (originCube 2 m))
    (vB LB : ℝ)
    (hrep : RepresentsQ3Remainder η vB LB (cubeCenter (originCube 2 m)))
    (hvB : 0 ≤ vB) (hLB : 0 < LB)
    (hlink : ∀ l, (η l).value.toFun =ᵐ[volume.restrict (openCubeSet (originCube 2 m))]
      fun x => responseCoefficientExtension (H l) x / σ) :
    let Q := originCube 2 m
    let κ := Real.sqrt vB *
      lemmaVH2Bn (cubeScaleFactor Q / LB) (diagMeshRadius Q j / LB)
    (∀ (s : Finset ℕ) (c : ℕ → ℝ), (∑ l ∈ s, c l ^ 2) ≤ 1 →
      |fderiv ℝ (lemmaVTrace m ν σ) k (∑ l ∈ s, c l • H l)| ≤
        2 * κ * lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k) *
          Real.sqrt (lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4)) *
            Real.sqrt (∑ l ∈ s, c l ^ 2)) ∧
    Summable (fun l : ℕ => (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ∧
    (∑' l : ℕ, (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ≤
      4 * κ ^ 2 * (lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)) ^ 2 *
        lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4) := by
  exact lemmaV_diag_remainder m j ν σ hν hσ k H η vB LB hrep hvB hLB hlink

/-- The covariance-defect single-direction Lemma V route at the same true
frame. -/
theorem nativeSingleTraceBracket (m : ℤ) (j : ℕ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) {L : ℝ}
    (hL : 0 < L)
    (H : ℕ → ResponseCoefficient (openCubeSet (originCube 2 m)))
    (hlink : ∀ l, (q3CovarianceDefectFamily (originCube 2 m) L l).value.toFun
      =ᵐ[volume.restrict (openCubeSet (originCube 2 m))]
        fun x => responseCoefficientExtension (H l) x / σ) :
    let Q := originCube 2 m
    let κ := lemmaVH2kn (cubeScaleFactor Q / L) (diagMeshRadius Q j / L)
    (∀ (s : Finset ℕ) (c : ℕ → ℝ), (∑ l ∈ s, c l ^ 2) ≤ 1 →
      |fderiv ℝ (lemmaVTrace m ν σ) k (∑ l ∈ s, c l • H l)| ≤
        2 * κ * lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k) *
          Real.sqrt (lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4)) *
            Real.sqrt (∑ l ∈ s, c l ^ 2)) ∧
    Summable (fun l : ℕ => (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ∧
    (∑' l : ℕ, (fderiv ℝ (lemmaVTrace m ν σ) k (H l)) ^ 2) ≤
      4 * κ ^ 2 * (lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)) ^ 2 *
        lemmaVTrace m ν σ k * (lemmaVTrace m ν σ k + 4) := by
  exact lemmaV_diag_single m j ν σ hν hσ k hL H hlink

/-- One-shell assembly of the constant, covariance-defect, and nonconstant
remainder pieces in the exact source shear identity. The last two estimates
are precisely the outputs supplied by the two Lemma V adapters above. -/
theorem nativeConstantRemainderShellBracket_le
    (v κf κB B T F D z df ΓR : ℝ)
    (hv : 0 ≤ v) (hκf : 0 ≤ κf)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hF : 0 ≤ F) (hD : 0 ≤ D)
    (hFdef : F = T + 4)
    (hz : z ^ 2 ≤ D * T)
    (hdf : df ^ 2 ≤ 4 * κf ^ 2 * B ^ 2 * T * F)
    (hrem : ΓR ≤ 4 * v * κB ^ 2 * B ^ 2 * T * F) :
    v * (2 * z) ^ 2 + 2 * v * (2 * z) * df + ΓR ≤
      4 * v * T * ((1 + κf) * D + (κB ^ 2 + κf) * B ^ 2 * F) := by
  have hDT : 0 ≤ D * T := mul_nonneg hD hT
  have hTF : 0 ≤ T * F := mul_nonneg hT hF
  have hzabs : |z| ≤ Real.sqrt (D * T) := by
    have hs := Real.sqrt_le_sqrt hz
    rw [Real.sqrt_sq_eq_abs] at hs
    exact hs
  have hdfabs : |df| ≤ 2 * κf * B * Real.sqrt (T * F) := by
    have hs := Real.sqrt_le_sqrt hdf
    rw [Real.sqrt_sq_eq_abs,
      show 4 * κf ^ 2 * B ^ 2 * T * F = (2 * κf * B) ^ 2 * (T * F) by ring,
      Real.sqrt_mul (sq_nonneg (2 * κf * B)),
      Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) hκf) hB)] at hs
    exact hs
  have hsqrtprod : Real.sqrt (D * T) * Real.sqrt (T * F) =
      T * Real.sqrt (D * F) := by
    rw [Real.sqrt_mul hD, Real.sqrt_mul hT]
    calc
      (Real.sqrt D * Real.sqrt T) * (Real.sqrt T * Real.sqrt F) =
          Real.sqrt D * (Real.sqrt T) ^ 2 * Real.sqrt F := by ring
      _ = Real.sqrt D * T * Real.sqrt F := by rw [Real.sq_sqrt hT]
      _ = T * Real.sqrt (D * F) := by
            rw [Real.sqrt_mul hD]
            ring
  have hYoung : 2 * B * Real.sqrt (D * F) ≤ D + B ^ 2 * F := by
    have hs := sq_nonneg (Real.sqrt D - B * Real.sqrt F)
    have heq : Real.sqrt (D * F) = Real.sqrt D * Real.sqrt F := Real.sqrt_mul hD F
    rw [heq]
    nlinarith [hs, Real.sq_sqrt hD, Real.sq_sqrt hF]
  have hcross : 2 * v * (2 * z) * df ≤
      4 * v * κf * T * (D + B ^ 2 * F) := by
    have hzdf : z * df ≤ |z| * |df| := by
      calc
        z * df ≤ |z * df| := le_abs_self _
        _ = |z| * |df| := abs_mul z df
    have hproduct : |z| * |df| ≤
        Real.sqrt (D * T) * (2 * κf * B * Real.sqrt (T * F)) := by
      calc
        |z| * |df| ≤ |z| * (2 * κf * B * Real.sqrt (T * F)) :=
          mul_le_mul_of_nonneg_left hdfabs (abs_nonneg z)
        _ ≤ Real.sqrt (D * T) * (2 * κf * B * Real.sqrt (T * F)) :=
          mul_le_mul_of_nonneg_right hzabs (by positivity)
    calc
      2 * v * (2 * z) * df = 4 * v * (z * df) := by ring
      _ ≤ 4 * v * (|z| * |df|) := mul_le_mul_of_nonneg_left hzdf (by positivity)
      _ ≤ 4 * v * (Real.sqrt (D * T) *
            (2 * κf * B * Real.sqrt (T * F))) :=
              mul_le_mul_of_nonneg_left hproduct (by positivity)
      _ = 8 * v * κf * B * T * Real.sqrt (D * F) := by
        calc
          4 * v * (Real.sqrt (D * T) *
              (2 * κf * B * Real.sqrt (T * F))) =
              8 * v * κf * B * (Real.sqrt (D * T) * Real.sqrt (T * F)) := by ring
          _ = _ := by rw [hsqrtprod]; ring
      _ ≤ 4 * v * κf * T * (D + B ^ 2 * F) := by
            calc
              8 * v * κf * B * T * Real.sqrt (D * F) =
                  (4 * v * κf * T) * (2 * B * Real.sqrt (D * F)) := by ring
              _ ≤ (4 * v * κf * T) * (D + B ^ 2 * F) :=
                mul_le_mul_of_nonneg_left hYoung (by positivity)
              _ = _ := by ring
  have hconst : v * (2 * z) ^ 2 ≤ 4 * v * D * T := by
    nlinarith [mul_le_mul_of_nonneg_left hz hv]
  calc
    v * (2 * z) ^ 2 + 2 * v * (2 * z) * df + ΓR ≤
        4 * v * D * T +
          4 * v * κf * T * (D + B ^ 2 * F) +
          4 * v * κB ^ 2 * B ^ 2 * T * F := by
            exact add_le_add (add_le_add hconst hcross) hrem
    _ = 4 * v * T * ((1 + κf) * D + (κB ^ 2 + κf) * B ^ 2 * F) := by
          rw [hFdef]
          ring

end ASDExplicitGamma.Native
