module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredTrace
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCoefficient

/-! Full centered basis trace with the exact bank source coefficient. -/

@[expose] public section
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Model ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
namespace ASDExplicitGamma.Inverse
noncomputable section
theorem pureFluxPlanarRowField_smul {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (η v : H1Function U) (c : ℝ) :
    lemmaVPlanarRowField I (c • η) v = fun x => c • lemmaVPlanarRowField I η v x := by
  funext x i
  fin_cases i <;>
    simp [lemmaVPlanarRowField, lemmaVPlanarWeakColumnDivergence, H1Function.smul_toFun,
      H1Function.smul_grad, matVecMul, responsePlanarJ, Fin.sum_univ_two,
      Pi.smul_apply, smul_eq_mul] <;> ring

private theorem pureFluxCenteredSource_energy_smul (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) (c : ℝ) :
    energy Q (fun x => c * f x) = c ^ 2 * energy Q f := by
  rw [energy_eq_integral_sq, energy_eq_integral_sq]
  simp only [mul_pow]
  rw [integral_const_mul]

private theorem pureFluxCenteredSource_cubeIncrement_smul (Q : TriadicCube 2) (n : ℕ)
    (f : Vec 2 → ℝ) (c : ℝ) :
    cubeIncrement Q n (fun x => c * f x) = fun x => c * cubeIncrement Q n f x := by
  cases n with
  | zero => simp [cubeIncrement_zero, projection_smul]
  | succ n =>
      simp only [cubeIncrement_succ, projection_smul]
      funext x
      ring

theorem pureFlux_positive_series_smul (Q : TriadicCube 2) (f : Vec 2 → ℝ)
    (c : ℝ) (hP : Summable (fun k => (Real.sqrt 3)^(k+1) *
      energy Q (cubeIncrement Q (k+1) f))) :
    Summable (fun k => (Real.sqrt 3)^(k+1) *
      energy Q (cubeIncrement Q (k+1) (fun x => c * f x))) := by
  have heq (k : ℕ) : (Real.sqrt 3)^(k+1) *
      energy Q (cubeIncrement Q (k+1) (fun x => c * f x)) =
      c^2 * ((Real.sqrt 3)^(k+1) * energy Q (cubeIncrement Q (k+1) f)) := by
    rw [pureFluxCenteredSource_cubeIncrement_smul, pureFluxCenteredSource_energy_smul]
    ring
  rw [show (fun k => (Real.sqrt 3)^(k+1) *
      energy Q (cubeIncrement Q (k+1) (fun x => c * f x))) =
      fun k => c^2 * ((Real.sqrt 3)^(k+1) *
        energy Q (cubeIncrement Q (k+1) f)) by funext k; exact heq k]
  exact hP.mul_left _

private theorem pureFluxMainQ3CenteredBasisMultiplier_scale
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) :
    pureFluxMainQ3CenteredBasisMultiplier n b σ L l =
      (σ⁻¹ : ℝ) • pureFluxMainQ3CenteredBasisMultiplier n b 1 L l := by
  simp [pureFluxMainQ3CenteredBasisMultiplier]

private theorem pureFluxMainQ3CenteredRow_vectorEnergy_scale
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (U : TriadicCube 2) (l : whiteBasisIndex) :
    vectorPositiveHaarEnergy U (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3CenteredBasisMultiplier n b σ L l)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u)) =
      (σ⁻¹)^2 * vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
          (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l)
          (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u)) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q m
  let c := σ⁻¹
  have hη := pureFluxMainQ3CenteredBasisMultiplier_scale n b σ L l
  have hdiv (x : Vec 2) :
      lemmaVPlanarWeakColumnDivergence
          (c • pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) x =
        c • lemmaVPlanarWeakColumnDivergence
          (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) x := by
    simp only [lemmaVPlanarWeakColumnDivergence, H1Function.smul_grad,
      Pi.smul_apply]
    ext i
    simp [Homogenization.matVecMul, ASDExplicitGamma.Response.responsePlanarJ,
      Fin.sum_univ_two, smul_eq_mul]
    ring
  have hval (x : Vec 2) :
      (c • pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) x =
        c * (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) x := by
    simp [H1Function.smul_toFun, smul_eq_mul]
  have hfield : (fun x => lemmaVPlanarRowField I
        (pureFluxMainQ3CenteredBasisMultiplier n b σ L l) v x) =
      fun x => c • lemmaVPlanarRowField I
        (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) v x := by
    funext x
    rw [hη]
    simp only [lemmaVPlanarRowField]
    rw [hval, hdiv]
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring_nf
  have hcomponent (i : Fin 2) :
      (fun x => lemmaVPlanarRowField I
        (pureFluxMainQ3CenteredBasisMultiplier n b σ L l) v x i) =
        fun x => c * lemmaVPlanarRowField I
          (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) v x i := by
    funext x
    have hx := congrFun hfield x
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hx i
  unfold vectorPositiveHaarEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (fun x => lemmaVPlanarRowField I
      (pureFluxMainQ3CenteredBasisMultiplier n b σ L l) v x i) =
      fun x => c * lemmaVPlanarRowField I
        (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) v x i from hcomponent i]
  exact sensitivity_primalEnergy_smul U (Real.sqrt 3)
    (fun x => lemmaVPlanarRowField I
      (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) v x i) c

private theorem pureFluxMainQ3CenteredRowEnergy_scale
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (l : whiteBasisIndex) :
    pureFluxMainQ3CenteredRowEnergy n b σ L m p u l =
      (σ⁻¹)^2 * pureFluxMainQ3CenteredRowEnergy n b 1 L m p u l := by
  change descendantsAverage (originCube 2 n) m (fun U : TriadicCube 2 => vectorPositiveHaarEnergy U
      (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3CenteredBasisMultiplier n b σ L l)
        (lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u))) =
    (σ⁻¹)^2 * descendantsAverage (originCube 2 n) m (fun U => vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
          (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l)
          (lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u)))
  rw [show (fun U : TriadicCube 2 => vectorPositiveHaarEnergy U
      (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3CenteredBasisMultiplier n b σ L l)
        (lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u))) =
      fun U => (σ⁻¹)^2 * vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField (diagInterpolant (originCube 2 n) m)
          (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l)
          (lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u)) by
      funext U
      exact pureFluxMainQ3CenteredRow_vectorEnergy_scale n b σ L m p u U l]
  rw [descendantsAverage_mul_left]


/-- The actual centered source row is Hilbert--Schmidt on every aligned mesh,
with the exact normalized source coefficient and physical frame factor. -/
theorem pureFluxMainQ3_centered_row_trace_bound (n : ℤ) (q i m : ℕ)
    (b σ : ℝ) (L : {l : ℝ // 0 < l})
    (hρ : cubeScaleFactor (originCube 2 n)/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m/L.1 = pureFluxCovarianceDelta q i)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n))) :
    let Q := originCube 2 n
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Summable (pureFluxMainQ3CenteredRowEnergy n b σ L m p u) ∧
      Real.sqrt (∑' l, pureFluxMainQ3CenteredRowEnergy n b σ L m p u l) ≤
        |σ⁻¹| * |b| * pureFluxCovarianceA q i *
          Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let R := pureFluxMainQ3CenteredRowEnergy n b σ L m p u
  let C := |σ⁻¹| * |b| * pureFluxCovarianceA q i *
    Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)
  have hsharp (s : Finset whiteBasisIndex) :
      Real.sqrt (∑ l ∈ s, R l) ≤ C := by
    have hscale : (∑ l ∈ s, R l) =
        (σ⁻¹)^2 * ∑ l ∈ s, pureFluxMainQ3CenteredRowEnergy n b 1 L m p u l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => pureFluxMainQ3CenteredRowEnergy_scale n b σ L m p u l)
    have hbase := pureFluxMainQ3CenteredRow_trace_finset_sharp n b L m p u s
    have hc := pureFlux_centered_source_coefficient_eq q i b (cubeScaleFactor Q)
      (diagMeshRadius Q m) L.1 L.2 hρ hδ
    dsimp only at hbase
    rw [hc] at hbase
    rw [hscale, Real.sqrt_mul (sq_nonneg (σ⁻¹)), Real.sqrt_sq_eq_abs]
    simpa only [C, Q, v, mul_assoc] using
      mul_le_mul_of_nonneg_left hbase (abs_nonneg (σ⁻¹))
  have hRnonneg (l : whiteBasisIndex) : 0 ≤ R l := by
    unfold R pureFluxMainQ3CenteredRowEnergy descendantsAverage
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _
  have hC : 0 ≤ C := by
    have hA := le_trans (pureFlux_covariance_rows_order q i).1
      (pureFlux_covariance_rows_order q i).2
    exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hA)
      (Real.sqrt_nonneg _)
  have hfinite (s : Finset whiteBasisIndex) : ∑ l ∈ s, R l ≤ C^2 := by
    have hs0 : 0 ≤ ∑ l ∈ s, R l := Finset.sum_nonneg fun l _ => hRnonneg l
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hsharp s) 2
    rw [Real.sq_sqrt hs0] at hs
    exact hs
  have hsum : Summable R := summable_of_sum_le hRnonneg hfinite
  have htotal : ∑' l, R l ≤ C^2 := Real.tsum_le_of_sum_le hRnonneg hfinite
  exact ⟨hsum, (Real.sqrt_le_iff).2 ⟨hC, htotal⟩⟩

/-- Genuine positive-series membership for every physical centered source row. -/
theorem pureFluxMainQ3_centered_row_positive_series
    (n : ℤ) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet (originCube 2 n)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) m)
    (l : whiteBasisIndex) (i : Fin 2) :
    Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField
        (diagInterpolant (originCube 2 n) m)
        (pureFluxMainQ3CenteredBasisMultiplier n b σ L l)
        (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)) p u) x i))) := by
  let Q := originCube 2 n
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q m
  have hη := pureFluxMainQ3CenteredBasisMultiplier_scale n b σ L l
  have hf : (fun x => lemmaVPlanarRowField I
      (pureFluxMainQ3CenteredBasisMultiplier n b σ L l) v x i) =
      fun x => σ⁻¹ * lemmaVPlanarRowField I
        (pureFluxMainQ3CenteredBasisMultiplier n b 1 L l) v x i := by
    simp_rw [hη, pureFluxPlanarRowField_smul]
    rfl
  change Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
    (cubeIncrement U (k+1) (fun x => lemmaVPlanarRowField I
      (pureFluxMainQ3CenteredBasisMultiplier n b σ L l) v x i)))
  rw [hf]
  exact pureFlux_positive_series_smul U _ (σ⁻¹)
    (pureFluxMainQ3_centered_row_positive_series_unit n b L m p u U hU l i)

end
end ASDExplicitGamma.Inverse
