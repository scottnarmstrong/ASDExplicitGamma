module

public import ASDExplicitGamma.Scalar.UpperCellEnergyBandGaussian
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalBandVariance
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBandWeakGradient
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBandStrongDerivative
public import ASDExplicitGamma.Scalar.Lambda8CovarianceAdapter

/-! The actual full physical RESET band has a weak gradient on each cell.
The forcing derivative is obtained from the literal finite-band Gaussian
jet and the skew-matrix identity, then transported through the stationary
Helmholtz projection. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped BigOperators
noncomputable section

/-- The physical labels enumerate exactly the future shell interval, even
when the bottom label is negative or the interval is empty. -/
theorem upper_cell_physical_band_sum {E : Type*} [AddCommMonoid E]
    (n : ℤ) (height : ℕ) (f : ℤ → E) :
    (∑ i : Fin height, f (upperCellPhysicalBandLabel n height i)) =
      ∑ k ∈ Finset.Ioc n (n+(height:ℤ)), f k := by
  apply Finset.sum_bij (fun i _ => upperCellPhysicalBandLabel n height i)
  · intro i _
    simp only [Finset.mem_Ioc, upperCellPhysicalBandLabel]
    have hi := i.isLt
    omega
  · intro i _ j _ hij
    exact upper_cell_physical_band_label_injective n height hij
  · intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    let i : Fin height := ⟨(k-n-1).toNat, by omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    dsimp only [upperCellPhysicalBandLabel, i]
    omega
  · intro i _
    rfl

/-- The actual physical scalar band and its stored jets are jointly Gaussian
on the original cutoff carrier. -/
theorem upper_cell_reset_band_jets_gaussian
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) :
    IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet (upperCellPhysicalBandLabel n height)
        (fun _ => c)) := by
  change IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
    (upperCellBandJet (upperCellPhysicalBandLabel n height) (fun _ => c))
  exact upper_cell_band_jets_gaussian M h hM _
    (upper_cell_physical_band_label_injective n height) _

/-- At each sample, the literal finite-band forcing is the scalar value jet
times the fixed planar quarter-turn of its direction. -/
theorem upper_cell_reset_band_forcing_point
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
    (valuePathForcing (c • e) (shellSumValuePath n (n+(height:ℤ)) ω.val)).ofLp i =
      matVecMul Response.responsePlanarJ e i *
        upperCellBandJet (upperCellPhysicalBandLabel n height)
          (fun _ => c) (.value 0) ω := by
  change matVecMul (shellSumValuePath n (n+(height:ℤ)) ω.val 0) (c • e) i = _
  rw [shellSumValuePath_apply, matVecMul_finiteShellIncrement_apply]
  have hp (k : ℤ) : shellRowForcing (c • e) 0 i k ω.val =
      matVecMul Response.responsePlanarJ e i *
        (c*shellDerivativeEval (.value 0) (ω.val k)) := by
    change matVecMul (ω.val k 0) (c • e) i = _
    rw [lambda8Q3ShellMatVec_eq_scalarJ]
    have he : matVecMul Response.responsePlanarJ (c • e) i =
        c * matVecMul Response.responsePlanarJ e i := by
      simp only [matVecMul, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
      ring
    change (ω.val k 0 1 0) * matVecMul Response.responsePlanarJ (c • e) i =
      matVecMul Response.responsePlanarJ e i *
        (c * (ω.val k 0 1 0))
    rw [he]
    ring
  simp_rw [hp]
  rw [← Finset.mul_sum]
  congr 1
  exact (upper_cell_physical_band_sum n height
    (fun k => c*shellDerivativeEval (.value 0) (ω.val k))).symm

/-- The actual cutoff-carrier forcing coordinates equal the scalar jet
coordinates, using only the actual shell-sum carrier. -/
theorem upper_cell_reset_band_forcing_coord
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (i : Fin 2) :
    vectorL2Coord i (upperCellResetBandForcing M n (n+(height:ℤ)) c e) =
      matVecMul Response.responsePlanarJ e i •
        upperCellResetBandJetClass M (upperCellPhysicalBandLabel n height)
          (fun _ => c)
          (upper_cell_reset_band_jets_gaussian M h hM n height c)
          (.value 0) := by
  let k := upperCellPhysicalBandLabel n height
  let w : Fin height → ℝ := fun _ => c
  let hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet k w) :=
    upper_cell_reset_band_jets_gaussian M h hM n height c
  let F := upperCellResetBandForcing M n (n+(height:ℤ)) c e
  let v := upperCellResetBandJetClass M k w hGaussian (.value 0)
  let hp := measurePreserving_shellSumValuePath_cutoffSample M n (n+(height:ℤ))
  have hc := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL F
  have ht := coeFn_carrierTransport hp
    (shellSumForcingL2 M (c • e) n (n+(height:ℤ)))
  have hf := hp.quasiMeasurePreserving.ae
    (memLp_two_valuePathForcing_shellSum M (c • e) n (n+(height:ℤ))).coeFn_toLp
  have hv := (upper_cell_reset_band_jet_memLp M k w hGaussian (.value 0)).coeFn_toLp
  have hs := Lp.coeFn_smul (matVecMul Response.responsePlanarJ e i) v
  apply Lp.ext
  filter_upwards [hc, ht, hf, hv, hs] with ω hc ht hf hv hs
  change vectorL2Coord i F ω = (F ω).ofLp i at hc
  change F ω = shellSumForcingL2 M (c • e) n (n+(height:ℤ))
    (shellSumValuePath n (n+(height:ℤ)) ω.val) at ht
  change shellSumForcingL2 M (c • e) n (n+(height:ℤ))
    (shellSumValuePath n (n+(height:ℤ)) ω.val) = _ at hf
  change v ω = upperCellResetBandJet k w (.value 0) ω at hv
  rw [hc, ht, hf, hs]
  change (valuePathForcing (c • e)
      (shellSumValuePath n (n+(height:ℤ)) ω.val)).ofLp i =
    matVecMul Response.responsePlanarJ e i * v ω
  rw [hv]
  exact upper_cell_reset_band_forcing_point n height c e ω i

/-- Continuous linear map from a scalar stationary class to the fixed vector
multiple that appears in the skew forcing coordinates. -/
noncomputable def upperCellResetScalarVectorMap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (b : Vec 2) :
    ScalarL2 μ →L[ℝ] VectorL2 2 μ :=
  ∑ i : Fin 2,
    (upperCellResetCoordLift μ i).comp
      ((ContinuousLinearMap.lsmul ℝ ℝ (E := ScalarL2 μ)) (b i))

theorem upper_cell_reset_scalar_vector_map_coord
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (b : Vec 2)
    (f : ScalarL2 μ) (i : Fin 2) :
    vectorL2Coord i (upperCellResetScalarVectorMap μ b f) = b i • f := by
  classical
  unfold upperCellResetScalarVectorMap
  simp only [sum_apply, map_sum, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lsmul_apply,
    upper_cell_reset_coord_lift]
  simp

theorem upper_cell_reset_scalar_vector_map_translate
    {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec 2) Ω]
    {μ : Measure Ω} [MeasurableConstVAdd (Vec 2) Ω]
    [VAddInvariantMeasure (Vec 2) Ω μ] (b : Vec 2) (z : Vec 2) (f : ScalarL2 μ) :
    upperCellResetScalarVectorMap μ b (koopman z f) =
      koopman z (upperCellResetScalarVectorMap μ b f) := by
  apply upper_cell_reset_vector_ext μ
  intro i
  rw [upper_cell_reset_scalar_vector_map_coord, ← koopman_vectorL2Coord,
    upper_cell_reset_scalar_vector_map_coord]
  simp

/-- The actual full physical band has an actual weak gradient on every fixed
cell. Its derivative is the finite-band Gaussian first jet transported
through the genuine solenoidal projection. -/
theorem upper_cell_reset_band_physical_weak_gradient
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) :
    let k := upperCellPhysicalBandLabel n height
    let w : Fin height → ℝ := fun _ => c
    let hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
        (upperCellResetBandJet k w) :=
      upper_cell_reset_band_jets_gaussian M h hM n height c
    let D : Fin 2 → VectorL2 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
      fun j => upperCellResetScalarVectorMap
        (Cutoff.cutoffSampleLaw M).toMeasure (matVecMul Response.responsePlanarJ e)
        (upperCellResetBandJetClass M k w hGaussian
          (.first 0 (basisVec j)))
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i : Fin 2,
      HasWeakGradientOn (openCubeSet Q)
        (fun x => (realize (cutoffBandFlux M n (n+(height:ℤ)) c e) ω x).toVec i)
        (fun x => (realize (upperCellResetDerivativeRowRepr D i) ω x).toVec) := by
  dsimp only
  let k := upperCellPhysicalBandLabel n height
  let w : Fin height → ℝ := fun _ => c
  let hGaussian : IsCenteredGaussianFamily (Cutoff.cutoffSampleLaw M).toMeasure
      (upperCellResetBandJet k w) :=
    upper_cell_reset_band_jets_gaussian M h hM n height c
  let v := upperCellResetBandJetClass M k w hGaussian (.value 0)
  let T := upperCellResetScalarVectorMap (Cutoff.cutoffSampleLaw M).toMeasure
    (matVecMul Response.responsePlanarJ e)
  let F := upperCellResetBandForcing M n (n+(height:ℤ)) c e
  let D : Fin 2 → VectorL2 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
    fun j => T (upperCellResetBandJetClass M k w hGaussian (.first 0 (basisVec j)))
  have hF : F = T v := by
    apply upper_cell_reset_vector_ext (Cutoff.cutoffSampleLaw M).toMeasure
    intro i
    rw [upper_cell_reset_scalar_vector_map_coord]
    exact upper_cell_reset_band_forcing_coord M h hM n height c e i
  have hD (j : Fin 2) : HasDerivAt
      (fun t : ℝ => koopman (t • basisVec j) F) (D j) 0 := by
    have hscalar := upper_cell_reset_band_horizontal_derivative M k w hGaussian
      (basisVec j)
    have hmap := T.hasFDerivAt.comp_hasDerivAt 0 hscalar
    have hfun : (fun t : ℝ => T (koopman (t • basisVec j) v)) =
        (fun t : ℝ => koopman (t • basisVec j) F) := by
      funext t
      rw [upper_cell_reset_scalar_vector_map_translate, hF]
    rw [← hfun]
    exact hmap
  exact upper_cell_reset_band_physical_weak_gradient' M n (n+(height:ℤ)) c e Q D hD

end
end ASDExplicitGamma.Scalar
