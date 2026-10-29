module

public import ASDExplicitGamma.Statements.PlanarQ3Gaussian
public import ASDExplicitGamma.Model.Q3Kernel
public import ASDExplicitGamma.Model.SpectralFirstChaos
public import Algsuperdiff.Probability.StationaryValueProjection

@[expose] public section

open MeasureTheory Homogenization ProbabilityTheory

namespace ASDExplicitGamma.Model

/-- The spectral mass of the one-dimensional q3 covariance is one. -/
theorem q3Cov_zero_eq_one : q3Cov 0 = 1 := by
  rw [q3Cov]
  calc
    (∫ y : ℝ, q3Kernel y * q3Kernel (y + 0)) =
        ∫ y : ℝ, q3Kernel y ^ 2 := by
          congr 1
          funext y
          simp [pow_two]
    _ = 1 := q3Kernel_sq_integral

noncomputable def planarRegLaw (M : Algsuperdiff.Section3.ABKModel 2) :=
  (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw M.P).toMeasure

/-- The frozen J1 stationarity gives the vadd-invariant measure structure
needed by the stationary gradient API. -/
instance q3PlanarRegLaw_vaddInvariant
    (M : Algsuperdiff.Section3.ABKModel 2) :
    VAddInvariantMeasure (Homogenization.Vec 2) (RegCoeffField 2) (planarRegLaw M) :=
  Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_vaddInvariant
    M.P
    (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
      M.P M.J1.stationary)

/-- The first coordinate vector in the planar coefficient carrier. -/
def planarBasis0 : Homogenization.Vec 2 := Pi.single 0 1

theorem planarBasis0_unit : Homogenization.Book.Ch02.vecNorm planarBasis0 = 1 := by
  have hsq : Homogenization.Book.Ch02.vecNorm planarBasis0 ^ 2 = 1 := by
    rw [Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq]
    norm_num [Homogenization.vecNormSq, Homogenization.vecDot,
      planarBasis0, Pi.single_apply]
  nlinarith [Homogenization.Book.Ch02.vecNorm_nonneg planarBasis0]

/-- The actual vector origin forcing selected by the frozen J4 definition. -/
noncomputable def q3OriginForcingL2
    (M : Algsuperdiff.Section3.ABKModel 2) :
    Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M) := by
  let hmem :=
    Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
      M.P M.J2.gaussian_tail planarBasis0 planarBasis0_unit
  exact Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellForcingL2
    M.P planarBasis0 hmem

/-- The scalar zero-shell stream value at the origin, represented in the
actual `RegCoeffField` L² carrier used by J4. -/
noncomputable def q3StreamOriginL2 (M : Algsuperdiff.Section3.ABKModel 2) :
    Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M) :=
  Algsuperdiff.Probability.Stationary.vectorL2Coord 1 (q3OriginForcingL2 M)

/-- The scalar origin observable is exactly the `(1,0)` entry of the regular
coefficient field, as an L² equivalence class. -/
theorem q3StreamOriginL2_coeFn (M : Algsuperdiff.Section3.ABKModel 2) :
    (q3StreamOriginL2 M : RegCoeffField 2 → ℝ) =ᵐ[planarRegLaw M]
      fun a => a 0 1 0 := by
  let hmem :=
    Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
      M.P M.J2.gaussian_tail planarBasis0 planarBasis0_unit
  let F := Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellForcingL2
    M.P planarBasis0 hmem
  change
    (Algsuperdiff.Probability.Stationary.vectorL2Coord 1 F :
      Lp ℝ 2 (planarRegLaw M)) =ᵐ[planarRegLaw M] fun a => a 0 1 0
  have hcoord :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 1).coeFn_compLpL F
  have hF :=
    Algsuperdiff.Frozen.Assumptions.ShellField.coeFn_zeroShellForcingL2
      M.P planarBasis0 hmem
  filter_upwards [hcoord, hF] with a hcoord hF
  calc
    _ = (F a) 1 := hcoord
    _ = a 0 1 0 := by
      rw [hF]
      simp [Algsuperdiff.Frozen.Assumptions.ShellField.originForcing,
        Homogenization.matVecMul, planarBasis0, Pi.single_apply]

/-- The frozen one-point Gaussian law fixes the spectral mass of the scalar
first chaos to `h^2`. -/
theorem q3StreamOriginL2_norm_sq
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h) :
    ‖q3StreamOriginL2 M‖ ^ 2 = h ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  simp only [Real.inner_apply]
  change (∫ a : RegCoeffField 2,
      q3StreamOriginL2 M a * q3StreamOriginL2 M a ∂planarRegLaw M) = h ^ 2
  have hcoe := q3StreamOriginL2_coeFn M
  have hreg : ∫ a : RegCoeffField 2,
        q3StreamOriginL2 M a * q3StreamOriginL2 M a ∂planarRegLaw M =
      ∫ a : RegCoeffField 2, (a 0 1 0) ^ 2 ∂planarRegLaw M := by
    apply integral_congr_ae
    filter_upwards [hcoe] with a ha
    rw [ha]
    simp [pow_two]
  rw [hreg]
  have hobs :
      ((Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure).map
          (fun j : Algsuperdiff.Frozen.Assumptions.ShellField 2 => j 0 1 0) =
        gaussianReal 0 (Real.toNNReal (h ^ 2)) := by
    simpa [q3Cov_zero_eq_one] using
      hM.2 1 (fun _ : Fin 1 => (0 : Homogenization.Vec 2))
        (fun _ : Fin 1 => (1 : ℝ))
  have hreglaw : planarRegLaw M =
      Measure.map Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell
        (Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure := by
    exact Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_toMeasure_eq_map_forgetShell
      M.P
  calc
    ∫ a : RegCoeffField 2, (a 0 1 0) ^ 2 ∂planarRegLaw M =
        ∫ j : Algsuperdiff.Frozen.Assumptions.ShellField 2,
          (j 0 1 0) ^ 2 ∂(Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure := by
      rw [hreglaw]
      rw [MeasureTheory.integral_map
        Algsuperdiff.Frozen.Assumptions.ShellField.measurable_forgetShell.aemeasurable]
      · apply integral_congr_ae
        filter_upwards [] with j
        simp [Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
      · exact ((Homogenization.measurable_apply_entry
          (0 : Homogenization.Vec 2) 1 0).pow_const 2).aestronglyMeasurable
    _ = ∫ y : ℝ, y ^ 2 ∂gaussianReal 0 (Real.toNNReal (h ^ 2)) := by
      calc
        _ = ∫ y : ℝ, y ^ 2 ∂
            ((Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellLaw M.P).toMeasure).map
              (fun j : Algsuperdiff.Frozen.Assumptions.ShellField 2 => j 0 1 0) := by
          have hmeas : Measurable
              (fun j : Algsuperdiff.Frozen.Assumptions.ShellField 2 => j 0 1 0) :=
            (Homogenization.measurable_apply_entry
              (0 : Homogenization.Vec 2) 1 0).comp
                Algsuperdiff.Frozen.Assumptions.ShellField.measurable_forgetShell
          exact (MeasureTheory.integral_map hmeas.aemeasurable
            ((measurable_id.pow_const 2).aestronglyMeasurable)).symm
        _ = ∫ y : ℝ, y ^ 2 ∂gaussianReal 0 (Real.toNNReal (h ^ 2)) := by rw [hobs]
    _ = h ^ 2 := by
      have hvar : Var[fun x : ℝ => x; gaussianReal 0 (Real.toNNReal (h ^ 2))] =
          (Real.toNNReal (h ^ 2) : ℝ) :=
        ProbabilityTheory.variance_fun_id_gaussianReal
      have hvar0 := hvar
      have hvarInt := ProbabilityTheory.variance_eq_integral
        (μ := gaussianReal 0 (Real.toNNReal (h ^ 2)))
        (X := fun x : ℝ => x) measurable_id.aemeasurable
      rw [hvarInt] at hvar
      rw [ProbabilityTheory.integral_id_gaussianReal] at hvar
      have hcast : (Real.toNNReal (h ^ 2) : ℝ) = h ^ 2 :=
        Real.coe_toNNReal _ (sq_nonneg h)
      have hsecond : ∫ y : ℝ, y ^ 2 ∂gaussianReal 0 (Real.toNNReal (h ^ 2)) =
          Var[fun x : ℝ => x; gaussianReal 0 (Real.toNNReal (h ^ 2))] := by
        rw [hvarInt]
        rw [ProbabilityTheory.integral_id_gaussianReal]
        simp [pow_two]
      calc
        ∫ y : ℝ, y ^ 2 ∂gaussianReal 0 (Real.toNNReal (h ^ 2)) =
            Var[fun x : ℝ => x; gaussianReal 0 (Real.toNNReal (h ^ 2))] := hsecond
        _ = (Real.toNNReal (h ^ 2) : ℝ) := hvar0
        _ = h ^ 2 := hcast

theorem q3OriginForcingL2_coord0_eq_zero
    (M : Algsuperdiff.Section3.ABKModel 2) :
    Algsuperdiff.Probability.Stationary.vectorL2Coord 0 (q3OriginForcingL2 M) = 0 := by
  have hmeas : MeasurableSet {a : RegCoeffField 2 | a 0 0 0 = 0} :=
    measurableSet_eq_fun
      (Homogenization.measurable_apply_entry (0 : Homogenization.Vec 2) 0 0)
      measurable_const
  have hskew : ∀ᵐ a ∂planarRegLaw M, a 0 0 0 = 0 := by
    rw [planarRegLaw,
      Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_toMeasure_eq_map_forgetShell]
    rw [ae_map_iff
      Algsuperdiff.Frozen.Assumptions.ShellField.measurable_forgetShell.aemeasurable hmeas]
    filter_upwards with j
    have hs := Algsuperdiff.Frozen.Assumptions.ShellField.skew_entry j
      (0 : Homogenization.Vec 2) 0 0
    have hz : j 0 0 0 = 0 := by linarith
    simpa [Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply] using hz
  apply Lp.ext
  have hcoord :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 0).coeFn_compLpL
      (q3OriginForcingL2 M)
  have hmem :=
    Algsuperdiff.Frozen.Assumptions.ShellField.memLp_originForcing_of_j2_tail
      M.P M.J2.gaussian_tail planarBasis0 planarBasis0_unit
  have hF := Algsuperdiff.Frozen.Assumptions.ShellField.coeFn_zeroShellForcingL2
    M.P planarBasis0 hmem
  have hF' : (q3OriginForcingL2 M : RegCoeffField 2 → Homogenization.HilbertVec 2) =ᵐ[
      planarRegLaw M] Algsuperdiff.Frozen.Assumptions.ShellField.originForcing planarBasis0 := by
    simpa [q3OriginForcingL2, planarRegLaw] using hF
  have hzero : ((0 : Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)) :
      RegCoeffField 2 → ℝ) =ᵐ[planarRegLaw M] 0 :=
    Lp.coeFn_zero ℝ 2 (planarRegLaw M)
  filter_upwards [hcoord, hF', hzero, hskew] with a hcoord hF hzero hskew
  calc
    _ = (q3OriginForcingL2 M : RegCoeffField 2 → Homogenization.HilbertVec 2) a 0 := hcoord
    _ = (Algsuperdiff.Frozen.Assumptions.ShellField.originForcing planarBasis0 a).ofLp 0 := by
      rw [hF]
    _ = Homogenization.matVecMul (a 0) planarBasis0 0 := by
      simp [Algsuperdiff.Frozen.Assumptions.ShellField.originForcing]
    _ = a 0 0 0 := by
      simp [Homogenization.matVecMul, planarBasis0, Pi.single_apply]
    _ = 0 := hskew
    _ = ((0 : Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)) :
      RegCoeffField 2 → ℝ) a := hzero.symm

/-- The canonical Koopman isometry on the planar zero-shell `L²` carrier. -/
noncomputable def q3StreamKoopman
    (M : Algsuperdiff.Section3.ABKModel 2) (z : Homogenization.Vec 2) :
    Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M) →ₗᵢ[ℝ]
      Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M) := by
  let hstationary :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
      M.P M.J1.stationary
  have hinv : VAddInvariantMeasure (Homogenization.Vec 2) (RegCoeffField 2)
      (planarRegLaw M) :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_vaddInvariant
      M.P hstationary
  letI := hinv
  exact Algsuperdiff.Probability.Stationary.koopman
    (μ := planarRegLaw M) (d := 2) z

/-- Translating the origin observable evaluates the scalar stream at the
translated spatial point. -/
theorem q3StreamKoopman_apply
    (M : Algsuperdiff.Section3.ABKModel 2) (z : Homogenization.Vec 2) :
    q3StreamKoopman M z (q3StreamOriginL2 M) =ᵐ[planarRegLaw M]
      fun a : RegCoeffField 2 => a z 1 0 := by
  let hstationary :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
      M.P M.J1.stationary
  have hinv : VAddInvariantMeasure (Homogenization.Vec 2) (RegCoeffField 2)
      (planarRegLaw M) :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_vaddInvariant
      M.P hstationary
  have hInvariant : VAddInvariantMeasure (Homogenization.Vec 2) (RegCoeffField 2)
      (planarRegLaw M) := hinv
  let mp := Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd
    (μ := planarRegLaw M) z
  have hcomp := Lp.coeFn_compMeasurePreserving (q3StreamOriginL2 M) mp
  have horigin := q3StreamOriginL2_coeFn M
  have hvadd (a : RegCoeffField 2) : z +ᵥ a = translateReg z a := rfl
  have hshift : (fun a : RegCoeffField 2 =>
      (q3StreamOriginL2 M : RegCoeffField 2 → ℝ) (translateReg z a)) =ᵐ[planarRegLaw M]
      fun a => a z 1 0 := by
    filter_upwards [mp.quasiMeasurePreserving.ae_eq_comp horigin] with a ha
    simpa only [Function.comp_apply, hvadd, translateReg_apply, zero_add] using ha
  filter_upwards [hcomp, hshift] with a ha hb
  simpa [q3StreamKoopman, Algsuperdiff.Probability.Stationary.koopman,
    Algsuperdiff.Frozen.Assumptions.ShellField.regCoeffFieldAddAction] using
    (ha.trans hb)

private theorem q3StreamKoopman_add
    (M : Algsuperdiff.Section3.ABKModel 2)
    [VAddInvariantMeasure (Homogenization.Vec 2) (RegCoeffField 2)
      (planarRegLaw M)]
    (x y : Homogenization.Vec 2)
    (f : Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)) :
    Algsuperdiff.Probability.Stationary.koopman
        (μ := planarRegLaw M) (d := 2) (x + y) f =
      Algsuperdiff.Probability.Stationary.koopman
        (μ := planarRegLaw M) (d := 2) x
          (Algsuperdiff.Probability.Stationary.koopman
            (μ := planarRegLaw M) (d := 2) y f) := by
  let μ := planarRegLaw M
  have hMaps : (fun a : RegCoeffField 2 => (x + y) +ᵥ a) =
      fun a => y +ᵥ (x +ᵥ a) := by
    funext a
    calc
      (x + y) +ᵥ a = (y + x) +ᵥ a := by rw [add_comm]
      _ = y +ᵥ (x +ᵥ a) := add_vadd y x a
  change
    Lp.compMeasurePreserving (fun a : RegCoeffField 2 => (x + y) +ᵥ a)
      (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) (x + y)) f =
    Lp.compMeasurePreserving (fun a : RegCoeffField 2 => x +ᵥ a)
      (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) x)
      (Lp.compMeasurePreserving (fun a : RegCoeffField 2 => y +ᵥ a)
        (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) y) f)
  have hMapComp : (fun a : RegCoeffField 2 => (x + y) +ᵥ a) =
      (fun a : RegCoeffField 2 => y +ᵥ a) ∘ (fun a => x +ᵥ a) := by
    funext a
    calc
      (x + y) +ᵥ a = y +ᵥ (x +ᵥ a) := congrFun hMaps a
      _ = ((fun a : RegCoeffField 2 => y +ᵥ a) ∘ (fun a => x +ᵥ a)) a := rfl
  have hPair :
      (⟨(fun a : RegCoeffField 2 => (x + y) +ᵥ a),
        Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) (x + y)⟩ :
        {g : RegCoeffField 2 → RegCoeffField 2 // MeasurePreserving g μ μ}) =
      ⟨(fun a : RegCoeffField 2 => y +ᵥ a) ∘ (fun a => x +ᵥ a),
        (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) y).comp
          (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) x)⟩ := by
    apply Subtype.ext
    exact hMapComp
  calc
    Lp.compMeasurePreserving (fun a : RegCoeffField 2 => (x + y) +ᵥ a)
        (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) (x + y)) f =
      Lp.compMeasurePreserving
        ((fun a : RegCoeffField 2 => y +ᵥ a) ∘ (fun a => x +ᵥ a))
        ((Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) y).comp
          (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) x)) f := by
      exact congrArg (fun g : {g : RegCoeffField 2 → RegCoeffField 2 // MeasurePreserving g μ μ} =>
        Lp.compMeasurePreserving g.1 g.2 f) hPair
    _ = Lp.compMeasurePreserving (fun a : RegCoeffField 2 => x +ᵥ a)
          (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) x)
          (Lp.compMeasurePreserving (fun a : RegCoeffField 2 => y +ᵥ a)
            (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) y) f) :=
      Lp.compMeasurePreserving_comp_apply f
        (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) y)
        (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) x)

/-- The zero translation acts as the identity on the stationary scalar `L²`. -/
theorem q3StreamKoopman_zero
    (M : Algsuperdiff.Section3.ABKModel 2)
    (f : Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)) :
    q3StreamKoopman M 0 f = f := by
  let hstationary :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
      M.P M.J1.stationary
  have hinv : VAddInvariantMeasure (Homogenization.Vec 2) (RegCoeffField 2)
      (planarRegLaw M) :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_vaddInvariant
      M.P hstationary
  change Lp.compMeasurePreserving (fun a : RegCoeffField 2 => (0 : Homogenization.Vec 2) +ᵥ a)
    (Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd
      (μ := planarRegLaw M) 0) f = f
  let μ := planarRegLaw M
  have hpair :
      (⟨(fun a : RegCoeffField 2 => (0 : Homogenization.Vec 2) +ᵥ a),
        Algsuperdiff.Probability.Stationary.measurePreserving_const_vadd (μ := μ) 0⟩ :
        {g : RegCoeffField 2 → RegCoeffField 2 // MeasurePreserving g μ μ}) =
      ⟨id, MeasurePreserving.id μ⟩ := by
    apply Subtype.ext
    funext a
    simp
  exact (congrArg (fun g : {g : RegCoeffField 2 → RegCoeffField 2 //
      MeasurePreserving g μ μ} => Lp.compMeasurePreserving g.1 g.2 f) hpair).trans
    (Lp.compMeasurePreserving_id_apply f)

/-- The first-chaos space for the scalar q3 stream on the frozen stationary
zero-shell law. It is the closed span of all translates of the origin stream. -/
noncomputable def q3StreamFirstChaos
    (M : Algsuperdiff.Section3.ABKModel 2) :
    Submodule ℝ (Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)) := by
  exact KoopmanOrbitSubspace
    (fun z : Homogenization.Vec 2 => q3StreamKoopman M z)
    (q3StreamOriginL2 M)

theorem q3StreamFirstChaos_contains_origin
    (M : Algsuperdiff.Section3.ABKModel 2) :
    q3StreamOriginL2 M ∈ q3StreamFirstChaos M := by
  change q3StreamOriginL2 M ∈ (Submodule.span ℝ
    (Set.range fun z : Homogenization.Vec 2 =>
      q3StreamKoopman M z (q3StreamOriginL2 M))).topologicalClosure
  apply subset_closure
  apply Submodule.subset_span
  exact ⟨0, q3StreamKoopman_zero M (q3StreamOriginL2 M)⟩

/-- The q3 stream cyclic subspace admits an orthogonal projection. -/
instance q3StreamFirstChaos_hasOrthogonalProjection
    (M : Algsuperdiff.Section3.ABKModel 2) :
    (q3StreamFirstChaos M).HasOrthogonalProjection := by
  change (KoopmanOrbitSubspace
    (fun x : Homogenization.Vec 2 => q3StreamKoopman M x)
    (q3StreamOriginL2 M)).HasOrthogonalProjection
  infer_instance

noncomputable def q3VectorCoordCLM (i : Fin 2) :
    ℝ →L[ℝ] Homogenization.HilbertVec 2 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) i)

noncomputable def q3VectorCoordLift
    (M : Algsuperdiff.Section3.ABKModel 2) (i : Fin 2) :
    Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M) →L[ℝ]
      Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M) :=
  (q3VectorCoordCLM i).compLpL 2 (planarRegLaw M)

theorem q3VectorCoordLift_coord
    (M : Algsuperdiff.Section3.ABKModel 2) (i j : Fin 2)
    (f : Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)) :
    Algsuperdiff.Probability.Stationary.vectorL2Coord i
      (q3VectorCoordLift M j f) = if i = j then f else 0 := by
  change (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).compLpL
      2 (planarRegLaw M) (q3VectorCoordLift M j f) = if i = j then f else 0
  apply Lp.ext
  have hL := (q3VectorCoordCLM j).coeFn_compLpL f
  have hproj := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i)
    |>.coeFn_compLpL (q3VectorCoordLift M j f)
  have hzero : ((0 : Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)) :
      RegCoeffField 2 → ℝ) =ᵐ[planarRegLaw M] 0 :=
    Lp.coeFn_zero ℝ 2 (planarRegLaw M)
  filter_upwards [hL, hproj, hzero] with a hL hproj hzero
  have hLift : (q3VectorCoordLift M j f : RegCoeffField 2 → Homogenization.HilbertVec 2) a =
      q3VectorCoordCLM j ((f : RegCoeffField 2 → ℝ) a) := hL
  rw [hproj, hLift]
  by_cases hij : i = j
  · subst i
    simp [q3VectorCoordCLM]
  · simpa [q3VectorCoordCLM, hij] using hzero.symm

private noncomputable def q3VectorFirstChaosProjection
    (M : Algsuperdiff.Section3.ABKModel 2) :
    Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M) →L[ℝ]
      Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M) :=
  ∑ i : Fin 2,
    (q3VectorCoordLift M i).comp
      ((q3StreamFirstChaos M).starProjection.comp
        (Algsuperdiff.Probability.Stationary.vectorL2Coord i))

private theorem q3VectorFirstChaosProjection_coord
    (M : Algsuperdiff.Section3.ABKModel 2) (i : Fin 2)
    (F : Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M)) :
    Algsuperdiff.Probability.Stationary.vectorL2Coord i
      (q3VectorFirstChaosProjection M F) =
      (q3StreamFirstChaos M).starProjection
        (Algsuperdiff.Probability.Stationary.vectorL2Coord i F) := by
  classical
  change Algsuperdiff.Probability.Stationary.vectorL2Coord i
      (∑ j : Fin 2, q3VectorCoordLift M j
        ((q3StreamFirstChaos M).starProjection
          (Algsuperdiff.Probability.Stationary.vectorL2Coord j F))) = _
  rw [map_sum]
  simp only [q3VectorCoordLift_coord]
  simp

theorem q3VectorL2_inner_eq_sum_coord
    (M : Algsuperdiff.Section3.ABKModel 2)
    (F G : Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M)) :
    inner ℝ F G = ∑ i : Fin 2,
      inner ℝ
        (Algsuperdiff.Probability.Stationary.vectorL2Coord i F)
        (Algsuperdiff.Probability.Stationary.vectorL2Coord i G) := by
  rw [MeasureTheory.L2.inner_def]
  simp only [PiLp.inner_apply]
  have hcoordF (i : Fin 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL F
  have hcoordG (i : Fin 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL G
  have hterm (i : Fin 2) :
      ∫ a : RegCoeffField 2, inner ℝ ((F a).ofLp i) ((G a).ofLp i) ∂planarRegLaw M =
        inner ℝ (Algsuperdiff.Probability.Stationary.vectorL2Coord i F)
          (Algsuperdiff.Probability.Stationary.vectorL2Coord i G) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcoordF i, hcoordG i] with a ha hb
    change (Algsuperdiff.Probability.Stationary.vectorL2Coord i F :
      RegCoeffField 2 → ℝ) a = _ at ha
    change (Algsuperdiff.Probability.Stationary.vectorL2Coord i G :
      RegCoeffField 2 → ℝ) a = _ at hb
    calc
      inner ℝ ((F a).ofLp i) ((G a).ofLp i) =
          inner ℝ ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i) (F a))
            ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i) (G a)) := rfl
      _ = inner ℝ
          ((Algsuperdiff.Probability.Stationary.vectorL2Coord i F : RegCoeffField 2 → ℝ) a)
          ((Algsuperdiff.Probability.Stationary.vectorL2Coord i G : RegCoeffField 2 → ℝ) a) :=
        by rw [← ha, ← hb]
  have hInt (i : Fin 2) :
      Integrable (fun a : RegCoeffField 2 => inner ℝ ((F a).ofLp i) ((G a).ofLp i))
        (planarRegLaw M) := by
    apply (MeasureTheory.L2.integrable_inner
      (Algsuperdiff.Probability.Stationary.vectorL2Coord i F)
      (Algsuperdiff.Probability.Stationary.vectorL2Coord i G)).congr
    filter_upwards [hcoordF i, hcoordG i] with a ha hb
    change (Algsuperdiff.Probability.Stationary.vectorL2Coord i F :
      RegCoeffField 2 → ℝ) a = _ at ha
    change (Algsuperdiff.Probability.Stationary.vectorL2Coord i G :
      RegCoeffField 2 → ℝ) a = _ at hb
    calc
      inner ℝ
          ((Algsuperdiff.Probability.Stationary.vectorL2Coord i F : RegCoeffField 2 → ℝ) a)
          ((Algsuperdiff.Probability.Stationary.vectorL2Coord i G : RegCoeffField 2 → ℝ) a) =
          inner ℝ ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i) (F a))
            ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i) (G a)) := by
              rw [ha, hb]
      _ = inner ℝ ((F a).ofLp i) ((G a).ofLp i) := rfl
  rw [integral_finsetSum]
  · simp_rw [hterm]
  · intro i hi
    exact hInt i

theorem q3VectorL2_ext_coord
    (M : Algsuperdiff.Section3.ABKModel 2)
    {F G : Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M)}
    (h : ∀ i : Fin 2,
      Algsuperdiff.Probability.Stationary.vectorL2Coord i F =
        Algsuperdiff.Probability.Stationary.vectorL2Coord i G) : F = G := by
  apply Lp.ext
  have hF (i : Fin 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL F
  have hG (i : Fin 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL G
  have he (i : Fin 2) := Lp.ext_iff.mp (h i)
  filter_upwards [hF 0, hG 0, hF 1, hG 1, he 0, he 1] with a hf0 hg0 hf1 hg1 he0 he1
  apply PiLp.ext
  intro i
  fin_cases i
  · calc
      (F a).ofLp 0 = PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 0 (F a) := rfl
      _ = (Algsuperdiff.Probability.Stationary.vectorL2Coord 0 F :
        RegCoeffField 2 → ℝ) a := hf0.symm
      _ = (Algsuperdiff.Probability.Stationary.vectorL2Coord 0 G :
        RegCoeffField 2 → ℝ) a := he0
      _ = PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 0 (G a) := hg0
      _ = (G a).ofLp 0 := rfl
  · calc
      (F a).ofLp 1 = PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 1 (F a) := rfl
      _ = (Algsuperdiff.Probability.Stationary.vectorL2Coord 1 F :
        RegCoeffField 2 → ℝ) a := hf1.symm
      _ = (Algsuperdiff.Probability.Stationary.vectorL2Coord 1 G :
        RegCoeffField 2 → ℝ) a := he1
      _ = PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) 1 (G a) := hg1
      _ = (G a).ofLp 1 := rfl

private theorem q3VectorFirstChaosProjection_symmetric
    (M : Algsuperdiff.Section3.ABKModel 2) :
    (q3VectorFirstChaosProjection M).toLinearMap.IsSymmetric := by
  intro F G
  calc
    inner ℝ (q3VectorFirstChaosProjection M F) G =
        ∑ i : Fin 2, inner ℝ
          ((q3StreamFirstChaos M).starProjection
            (Algsuperdiff.Probability.Stationary.vectorL2Coord i F))
          (Algsuperdiff.Probability.Stationary.vectorL2Coord i G) := by
      rw [q3VectorL2_inner_eq_sum_coord]
      simp_rw [q3VectorFirstChaosProjection_coord]
    _ = ∑ i : Fin 2, inner ℝ
          (Algsuperdiff.Probability.Stationary.vectorL2Coord i F)
          ((q3StreamFirstChaos M).starProjection
            (Algsuperdiff.Probability.Stationary.vectorL2Coord i G)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (q3StreamFirstChaos M).starProjection_isSymmetric _ _
    _ = inner ℝ F (q3VectorFirstChaosProjection M G) := by
      rw [q3VectorL2_inner_eq_sum_coord]
      simp_rw [q3VectorFirstChaosProjection_coord]

/-- The orthogonal projection onto the q3 stream first chaos commutes with all
stationary translations. -/
theorem q3StreamFirstChaosProjection_commute
    (M : Algsuperdiff.Section3.ABKModel 2) (z : Homogenization.Vec 2)
    (f : Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)) :
    (q3StreamFirstChaos M).starProjection (q3StreamKoopman M z f) =
      q3StreamKoopman M z ((q3StreamFirstChaos M).starProjection f) := by
  let hstationary :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
      M.P M.J1.stationary
  have hinv : VAddInvariantMeasure (Homogenization.Vec 2) (RegCoeffField 2)
      (planarRegLaw M) :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_vaddInvariant
      M.P hstationary
  have hgroup : ∀ x y g, q3StreamKoopman M (x + y) g =
      q3StreamKoopman M x (q3StreamKoopman M y g) := by
    intro x y g
    exact @q3StreamKoopman_add M hinv x y g
  have hinverse : ∀ x g, q3StreamKoopman M x (q3StreamKoopman M (-x) g) = g := by
    intro x g
    calc
      q3StreamKoopman M x (q3StreamKoopman M (-x) g) =
          q3StreamKoopman M (x + -x) g := (hgroup x (-x) g).symm
      _ = g := by rw [add_neg_cancel, q3StreamKoopman_zero]
  exact koopmanOrbitProjection_commute
    (fun x : Homogenization.Vec 2 => q3StreamKoopman M x)
    (q3StreamOriginL2 M) hgroup hinverse z f

private theorem q3VectorFirstChaosProjection_maps_gradient
    (M : Algsuperdiff.Section3.ABKModel 2)
    {φ : Algsuperdiff.Probability.Stationary.ScalarL2 (planarRegLaw M)}
    {F : Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M)}
    (hgrad : Algsuperdiff.Probability.Stationary.HasHorizontalGradient φ F) :
    Algsuperdiff.Probability.Stationary.HasHorizontalGradient
      ((q3StreamFirstChaos M).starProjection φ)
      (q3VectorFirstChaosProjection M F) := by
  let hstationary :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
      M.P M.J1.stationary
  have hinv : VAddInvariantMeasure (Homogenization.Vec 2) (RegCoeffField 2)
      (planarRegLaw M) :=
    Algsuperdiff.Frozen.Assumptions.ShellField.zeroShellRegLaw_vaddInvariant
      M.P hstationary
  intro i
  let b : Homogenization.Vec 2 := Pi.single i 1
  have hprojected : HasDerivAt
      (fun t : ℝ => (q3StreamFirstChaos M).starProjection
        (Algsuperdiff.Probability.Stationary.koopman
          (μ := planarRegLaw M) (t • b) φ))
      ((q3StreamFirstChaos M).starProjection
        (Algsuperdiff.Probability.Stationary.vectorL2Coord i F)) 0 := by
    simpa [b] using (hasDerivAt_const (x := (0 : ℝ))
      (c := (q3StreamFirstChaos M).starProjection)).clm_apply (hgrad i)
  have hcomm (t : ℝ) :
      q3StreamKoopman M (t • b) ((q3StreamFirstChaos M).starProjection φ) =
        (q3StreamFirstChaos M).starProjection
          (q3StreamKoopman M (t • b) φ) :=
    (q3StreamFirstChaosProjection_commute M (t • b) φ).symm
  have hfun :
      (fun t : ℝ => Algsuperdiff.Probability.Stationary.koopman
        (μ := planarRegLaw M) (t • b) ((q3StreamFirstChaos M).starProjection φ)) =
      (fun t : ℝ => (q3StreamFirstChaos M).starProjection
        (Algsuperdiff.Probability.Stationary.koopman
          (μ := planarRegLaw M) (t • b) φ)) := by
    funext t
    simpa [q3StreamKoopman] using hcomm t
  change HasDerivAt
    (fun t : ℝ => Algsuperdiff.Probability.Stationary.koopman
      (μ := planarRegLaw M) (t • b) ((q3StreamFirstChaos M).starProjection φ))
    (Algsuperdiff.Probability.Stationary.vectorL2Coord i
      (q3VectorFirstChaosProjection M F)) 0
  rw [hfun, q3VectorFirstChaosProjection_coord]
  exact hprojected

def q3FirstChaosHorizontalGradientRange
    (M : Algsuperdiff.Section3.ABKModel 2) :
    Submodule ℝ (Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M)) where
  carrier := {F | ∃ φ, φ ∈ q3StreamFirstChaos M ∧
    Algsuperdiff.Probability.Stationary.HasHorizontalGradient φ F}
  zero_mem' := by
    exact ⟨0, q3StreamFirstChaos M |>.zero_mem, by
      exact Algsuperdiff.Probability.Stationary.hasHorizontalGradient_zero⟩
  add_mem' := by
    rintro F G ⟨φ, hφ, hgradφ⟩ ⟨ψ, hψ, hgradψ⟩
    exact ⟨φ + ψ, q3StreamFirstChaos M |>.add_mem hφ hψ,
      hgradφ.add hgradψ⟩
  smul_mem' := by
    rintro c F ⟨φ, hφ, hgradφ⟩
    exact ⟨c • φ, q3StreamFirstChaos M |>.smul_mem c hφ,
      hgradφ.smul c⟩

noncomputable def q3FirstChaosPotentialSubspace
    (M : Algsuperdiff.Section3.ABKModel 2) :
    Submodule ℝ (Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M)) :=
  (q3FirstChaosHorizontalGradientRange M).topologicalClosure

private theorem q3FirstChaosPotentialSubspace_le_stationaryPotentialSubspace
    (M : Algsuperdiff.Section3.ABKModel 2) :
    q3FirstChaosPotentialSubspace M ≤
      Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
        (μ := planarRegLaw M) (d := 2) := by
  apply Submodule.topologicalClosure_mono
  intro F hF
  rcases hF with ⟨φ, hφ, hgrad⟩
  exact ⟨φ, hgrad⟩

private theorem q3VectorFirstChaosProjection_maps_gradientRange
    (M : Algsuperdiff.Section3.ABKModel 2)
    (F : Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M))
    (hF : F ∈ Algsuperdiff.Probability.Stationary.horizontalGradientRange
      (μ := planarRegLaw M) (d := 2)) :
    q3VectorFirstChaosProjection M F ∈
      Algsuperdiff.Probability.Stationary.horizontalGradientRange
        (μ := planarRegLaw M) (d := 2) := by
  rcases hF with ⟨φ, hgrad⟩
  exact ⟨(q3StreamFirstChaos M).starProjection φ,
    q3VectorFirstChaosProjection_maps_gradient M hgrad⟩

private theorem q3VectorFirstChaosProjection_maps_potentialClosure_to_firstChaos
    (M : Algsuperdiff.Section3.ABKModel 2)
    (F : Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M))
    (hF : F ∈ Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
      (μ := planarRegLaw M) (d := 2)) :
    q3VectorFirstChaosProjection M F ∈ q3FirstChaosPotentialSubspace M := by
  let S := Algsuperdiff.Probability.Stationary.horizontalGradientRange
    (μ := planarRegLaw M) (d := 2)
  let T := q3FirstChaosHorizontalGradientRange M
  have hsub : S ≤ T.topologicalClosure.comap
      (q3VectorFirstChaosProjection M).toLinearMap := by
    intro G hG
    rcases hG with ⟨φ, hgrad⟩
    have hmem : q3VectorFirstChaosProjection M G ∈ T :=
      ⟨(q3StreamFirstChaos M).starProjection φ,
        (q3StreamFirstChaos M).starProjection_apply_mem φ,
        q3VectorFirstChaosProjection_maps_gradient M hgrad⟩
    exact (Submodule.le_topologicalClosure T) hmem
  have hclosed : IsClosed
      (T.topologicalClosure.comap (q3VectorFirstChaosProjection M).toLinearMap :
        Set (Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M))) := by
    change IsClosed (q3VectorFirstChaosProjection M ⁻¹' (T.topologicalClosure : Set _))
    exact (Submodule.isClosed_topologicalClosure T).preimage
      (q3VectorFirstChaosProjection M).continuous
  exact Submodule.topologicalClosure_minimal S hsub hclosed hF

private theorem q3VectorFirstChaosProjection_maps_potentialSubspace
    (M : Algsuperdiff.Section3.ABKModel 2) :
    ∀ F ∈ Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
      (μ := planarRegLaw M) (d := 2),
      q3VectorFirstChaosProjection M F ∈
        Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
          (μ := planarRegLaw M) (d := 2) := by
  let S := Algsuperdiff.Probability.Stationary.horizontalGradientRange
    (μ := planarRegLaw M) (d := 2)
  have hS : S ∈ Module.End.invtSubmodule
      (q3VectorFirstChaosProjection M).toLinearMap := by
    rw [Module.End.mem_invtSubmodule_iff_map_le]
    rw [Submodule.map_le_iff_le_comap]
    intro F hF
    exact q3VectorFirstChaosProjection_maps_gradientRange M F hF
  have hclosure := Submodule.topologicalClosure_mem_invtSubmodule
    (f := q3VectorFirstChaosProjection M) hS
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hclosure
  intro F hF
  exact hclosure ⟨F, hF, rfl⟩

private theorem q3VectorFirstChaosProjection_maps_potentialOrthogonal
    (M : Algsuperdiff.Section3.ABKModel 2)
    (F : Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M))
    (hF : F ∈ (Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
      (μ := planarRegLaw M) (d := 2))ᗮ) :
    q3VectorFirstChaosProjection M F ∈
      (Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
        (μ := planarRegLaw M) (d := 2))ᗮ := by
  intro G hG
  calc
    inner ℝ G (q3VectorFirstChaosProjection M F) =
        inner ℝ (q3VectorFirstChaosProjection M F) G := real_inner_comm _ _
    _ = inner ℝ F (q3VectorFirstChaosProjection M G) :=
      q3VectorFirstChaosProjection_symmetric M F G
    _ = inner ℝ (q3VectorFirstChaosProjection M G) F := real_inner_comm _ _
    _ = 0 := hF _ (q3VectorFirstChaosProjection_maps_potentialSubspace M G hG)

private theorem q3VectorFirstChaosProjection_commute_potentialProjection
    (M : Algsuperdiff.Section3.ABKModel 2)
    (F : Algsuperdiff.Probability.Stationary.VectorL2 2 (planarRegLaw M)) :
    Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
      (μ := planarRegLaw M) (d := 2) (q3VectorFirstChaosProjection M F) =
    q3VectorFirstChaosProjection M
      (Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
        (μ := planarRegLaw M) (d := 2) F) := by
  let K := Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
    (μ := planarRegLaw M) (d := 2)
  have hq : q3VectorFirstChaosProjection M
      (Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
        (μ := planarRegLaw M) (d := 2) F) ∈ K :=
    q3VectorFirstChaosProjection_maps_potentialSubspace M _
      (Algsuperdiff.Probability.Stationary.stationaryPotentialProjection_mem F)
  have hsub : q3VectorFirstChaosProjection M F -
      q3VectorFirstChaosProjection M
        (Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
          (μ := planarRegLaw M) (d := 2) F) =
      q3VectorFirstChaosProjection M
        (F - Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
          (μ := planarRegLaw M) (d := 2) F) := by
    rw [map_sub]
  have horth : q3VectorFirstChaosProjection M F -
      q3VectorFirstChaosProjection M
        (Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
          (μ := planarRegLaw M) (d := 2) F) ∈ Kᗮ := by
    rw [hsub]
    exact q3VectorFirstChaosProjection_maps_potentialOrthogonal M _
      (Algsuperdiff.Probability.Stationary.sub_stationaryPotentialProjection_mem_orthogonal F)
  exact (Algsuperdiff.Probability.Stationary.eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
    hq horth).symm

private theorem q3OriginForcingL2_fixed_by_firstChaosProjection
    (M : Algsuperdiff.Section3.ABKModel 2) :
    q3VectorFirstChaosProjection M (q3OriginForcingL2 M) = q3OriginForcingL2 M := by
  apply q3VectorL2_ext_coord M
  intro i
  fin_cases i
  · rw [q3VectorFirstChaosProjection_coord]
    change (q3StreamFirstChaos M).starProjection
      (Algsuperdiff.Probability.Stationary.vectorL2Coord 0
        (q3OriginForcingL2 M)) =
      Algsuperdiff.Probability.Stationary.vectorL2Coord 0
        (q3OriginForcingL2 M)
    rw [q3OriginForcingL2_coord0_eq_zero]
    simp
  · rw [q3VectorFirstChaosProjection_coord]
    have hfix : (q3StreamFirstChaos M).starProjection
        (q3StreamOriginL2 M) = q3StreamOriginL2 M :=
      (q3StreamFirstChaos M).starProjection_eq_self_iff.mpr
        (q3StreamFirstChaos_contains_origin M)
    simpa [q3StreamOriginL2] using hfix

private theorem q3OriginForcingL2_stationaryPotential_mem_firstChaosPotentialSubspace
    (M : Algsuperdiff.Section3.ABKModel 2) :
    Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
      (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M) ∈
      q3FirstChaosPotentialSubspace M := by
  have hfix := q3OriginForcingL2_fixed_by_firstChaosProjection M
  have hcomm := q3VectorFirstChaosProjection_commute_potentialProjection M
    (q3OriginForcingL2 M)
  have heq : Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
      (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M) =
      q3VectorFirstChaosProjection M
        (Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
          (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M)) := by
    calc
      _ = Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
          (μ := planarRegLaw M) (d := 2)
          (q3VectorFirstChaosProjection M (q3OriginForcingL2 M)) :=
        congrArg (Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
          (μ := planarRegLaw M) (d := 2)) hfix.symm
      _ = _ := hcomm
  rw [heq]
  exact q3VectorFirstChaosProjection_maps_potentialClosure_to_firstChaos M _
    (Algsuperdiff.Probability.Stationary.stationaryPotentialProjection_mem
      (q3OriginForcingL2 M))

noncomputable instance q3FirstChaosPotentialSubspace_hasOrthogonalProjection
    (M : Algsuperdiff.Section3.ABKModel 2) :
    (q3FirstChaosPotentialSubspace M).HasOrthogonalProjection := by
  have hcomplete : CompleteSpace (q3FirstChaosPotentialSubspace M) := by
    change CompleteSpace (q3FirstChaosHorizontalGradientRange M).topologicalClosure
    infer_instance
  infer_instance

/-- The literal J4 input is reduced to the closure of gradients whose potential
lies in the scalar q3 first chaos. -/
theorem q3FirstChaosReduction
    (M : Algsuperdiff.Section3.ABKModel 2) :
    Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
      (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M) =
    (q3FirstChaosPotentialSubspace M).starProjection (q3OriginForcingL2 M) := by
  have hp : Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
      (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M) ∈
      q3FirstChaosPotentialSubspace M :=
    q3OriginForcingL2_stationaryPotential_mem_firstChaosPotentialSubspace M
  have horth : q3OriginForcingL2 M -
      Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
        (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M) ∈
      (q3FirstChaosPotentialSubspace M)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro G hG
    calc
      inner ℝ (q3OriginForcingL2 M -
        Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
          (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M)) G =
        inner ℝ G (q3OriginForcingL2 M -
          Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
            (μ := planarRegLaw M) (d := 2) (q3OriginForcingL2 M)) := real_inner_comm _ _
      _ = 0 :=
        Algsuperdiff.Probability.Stationary.sub_stationaryPotentialProjection_mem_orthogonal
          (q3OriginForcingL2 M) G
          (q3FirstChaosPotentialSubspace_le_stationaryPotentialSubspace M hG)
  exact (Submodule.eq_starProjection_of_mem_orthogonal hp horth).symm

end ASDExplicitGamma.Model

end
