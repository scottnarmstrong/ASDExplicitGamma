module

public import ASDExplicitGamma.Main.EOscillationMinimizer
public import ASDExplicitGamma.Main.EnvelopeHMaxHistory
public import ASDExplicitGamma.Main.MultiplierMatrixBound
public import ASDExplicitGamma.Main.DirectionalGram
public import ASDExplicitGamma.Native.OldSignedCanonicalFluxL2
public import ASDExplicitGamma.Native.OldSignedPhysicalFluxDirectionalNorm
public import ASDExplicitGamma.Native.OldSignedPairedWeakTrace
public import ASDExplicitGamma.Triadic.VectorHaar
public import ASDExplicitGamma.Inverse.RawTraceHistory

/-! The actual top-load physical-flux carrier in the OLD frame. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Inverse
  ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped RealInnerProductSpace

noncomputable section

theorem main_directional_response_frame_eq_scaled_partial_coefficient
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (x : Vec 2) (hx : x ∈ openCubeSet Q) :
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q ω) x =
      (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x := by
  let k := mainInsertionSkewCoefficient m t Q ω
  let σ : ℝ := Annealed.sigmaBar M m
  have hval : responseCoefficientExtension k x =
      Cutoff.cutoff m ω x 1 0 +
        Real.sqrt t * (ω.1 (m + 1) x 1 0) := by
    rw [responseCoefficientExtension_eq k hx]
    rfl
  have hcut := Cutoff.cutoff_skew m ω x
  have hcut00 : Cutoff.cutoff m ω x 0 0 = 0 := by
    have hh := congrArg (fun A : Mat 2 => A 0 0) hcut
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hh
    linarith
  have hcut11 : Cutoff.cutoff m ω x 1 1 = 0 := by
    have hh := congrArg (fun A : Mat 2 => A 1 1) hcut
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hh
    linarith
  have hcut01 : Cutoff.cutoff m ω x 0 1 = -Cutoff.cutoff m ω x 1 0 := by
    have hh := congrArg (fun A : Mat 2 => A 0 1) hcut
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hh
    linarith
  have hcut00' : (∑' r : ℕ, ω.1 (m - (r : ℤ)) x 0 0) = 0 := by
    simpa only [Cutoff.cutoff_apply_entry] using hcut00
  have hcut11' : (∑' r : ℕ, ω.1 (m - (r : ℤ)) x 1 1) = 0 := by
    simpa only [Cutoff.cutoff_apply_entry] using hcut11
  have hcut01' : (∑' r : ℕ, ω.1 (m - (r : ℤ)) x 0 1) =
      -(∑' r : ℕ, ω.1 (m - (r : ℤ)) x 1 0) := by
    simpa only [Cutoff.cutoff_apply_entry] using hcut01
  have hshell := (ω.1 (m + 1)).skew_entry x
  have hshell00 : (ω.1 (m + 1)) x 0 0 = 0 := by
    have hh := hshell 0 0
    linarith
  have hshell11 : (ω.1 (m + 1)) x 1 1 = 0 := by
    have hh := hshell 1 1
    linarith
  have hshell01 : (ω.1 (m + 1)) x 0 1 = -(ω.1 (m + 1)) x 1 0 := by
    have hh := hshell 0 1
    linarith
  have hmodel : (Model.partialInsertedCoefficient M m t ω).toFun x =
      M.nu • (1 : Mat 2) + Cutoff.cutoff m ω x +
        Real.sqrt t • Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell
          (ω.1 (m + 1)) x := by
    rw [mainInsertion_coefficient]
    ext i j
    simp [RegCoeffField.add_apply, RegCoeffField.smul_apply,
      Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
  have hσ : σ = Annealed.sigmaBar M m := rfl
  have hσpos : 0 < σ := by
    rw [hσ]
    exact (Annealed.sigmaBar_characterization M m).1
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [responseFramePlanarCoefficientField_apply, responsePlanarCoefficient,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, responsePlanarJ]
    rw [hval, hmodel]
    simp only [Cutoff.cutoff_apply_entry]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
    simp [hcut00', hcut11', hcut01', hshell00, hshell11, hshell01]
    field_simp [ne_of_gt hσpos] <;> ring

/-- The physical-flux error for an arbitrary deterministic top load `e`. -/
noncomputable def mainDirectionalTopPhysicalFluxDirectionError
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) : Vec 2 → Vec 2 := by
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  exact fun x =>
    (blockMatVecMul (blockCoeffField a x)
      (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).2 k (e, 0) x)).1 - e

/-- The actual top-load physical-flux weak energy is paid by the OLD
corrector history, for every deterministic direction. -/
theorem main_directional_top_physical_flux_direction_weak_energy
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) :
    vectorWeakHaarEnergy Q
      (mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e) ≤
      2 * oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t Q ω)) *
        vecNormSq e := by
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let P : BlockVec 2 := (e, 0)
  let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).2 k P
  let F : Vec 2 → BlockVec 2 := fun x => scalarCoefficientFlux a S x - P
  have hflux := old_signed_physical_flux_directional_weak_norm Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).2 k false e
  change (oldSignedBlockWeakNorm Q F)^2 ≤
    2 * oldSignedCorrectorHistory Q a * vecNormSq e at hflux
  have hblock := old_signed_block_weak_norm_sq Q F
  have henergy : vectorWeakHaarEnergy Q (fun x => (F x).1) ≤
      (oldSignedBlockWeakNorm Q F)^2 := by
    rw [hblock]
    exact le_add_of_nonneg_right (vectorWeakHaarEnergy_nonneg Q
      (fun x => (F x).2))
  have hfield : mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e =
      fun x => (F x).1 := by
    funext x
    simp [mainDirectionalTopPhysicalFluxDirectionError, F, scalarCoefficientFlux,
      P, S, a, σ, k, oldSignedFrameCanonicalField, oldSignedCanonicalAffineField,
      blockMatVecMul]
  rw [hfield]
  exact henergy.trans hflux

/-- The actual OLD-frame affine minimizer is additive in its deterministic
load. This is the linearity needed to form the physical-flux Gram matrix. -/
theorem main_directional_old_minimizer_add
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (P R : BlockVec 2) :
    oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t Q ω) (P + R) =
    oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t Q ω) P +
    oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t Q ω) R := by
  let a := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t Q ω)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar M m).2 (mainInsertionSkewCoefficient m t Q ω)
  apply Lp.ext
  filter_upwards with x
  simp only [oldSignedFrameCanonicalField, oldSignedCanonicalAffineField,
    map_add]

/-- The actual OLD-frame affine minimizer is homogeneous in its deterministic
load, as an L² field. -/
theorem main_directional_old_minimizer_smul
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (c : ℝ) (P : BlockVec 2) :
    oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t Q ω) (c • P) =
    c • oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t Q ω) P := by
  simp only [oldSignedFrameCanonicalField, oldSignedCanonicalAffineField,
    map_smul]

/-- The representative of the actual OLD-frame minimizer is additive almost
everywhere. This transports the L² identity to the pointwise carrier used by
the Haar pairing. -/
theorem main_directional_old_minimizer_add_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (P R : BlockVec 2) :
    (fun x => oldSignedFrameCanonicalField Q M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t Q ω) (P + R) x) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      fun x => oldSignedFrameCanonicalField Q M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) P x +
        oldSignedFrameCanonicalField Q M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t Q ω) R x := by
  exact (Lp.ext_iff.mp
    (main_directional_old_minimizer_add M m t Q ω P R)).trans
      (Lp.coeFn_add
        (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t Q ω) P)
        (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t Q ω) R))

/-- The representative of the actual OLD-frame minimizer is homogeneous
almost everywhere, again with the physical measure on the source cell. -/
theorem main_directional_old_minimizer_smul_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (c : ℝ) (P : BlockVec 2) :
    (fun x => oldSignedFrameCanonicalField Q M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t Q ω) (c • P) x) =ᵐ[
        volumeMeasureOn (openCubeSet Q)]
      fun x => c • oldSignedFrameCanonicalField Q M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) P x := by
  exact (Lp.ext_iff.mp
    (main_directional_old_minimizer_smul M m t Q ω c P)).trans
      (Lp.coeFn_smul c
        (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t Q ω) P))

/-- The physical-flux error for the actual top load `e_i` and actual
local OLD-frame affine minimizer. The coefficient action is the first block
of `A S`, with the same partial-insertion coefficient used to construct `S`. -/
noncomputable def mainDirectionalTopPhysicalFluxError
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (i : Fin 2) : Vec 2 → Vec 2 := by
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let P := oldSignedPairLoad false i
  exact fun x =>
    (blockMatVecMul (blockCoeffField a x)
      (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).2 k P x)).1 - P.1

/-- The arbitrary-direction flux carrier agrees with the basis-load carrier
used in the trace. -/
theorem main_directional_top_physical_flux_error_eq_direction
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (i : Fin 2) :
    mainDirectionalTopPhysicalFluxError M m t Q ω i =
      mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (basisVec i) := by
  funext x
  simp [mainDirectionalTopPhysicalFluxError,
    mainDirectionalTopPhysicalFluxDirectionError, oldSignedPairLoad,
    blockBasis, blockMatVecMul, basisVec]

/-- The pathwise trace carrier whose two diagonal entries are the actual
top-load physical-flux weak-Haar errors. -/
noncomputable def mainDirectionalTopPhysicalFluxTrace
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) : ℝ :=
  ∑ i : Fin 2, vectorWeakHaarEnergy Q
    (mainDirectionalTopPhysicalFluxError M m t Q ω i)

/-- The physical-flux trace carrier is nonnegative pathwise. -/
theorem main_directional_top_physical_flux_trace_nonneg
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    0 ≤ mainDirectionalTopPhysicalFluxTrace M m t Q ω := by
  unfold mainDirectionalTopPhysicalFluxTrace
  exact Finset.sum_nonneg fun i _ =>
    vectorWeakHaarEnergy_nonneg Q
      (mainDirectionalTopPhysicalFluxError M m t Q ω i)

/-- Every actual arbitrary-direction physical-flux coordinate is in the
normalized-cell L² space, by coefficient action on the actual affine
minimizer. -/
theorem main_directional_top_physical_flux_direction_memLp
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) (i : Fin 2) :
    MemLp (fun x => mainDirectionalTopPhysicalFluxDirectionError
        M m t Q ω e x i) 2 (normalizedCubeMeasure Q) := by
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos (Annealed.sigmaBar M m).2 k
  let P : BlockVec 2 := (e, 0)
  let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).2 k P
  have hCoeff : MemBlockL2 (openCubeSet Q) (fun x =>
      blockMatVecMul (blockCoeffField a x) (S x)) := by
    simpa [S, a, σ, hEll, oldSignedFrameCanonicalField] using
      old_signed_canonical_coefficient_memL2 Q a hEll P
  have hfirst := memVectorL2_fst_of_memBlockL2 hCoeff
  have herr := hfirst.sub (memVectorL2_const e)
  have hcoord := memScalarL2_coord_of_memVectorL2 herr i
  change MemLp (fun x => mainDirectionalTopPhysicalFluxDirectionError
    M m t Q ω e x i) 2 (normalizedCubeMeasure Q)
  simpa [mainDirectionalTopPhysicalFluxDirectionError, S, P, a, σ, k,
    oldSignedFrameCanonicalField] using memLp_normalized_of_memL2On hcoord

private theorem main_top_flux_raw_ae_to_cube_ae
    (Q : TriadicCube 2) {P : Vec 2 → Prop}
    (hP : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), P x) :
    ∀ᵐ x ∂volume.restrict (cubeSet Q), P x := by
  rw [volumeMeasureOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at hP
  exact hP

/-- The actual physical-flux error is additive in its deterministic load
almost everywhere on the source cell. -/
theorem main_directional_top_physical_flux_direction_add_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e f : Vec 2) :
    mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (e + f) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x => mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e x +
        mainDirectionalTopPhysicalFluxDirectionError M m t Q ω f x := by
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let S (v : Vec 2) := oldSignedFrameCanonicalField Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).2 k (v, 0)
  have hS := main_directional_old_minimizer_add_ae M m t Q ω
    ((e, 0) : BlockVec 2) (f, 0)
  have hload : ((e + f, (0 : Vec 2)) : BlockVec 2) = (e, 0) + (f, 0) := by
    apply Prod.ext
    · rfl
    · exact (zero_add (0 : Vec 2)).symm
  have hAction : (fun x => blockMatVecMul (blockCoeffField a x) (S (e + f) x)) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => blockMatVecMul (blockCoeffField a x) (S e x) +
        blockMatVecMul (blockCoeffField a x) (S f x) := by
    filter_upwards [hS] with x hx
    change blockMatVecMul (blockCoeffField a x)
        (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).2 k ((e + f, 0) : BlockVec 2) x) = _
    rw [hload, hx, blockMatVecMul_add]
  have hFirst := hAction.mono fun x hx => congrArg Prod.fst hx
  have hErr : (fun x => (blockMatVecMul (blockCoeffField a x) (S (e + f) x)).1 - (e + f)) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => ((blockMatVecMul (blockCoeffField a x) (S e x)).1 - e) +
        ((blockMatVecMul (blockCoeffField a x) (S f x)).1 - f) := by
    filter_upwards [hFirst] with x hx
    rw [hx]
    funext i
    simp
    ring
  have hErr' : (fun x => mainDirectionalTopPhysicalFluxDirectionError
      M m t Q ω (e + f) x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e x +
        mainDirectionalTopPhysicalFluxDirectionError M m t Q ω f x := by
    simpa [mainDirectionalTopPhysicalFluxDirectionError, S, a, k, σ] using hErr
  exact main_top_flux_raw_ae_to_cube_ae Q hErr'

/-- The actual physical-flux error is homogeneous in its deterministic load
almost everywhere on the source cell. -/
theorem main_directional_top_physical_flux_direction_smul_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (c : ℝ) (e : Vec 2) :
    mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (c • e) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x => c • mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e x := by
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let S (v : Vec 2) := oldSignedFrameCanonicalField Q M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).2 k (v, 0)
  have hS := main_directional_old_minimizer_smul_ae M m t Q ω c
    ((e, 0) : BlockVec 2)
  have hload : ((c • e, (0 : Vec 2)) : BlockVec 2) = c • (e, 0) := by
    apply Prod.ext
    · rfl
    · exact (smul_zero c).symm
  have hAction : (fun x => blockMatVecMul (blockCoeffField a x) (S (c • e) x)) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => c • blockMatVecMul (blockCoeffField a x) (S e x) := by
    filter_upwards [hS] with x hx
    have hSx : S (c • e) x = c • S e x := by
      simp only [S]
      rw [hload, hx]
    rw [hSx, blockMatVecMul_smul]
  have hFirst := hAction.mono fun x hx => congrArg Prod.fst hx
  have hErr : (fun x => (blockMatVecMul (blockCoeffField a x) (S (c • e) x)).1 - c • e) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => c • ((blockMatVecMul (blockCoeffField a x) (S e x)).1 - e) := by
    filter_upwards [hFirst] with x hx
    rw [hx]
    funext i
    simp
    ring
  have hErr' : (fun x => mainDirectionalTopPhysicalFluxDirectionError
      M m t Q ω (c • e) x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => c • mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e x := by
    simpa [mainDirectionalTopPhysicalFluxDirectionError, S, a, k, σ] using hErr
  exact main_top_flux_raw_ae_to_cube_ae Q hErr'

/-- Every arbitrary-direction top physical-flux defect is the linear
combination of its two actual basis-load defects, a.e. on the source cell. -/
private theorem main_directional_top_physical_flux_direction_basis_expansion_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) :
    (fun x i => mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e x i) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x i => e 0 * mainDirectionalTopPhysicalFluxDirectionError M m t Q ω
          (basisVec 0) x i +
        e 1 * mainDirectionalTopPhysicalFluxDirectionError M m t Q ω
          (basisVec 1) x i := by
  have he : e = e 0 • basisVec 0 + e 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  have hadd := main_directional_top_physical_flux_direction_add_ae M m t Q ω
    (e 0 • basisVec 0) (e 1 • basisVec 1)
  have hsmul0 := main_directional_top_physical_flux_direction_smul_ae M m t Q ω
    (e 0) (basisVec 0)
  have hsmul1 := main_directional_top_physical_flux_direction_smul_ae M m t Q ω
    (e 1) (basisVec 1)
  filter_upwards [hadd, hsmul0, hsmul1] with x hadd hsmul0 hsmul1
  ext i
  rw [he, hadd, hsmul0, hsmul1]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The actual directional matrix is the weak-Haar Gram matrix of the
two actual top-load physical-flux defects. -/
noncomputable def mainDirectionalTopPhysicalFluxCovarianceMatrix
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => mainVectorWeakHaarPairing Q
    (fun x k => mainDirectionalTopPhysicalFluxDirectionError
      M m t Q ω (basisVec i) x k)
    (fun x k => mainDirectionalTopPhysicalFluxDirectionError
      M m t Q ω (basisVec j) x k)

/-- The top physical-flux covariance matrix is symmetric pathwise. -/
theorem main_directional_top_physical_flux_covariance_matrix_symm
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (i j : Fin 2) :
    mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω i j =
      mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω j i := by
  simp only [mainDirectionalTopPhysicalFluxCovarianceMatrix,
    main_vector_weak_hair_pairing_comm]

/-- The top physical-flux covariance matrix is positive semidefinite as an
actual weak-Haar Gram matrix. -/
theorem main_directional_top_physical_flux_covariance_matrix_posSemidef
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    Matrix.PosSemidef (mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω) := by
  classical
  let F : Fin 2 → Vec 2 → Fin 2 → ℝ := fun i x k =>
    mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (basisVec i) x k
  have hF : ∀ i k, MemLp (fun x => F i x k) 2 (normalizedCubeMeasure Q) := by
    intro i k
    exact main_directional_top_physical_flux_direction_memLp
      M m t Q ω (basisVec i) k
  have hMatrix : mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω =
      fun i j => mainVectorWeakHaarPairing Q (F i) (F j) := by
    ext i j
    rfl
  rw [hMatrix]
  exact main_vector_weak_hair_gram_matrix_posSemidef Q F hF

/-- The top physical-flux matrix's quadratic form is exactly the weak energy
of the actual arbitrary-direction error for every deterministic load. -/
theorem main_directional_top_physical_flux_covariance_quadratic_eq_source
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) :
    dotProduct (star e)
        (Matrix.mulVec (mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω) e) =
      vectorWeakHaarEnergy Q
        (mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e) := by
  classical
  let F : Fin 2 → Vec 2 → Fin 2 → ℝ := fun i x k =>
    mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (basisVec i) x k
  let G : Vec 2 → Fin 2 → ℝ := fun x k => e 0 * F 0 x k + e 1 * F 1 x k
  have hF : ∀ i k, MemLp (fun x => F i x k) 2 (normalizedCubeMeasure Q) := by
    intro i k
    exact main_directional_top_physical_flux_direction_memLp
      M m t Q ω (basisVec i) k
  have hG : ∀ k, MemLp (fun x => G x k) 2 (normalizedCubeMeasure Q) := by
    intro k
    exact (hF 0 k).const_mul (e 0) |>.add ((hF 1 k).const_mul (e 1))
  have hCurrent : ∀ k, MemLp
      (fun x => mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e x k)
      2 (normalizedCubeMeasure Q) := by
    intro k
    exact main_directional_top_physical_flux_direction_memLp M m t Q ω e k
  have hExpansion := main_directional_top_physical_flux_direction_basis_expansion_ae
    M m t Q ω e
  have hEnergy := main_vector_weak_hair_energy_congr_ae Q hCurrent hG hExpansion
  have hMatrix : mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω =
      fun i j => mainVectorWeakHaarPairing Q (F i) (F j) := by
    ext i j
    rfl
  rw [hMatrix]
  calc
    dotProduct (star e)
        (Matrix.mulVec (fun i j => mainVectorWeakHaarPairing Q (F i) (F j)) e) =
        vectorWeakHaarEnergy Q G :=
      main_vector_weak_hair_gram_quadratic_eq_energy Q F hF e
    _ = vectorWeakHaarEnergy Q
        (mainDirectionalTopPhysicalFluxDirectionError M m t Q ω e) := hEnergy.symm

/-- The actual top-matrix quadratic form has the sharp directional source
payment furnished by the OLD-frame Riesz estimate. -/
theorem main_directional_top_physical_flux_covariance_quadratic_le_corrector_history
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) :
    dotProduct (star e)
        (Matrix.mulVec (mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω) e) ≤
      2 * oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t Q ω)) *
        vecNormSq e := by
  rw [main_directional_top_physical_flux_covariance_quadratic_eq_source]
  exact main_directional_top_physical_flux_direction_weak_energy M m t Q ω e

/-- The two-coordinate top-load trace is paid by four times the OLD
corrector history, with no source or cap hypothesis. -/
theorem main_directional_top_physical_flux_trace_le_corrector_history
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    mainDirectionalTopPhysicalFluxTrace M m t Q ω ≤
      4 * oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t Q ω)) := by
  unfold mainDirectionalTopPhysicalFluxTrace
  calc
    (∑ i : Fin 2, vectorWeakHaarEnergy Q
      (mainDirectionalTopPhysicalFluxError M m t Q ω i)) ≤
        ∑ i : Fin 2, 2 * oldSignedCorrectorHistory Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t Q ω)) *
          vecNormSq (basisVec i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [main_directional_top_physical_flux_error_eq_direction]
      exact main_directional_top_physical_flux_direction_weak_energy
        M m t Q ω (basisVec i)
    _ = 4 * oldSignedCorrectorHistory Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t Q ω)) := by
      rw [← Finset.mul_sum]
      have hBasis : (∑ i : Fin 2, vecNormSq (basisVec i)) = 2 := by
        norm_num [Fin.sum_univ_two, vecNormSq, vecDot, basisVec]
      rw [hBasis]
      ring

/-- The Gram matrix diagonal is the actual two-coordinate trace. -/
theorem main_directional_top_physical_flux_trace_eq_covariance_matrix_trace
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    mainDirectionalTopPhysicalFluxTrace M m t Q ω =
      Matrix.trace (mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω) := by
  classical
  let F : Fin 2 → Vec 2 → Fin 2 → ℝ := fun i x k =>
    mainDirectionalTopPhysicalFluxDirectionError M m t Q ω (basisVec i) x k
  have hDiag (i : Fin 2) : mainVectorWeakHaarPairing Q (F i) (F i) =
      vectorWeakHaarEnergy Q (mainDirectionalTopPhysicalFluxError M m t Q ω i) := by
    rw [main_directional_top_physical_flux_error_eq_direction]
    apply main_vector_weak_hair_pairing_self_eq_energy
    intro k
    exact main_directional_top_physical_flux_direction_memLp
      M m t Q ω (basisVec i) k
  rw [Matrix.trace_fin_two]
  unfold mainDirectionalTopPhysicalFluxTrace
  simp only [mainDirectionalTopPhysicalFluxCovarianceMatrix, Fin.sum_univ_two]
  rw [← hDiag 0, ← hDiag 1]

/-- The expected-source trace adapter uses the same actual matrix trace, so the
existing exact multiplier-history payment applies directly to this matrix. -/
theorem main_directional_top_physical_flux_covariance_trace_le_corrector_history
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    Matrix.trace (mainDirectionalTopPhysicalFluxCovarianceMatrix M m t Q ω) ≤
      4 * oldSignedCorrectorHistory Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t Q ω)) := by
  rw [← main_directional_top_physical_flux_trace_eq_covariance_matrix_trace]
  exact main_directional_top_physical_flux_trace_le_corrector_history M m t Q ω

/-- The physical-flux trace on the source cell of side `3^(m-5)`, in the
single completed OLD frame `sigmaBar M m`. -/
noncomputable def mainSourceDirectionalTopPhysicalFluxTrace
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) : ℝ :=
  mainDirectionalTopPhysicalFluxTrace M m t (originCube 2 (m - 5)) ω

/-- Nonnegativity on the actual MA source cell. -/
theorem main_source_directional_top_physical_flux_trace_nonneg
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) :
    0 ≤ mainSourceDirectionalTopPhysicalFluxTrace M m t ω := by
  exact main_directional_top_physical_flux_trace_nonneg
    M m t (originCube 2 (m - 5)) ω

end
private theorem main_directional_response_history_real_sum
    (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    oldSignedResponseHistory Q a =
      (1 - Scalar.inverseHistoryDiscount) *
        (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
          Scalar.fullResponseDepthMax Q a j) := by
  let α := Scalar.inverseHistoryDiscount
  let b (j : ℕ) := Scalar.fullResponseDepthMax Q a j
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr Scalar.inverse_history_discount_range.2.le
  have hs : Summable (fun j : ℕ => α ^ j * b j) := by
    simpa [α, b] using old_signed_response_depth_series_summable Q a hEll
  have hterm : ∀ j, 0 ≤ α ^ j * b j := fun j =>
    mul_nonneg (pow_nonneg hα j) (Scalar.full_response_depth_max_nonneg Q a j)
  have hsumNonneg : 0 ≤ ∑' j : ℕ, α ^ j * b j := tsum_nonneg hterm
  have hseries : (∑' j : ℕ, ENNReal.ofReal (α ^ j * b j)) =
      ENNReal.ofReal (∑' j : ℕ, α ^ j * b j) :=
    (ENNReal.ofReal_tsum_of_nonneg hterm hs).symm
  unfold oldSignedResponseHistory Scalar.completeFullResponseHistory
  change (ENNReal.ofReal (1 - α) *
      ∑' j : ℕ, ENNReal.ofReal (α ^ j * b j)).toReal =
    (1 - α) * ∑' j : ℕ, α ^ j * b j
  rw [hseries, ← ENNReal.ofReal_mul h1α]
  simp only [ENNReal.toReal_ofReal (mul_nonneg h1α hsumNonneg)]

private theorem main_directional_response_history_congr
    (Q : TriadicCube 2) (a b : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hcoef : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b) :
    oldSignedResponseHistory Q a =
      (1 - Scalar.inverseHistoryDiscount) *
        (∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j *
          Scalar.fullResponseDepthMax Q b j) := by
  rw [main_directional_response_history_real_sum Q a hEll]
  apply congrArg (fun x : ℝ => (1 - Scalar.inverseHistoryDiscount) * x)
  apply tsum_congr
  intro j
  rw [old_signed_response_depth_congr Q j a b hcoef]

private theorem main_directional_trace_history_le_trace_max
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : CutoffSample 2)
    (hfinite : mainPartialInsertedTraceMaxHistory M m t ω < ⊤) :
    (oldSignedTraceHistory (originCube 2 (m - 5))
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω))).toReal ≤
      (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let σ : ℝ := Annealed.sigmaBar M m
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t Q ω)
  let d : ℕ → ℝ := fun j => descendantsAverage Q j
    (fun R => traceDefect (openCubeSet R) a 1)
  let T : ℕ → ℝ := mainPartialInsertedTraceDepthMax M m t ω
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  obtain ⟨ell, hCover⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hCube : cubeSet Q ⊆ openCubeSet (originCube 2 ell) := by
    intro x hx
    exact hCover (subset_closure hx)
  have hEllRaw := Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
    (measurableSet_cubeSet Q) hCube
  have hEllA := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ
    (mainInsertionSkewCoefficient m t Q ω)
  have hcell (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) :
      traceDefect (openCubeSet R) a 1 = rawCubeFourLoadTrace M m R t ω := by
    have hRsub : openCubeSet R ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hfield : ∀ x ∈ openCubeSet R,
        a x = (σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun) x := by
      intro x hx
      exact main_directional_response_frame_eq_scaled_partial_coefficient
        M m t Q ω x (hRsub hx)
    have hae := (ae_restrict_mem (μ := volume)
      (measurableSet_openCubeSet R)).mono hfield
    have htrace : traceDefect (openCubeSet R) a 1 =
        traceDefect (openCubeSet R)
          (σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun) 1 := by
      unfold traceDefect
      rw [coarseBlockMatrix_congr_of_ae_eq hae]
    have hEllR := hEllRaw.mono (measurableSet_cubeSet R)
      (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hframe := Cold.cold_trace_frame M.nu_pos hEllR hσ
    have htraceRaw : rawCubeFourLoadTrace M m R t ω =
        traceDefect (openCubeSet R) a 1 := by
      change traceDefect (cubeSet R)
          (Model.partialInsertedCoefficient M m t ω).toFun σ = _
      exact hframe.symm.trans htrace.symm
    exact htraceRaw.symm
  have hrawle (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) : rawCubeFourLoadTrace M m R t ω ≤ T j := by
    have hmax := Finset.le_sup
      (f := fun R => ENNReal.ofReal (rawCubeFourLoadTrace M m R t ω)) hR
    have hreal := ENNReal.toReal_mono
      (main_partial_inserted_trace_depth_max_ne_top M m t ω j) hmax
    rw [ENNReal.toReal_ofReal
      (raw_cube_four_load_trace_nonneg M m R t ht ω)] at hreal
    simpa [T, mainPartialInsertedTraceDepthMax, Inverse.historyFiniteMax] using hreal
  have hdepth (j : ℕ) : d j ≤ T j := by
    dsimp [d]
    calc
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) ≤
          descendantsAverage Q j (fun R => T j) :=
        descendantsAverage_le fun R hR => by rw [hcell j R hR]; exact hrawle j R hR
      _ = T j := descendantsAverage_const Q j (T j)
  have hTraceSeries := old_signed_trace_history_toReal Q a hEllA
  have hMaxSeries := main_partial_inserted_trace_history_real_series
    M m t ω hfinite
  have hOldEq : (oldSignedTraceHistory Q a).toReal =
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * d j := by
    rw [← hTraceSeries]
    rfl
  have hAlpha : 0 ≤ 1 - Scalar.inverseHistoryDiscount :=
    sub_nonneg.mpr Scalar.inverse_history_discount_range.2.le
  have hsumle := (old_signed_trace_depth_series_summable Q a hEllA).tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hdepth j)
      (pow_nonneg Scalar.inverse_history_discount_range.1.le j)) hMaxSeries.1
  calc
    (oldSignedTraceHistory Q a).toReal =
        (1 - Scalar.inverseHistoryDiscount) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * d j := hOldEq
    _ ≤ (1 - Scalar.inverseHistoryDiscount) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * T j :=
        mul_le_mul_of_nonneg_left hsumle hAlpha
    _ = (mainPartialInsertedTraceMaxHistory M m t ω).toReal := hMaxSeries.2

theorem main_directional_corrector_history_le_multiplier_product
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : CutoffSample 2)
    (hfinite : mainPartialInsertedTraceMaxHistory M m t ω < ⊤) :
    oldSignedCorrectorHistory (originCube 2 (m - 5))
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) ≤
      mainD * mainPartialInsertedMultiplierHistory M m t ω *
        (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t Q ω)
  let B := mainPartialInsertedMultiplierHistory M m t ω
  let H := (mainPartialInsertedTraceMaxHistory M m t ω).toReal
  have hAlpha := Scalar.inverse_history_discount_range
  have hD : 0 ≤ mainD := by unfold mainD mainAlpha; positivity
  have hB : 0 ≤ B := main_partial_inserted_multiplier_history_nonneg M m t ω
  have hH : 0 ≤ H := ENNReal.toReal_nonneg
  let σ : ℝ := Annealed.sigmaBar M m
  let b : CoeffField 2 := σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hEllA := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ
    (mainInsertionSkewCoefficient m t Q ω)
  have hcoef : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b := by
    filter_upwards [ae_restrict_mem (μ := volume)
      (measurableSet_openCubeSet Q)] with x hx
    exact main_directional_response_frame_eq_scaled_partial_coefficient
      M m t Q ω x hx
  have hrespEq := main_directional_response_history_congr Q a b hEllA hcoef
  have hresp : oldSignedResponseHistory Q a = B := by
    simpa [B, mainPartialInsertedMultiplierHistory,
      mainPartialInsertedMultiplierDepthMax, Q, b] using hrespEq
  have hrespLe : oldSignedResponseHistory Q a ≤ B := hresp.le
  have htrace := main_directional_trace_history_le_trace_max
    M m t ht ω hfinite
  have htrace0 : 0 ≤ (oldSignedTraceHistory Q a).toReal := ENNReal.toReal_nonneg
  change (1 + Scalar.inverseHistoryDiscount) *
      oldSignedResponseHistory Q a * (oldSignedTraceHistory Q a).toReal ≤ _
  calc
    (1 + Scalar.inverseHistoryDiscount) *
        oldSignedResponseHistory Q a * (oldSignedTraceHistory Q a).toReal ≤
      (1 + Scalar.inverseHistoryDiscount) * B * (oldSignedTraceHistory Q a).toReal := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrespLe (by positivity)) htrace0
    _ ≤ (1 + Scalar.inverseHistoryDiscount) * B * H :=
      mul_le_mul_of_nonneg_left htrace (mul_nonneg (by positivity) hB)
    _ = mainD * B * H := by simp [mainD, mainAlpha, Scalar.inverseHistoryDiscount]

/-- The actual top-load trace is paid pathwise by the precise local
multiplier product used by MA-MULTIPLIER-MOMENTS. This is the source-cell
bound before taking expectation; finiteness is the first component of the
exact max-history conclusion of MA-ENVELOPE-H. -/
theorem main_source_directional_top_physical_flux_trace_le_multiplier_product
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainSourceDirectionalTopPhysicalFluxTrace M m t ω ≤
        4 * mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  have hEnvelope := main_ordinary_trace_max_history_memLp_two_le_mainEnvelopeH
    M h hM hgamma m hpast t ht0 ht1
  have hfinite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainPartialInsertedTraceMaxHistory M m t ω < ⊤ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.1
  filter_upwards [hfinite] with ω hω
  have htrace := main_directional_top_physical_flux_trace_le_corrector_history
    M m t (originCube 2 (m - 5)) ω
  have hcorrector := main_directional_corrector_history_le_multiplier_product
    M m t ⟨ht0, ht1⟩ ω hω
  calc
    mainSourceDirectionalTopPhysicalFluxTrace M m t ω ≤
        4 * oldSignedCorrectorHistory (originCube 2 (m - 5))
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) := by
      simpa [mainSourceDirectionalTopPhysicalFluxTrace] using
        main_directional_top_physical_flux_trace_le_corrector_history
          M m t (originCube 2 (m - 5)) ω
    _ ≤ 4 * (mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal) :=
      mul_le_mul_of_nonneg_left hcorrector (by norm_num)
    _ = 4 * mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by ring

/-- The top-load Gram matrix inherits the actual source-cell multiplier
product trace bound, a.e. under the cutoff sample law. -/
theorem main_source_directional_top_physical_flux_covariance_trace_le_multiplier_product
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Matrix.trace (mainDirectionalTopPhysicalFluxCovarianceMatrix M m t
        (originCube 2 (m - 5)) ω) ≤
        4 * mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  have htrace := main_source_directional_top_physical_flux_trace_le_multiplier_product
    M h hM hgamma m hpast t ht0 ht1
  filter_upwards [htrace] with ω hω
  rw [← main_directional_top_physical_flux_trace_eq_covariance_matrix_trace
    M m t (originCube 2 (m - 5)) ω]
  exact hω

end ASDExplicitGamma.Main
