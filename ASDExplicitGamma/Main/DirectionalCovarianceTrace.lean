module

public import ASDExplicitGamma.Main.EOscillationMinimizer
public import ASDExplicitGamma.Main.DirectionalPhysicalFlux
public import ASDExplicitGamma.Main.DirectionalGram
public import ASDExplicitGamma.Native.OldSignedPairedWeakTrace
public import ASDExplicitGamma.Inverse.RawWeakHistory

/-! Actual OLD-frame bottom-load trace data for directional covariance. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Native ASDExplicitGamma.Response
open ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The actual weak-Haar trace of the two bottom-load primal and reciprocal
defects at a source cell. The loads and minimizers are those of the OLD-frame
partial-insertion coefficient. -/
noncomputable def mainDirectionalBottomPairTrace
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) : ℝ :=
  let σ : ℝ := Annealed.sigmaBar M m
  let k := mainInsertionSkewCoefficient m t Q ω
  ∑ c : BlockCoord 2,
    vectorWeakHaarEnergy Q
      (oldSignedPairedDefectField Q M.nu σ M.nu_pos (Annealed.sigmaBar M m).2
        k true c)

/-- This actual two-load trace is paid by the exact OLD-frame weak-trace
proxy from the paired projection theorem. The only coefficient is the
partial insertion itself, with the same true frame throughout. -/
theorem main_directional_bottom_pair_trace_raw_proxy
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    mainDirectionalBottomPairTrace M m t Q ω ≤
      rawWeakTraceProxy
        (lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q ω)))
        (fun j => descendantsAverage Q j (fun U =>
          traceDefect (openCubeSet U)
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t Q ω)) 1)) := by
  unfold mainDirectionalBottomPairTrace
  exact old_signed_paired_weak_trace_bound Q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar M m).2
    (mainInsertionSkewCoefficient m t Q ω) true

/-- The source-cell instance used by MA-DIRECTIONAL-COVARIANCE, in the fixed
completed OLD frame and with the actual insertion sample. -/
noncomputable def mainSourceBottomPairTrace
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) : ℝ :=
  mainDirectionalBottomPairTrace M m t (originCube 2 (m - 5)) ω

/-- The actual primal bottom-load defect for an arbitrary physical direction.
Its load is the source's `(0,e)` in the fixed OLD frame. -/
noncomputable def mainDirectionalBottomPrimalDirection
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) : Vec 2 → Vec 2 :=
  fun x => (oldSignedFrameCanonicalField Q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
    (mainInsertionSkewCoefficient m t Q ω) (0, e) x).1

/-- The actual reciprocal bottom-load defect for an arbitrary physical
direction, paired with the same OLD-frame canonical minimizer. -/
noncomputable def mainDirectionalBottomReciprocalDirection
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) : Vec 2 → Vec 2 :=
  fun x => (oldSignedDualReflection Q M.nu (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t Q ω)
    (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos (Annealed.sigmaBar M m).2
      (mainInsertionSkewCoefficient m t Q ω) (0, e)) x).1 - e

/-- Every coordinate of the actual primal directional defect lies in the
normalized-cell `L²` space used by the weak-Haar pairing. -/
theorem main_directional_bottom_primal_direction_memLp
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) (i : Fin 2) :
    MemLp (fun x => mainDirectionalBottomPrimalDirection M m t Q ω e x i)
      2 (normalizedCubeMeasure Q) := by
  have hS : MemBlockL2 (openCubeSet Q)
      (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) (0, e)) := by
    exact Lp.memLp _
  have hfirst := memVectorL2_fst_of_memBlockL2 hS
  exact memLp_normalized_of_memL2On
    (memScalarL2_coord_of_memVectorL2 hfirst i)

/-- Every coordinate of the actual reciprocal directional defect is in the
normalized-cell `L²` space used by the weak-Haar pairing. -/
theorem main_directional_bottom_reciprocal_direction_memLp
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) (i : Fin 2) :
    MemLp (fun x => mainDirectionalBottomReciprocalDirection M m t Q ω e x i)
      2 (normalizedCubeMeasure Q) := by
  have hS : MemBlockL2 (openCubeSet Q)
      (oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) (0, e)) := by
    exact Lp.memLp _
  have hJ := old_signed_dual_reflection_memL2 Q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t Q ω) hS
  have hfirst := (memVectorL2_fst_of_memBlockL2 hJ).sub (memVectorL2_const e)
  exact memLp_normalized_of_memL2On
    (memScalarL2_coord_of_memVectorL2 hfirst i)

private theorem main_directional_raw_ae_to_cube_ae
    (Q : TriadicCube 2) {P : Vec 2 → Prop}
    (hP : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), P x) :
    ∀ᵐ x ∂volume.restrict (cubeSet Q), P x := by
  rw [volumeMeasureOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q] at hP
  exact hP

/-- The actual primal bottom defect is additive in the deterministic source
direction, as an a.e. identity on the source cell. -/
theorem main_directional_bottom_primal_direction_add_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e f : Vec 2) :
    mainDirectionalBottomPrimalDirection M m t Q ω (e + f) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x => mainDirectionalBottomPrimalDirection M m t Q ω e x +
        mainDirectionalBottomPrimalDirection M m t Q ω f x := by
  have hsum := main_directional_old_minimizer_add_ae M m t Q ω (0, e) (0, f)
  have hsum' :
      (fun x => oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) (0, e + f) x) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      fun x => oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) (0, e) x +
        oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
          M.nu_pos (Annealed.sigmaBar M m).2
          (mainInsertionSkewCoefficient m t Q ω) (0, f) x := by
    convert hsum using 1 <;> ext x i <;> simp
  have hsumCell := main_directional_raw_ae_to_cube_ae Q hsum'
  filter_upwards [hsumCell] with x hx
  exact congrArg Prod.fst hx

/-- The actual primal bottom defect is homogeneous in the deterministic
source direction, as an a.e. identity on the source cell. -/
theorem main_directional_bottom_primal_direction_smul_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (c : ℝ) (e : Vec 2) :
    mainDirectionalBottomPrimalDirection M m t Q ω (c • e) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x => c • mainDirectionalBottomPrimalDirection M m t Q ω e x := by
  have hsmul := main_directional_old_minimizer_smul_ae M m t Q ω c (0, e)
  have hsmul' :
      (fun x => oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) (0, c • e) x) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      fun x => c • oldSignedFrameCanonicalField Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).2
        (mainInsertionSkewCoefficient m t Q ω) (0, e) x := by
    convert hsmul using 1 <;> ext x i <;> simp
  have hsmulCell := main_directional_raw_ae_to_cube_ae Q hsmul'
  filter_upwards [hsmulCell] with x hx
  exact congrArg Prod.fst hx

/-- The actual reciprocal bottom defect is additive in the deterministic
source direction, including its affine subtraction of the load. -/
theorem main_directional_bottom_reciprocal_direction_add_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e f : Vec 2) :
    mainDirectionalBottomReciprocalDirection M m t Q ω (e + f) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x => mainDirectionalBottomReciprocalDirection M m t Q ω e x +
        mainDirectionalBottomReciprocalDirection M m t Q ω f x := by
  let S (v : Vec 2) := oldSignedFrameCanonicalField Q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
    (mainInsertionSkewCoefficient m t Q ω) (0, v)
  let J (v : Vec 2) := oldSignedDualReflection Q M.nu
    (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t Q ω) (S v)
  have hS := main_directional_old_minimizer_add_ae M m t Q ω (0, e) (0, f)
  have hS' : (fun x => S (e + f) x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => S e x + S f x := by
    convert hS using 1 <;> ext x i <;> simp [S]
  have hJ : (fun x => J (e + f) x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => J e x + J f x := by
    filter_upwards [hS'] with x hx
    change (blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q ω)) x) (S (e + f) x)).swap = _
    rw [hx, blockMatVecMul_add]
    rfl
  have hJfirst : (fun x => (J (e + f) x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => (J e x).1 + (J f x).1 := by
    filter_upwards [hJ] with x hx
    exact congrArg Prod.fst hx
  have hRaw :
      (fun x => (J (e + f) x).1 - (e + f)) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      fun x => ((J e x).1 - e) + ((J f x).1 - f) := by
    filter_upwards [hJfirst] with x hx
    rw [hx]
    funext i
    simp
    ring
  have hCell := main_directional_raw_ae_to_cube_ae Q hRaw
  change (fun x => (J (e + f) x).1 - (e + f)) =ᵐ[
      volume.restrict (cubeSet Q)]
    fun x => ((J e x).1 - e) + ((J f x).1 - f)
  exact hCell

/-- The actual reciprocal bottom defect is homogeneous in the deterministic
source direction, including its affine subtraction of the load. -/
theorem main_directional_bottom_reciprocal_direction_smul_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (c : ℝ) (e : Vec 2) :
    mainDirectionalBottomReciprocalDirection M m t Q ω (c • e) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x => c • mainDirectionalBottomReciprocalDirection M m t Q ω e x := by
  let S (v : Vec 2) := oldSignedFrameCanonicalField Q M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos (Annealed.sigmaBar M m).2
    (mainInsertionSkewCoefficient m t Q ω) (0, v)
  let J (v : Vec 2) := oldSignedDualReflection Q M.nu
    (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t Q ω) (S v)
  have hS := main_directional_old_minimizer_smul_ae M m t Q ω c (0, e)
  have hS' : (fun x => S (c • e) x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => c • S e x := by
    convert hS using 1 <;> ext x i <;> simp [S]
  have hJ : (fun x => J (c • e) x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => c • J e x := by
    filter_upwards [hS'] with x hx
    change (blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q ω)) x) (S (c • e) x)).swap = _
    rw [hx, blockMatVecMul_smul]
    rfl
  have hJfirst : (fun x => (J (c • e) x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => c • (J e x).1 := by
    filter_upwards [hJ] with x hx
    exact congrArg Prod.fst hx
  have hRaw :
      (fun x => (J (c • e) x).1 - (c • e)) =ᵐ[
          volumeMeasureOn (openCubeSet Q)]
      fun x => c • ((J e x).1 - e) := by
    filter_upwards [hJfirst] with x hx
    rw [hx]
    funext i
    simp
    ring
  have hCell := main_directional_raw_ae_to_cube_ae Q hRaw
  change (fun x => (J (c • e) x).1 - (c • e)) =ᵐ[
      volume.restrict (cubeSet Q)]
    fun x => c • ((J e x).1 - e)
  exact hCell

/-- The actual directional covariance matrix is the Gram matrix of the two
weak-Haar defect families from the bottom-load minimizers. -/
noncomputable def mainDirectionalBottomPairCovarianceMatrix
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    mainVectorWeakHaarPairing Q
      (fun x k => mainDirectionalBottomPrimalDirection M m t Q ω (basisVec i) x k)
      (fun x k => mainDirectionalBottomPrimalDirection M m t Q ω (basisVec j) x k) +
    mainVectorWeakHaarPairing Q
      (fun x k => mainDirectionalBottomReciprocalDirection M m t Q ω (basisVec i) x k)
      (fun x k => mainDirectionalBottomReciprocalDirection M m t Q ω (basisVec j) x k)

/-- The actual bottom covariance Gram matrix is symmetric pathwise. -/
theorem main_directional_bottom_pair_covariance_matrix_symm
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (i j : Fin 2) :
    mainDirectionalBottomPairCovarianceMatrix M m t Q ω i j =
      mainDirectionalBottomPairCovarianceMatrix M m t Q ω j i := by
  simp only [mainDirectionalBottomPairCovarianceMatrix,
    main_vector_weak_hair_pairing_comm]

/-- The actual bottom covariance matrix is positive semidefinite: it is the
sum of the primal and reciprocal weak-Haar Gram matrices. -/
theorem main_directional_bottom_pair_covariance_matrix_posSemidef
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    Matrix.PosSemidef (mainDirectionalBottomPairCovarianceMatrix M m t Q ω) := by
  classical
  let P : Fin 2 → Vec 2 → Fin 2 → ℝ := fun l x i =>
    mainDirectionalBottomPrimalDirection M m t Q ω (basisVec l) x i
  let R : Fin 2 → Vec 2 → Fin 2 → ℝ := fun l x i =>
    mainDirectionalBottomReciprocalDirection M m t Q ω (basisVec l) x i
  let NP : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    mainVectorWeakHaarPairing Q (P i) (P j)
  let NR : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    mainVectorWeakHaarPairing Q (R i) (R j)
  have hP : Matrix.PosSemidef NP := by
    apply main_vector_weak_hair_gram_matrix_posSemidef
    intro i k
    exact main_directional_bottom_primal_direction_memLp M m t Q ω
      (basisVec i) k
  have hR : Matrix.PosSemidef NR := by
    apply main_vector_weak_hair_gram_matrix_posSemidef
    intro i k
    exact main_directional_bottom_reciprocal_direction_memLp M m t Q ω
      (basisVec i) k
  have hsum : Matrix.PosSemidef (NP + NR) := by
    rw [add_comm NP NR]
    simpa [NP, NR] using
      (Matrix.posSemidef_sum (s := (Finset.univ : Finset Bool))
        (x := fun b => if b then NR else NP) (by
          intro b hb
          cases b <;> simp [hP, hR]))
  have hmatrix : mainDirectionalBottomPairCovarianceMatrix M m t Q ω = NP + NR := by
    ext i j
    rfl
  rw [hmatrix]
  exact hsum

/-- The actual primal bottom defect in a direction is the basis-linear
combination of its two actual basis-load defects, a.e. on the source cell. -/
private theorem main_directional_bottom_primal_direction_basis_expansion_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) :
    (fun x i => mainDirectionalBottomPrimalDirection M m t Q ω e x i) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x i => e 0 * mainDirectionalBottomPrimalDirection M m t Q ω
          (basisVec 0) x i +
        e 1 * mainDirectionalBottomPrimalDirection M m t Q ω
          (basisVec 1) x i := by
  have he : e = e 0 • basisVec 0 + e 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  have hadd := main_directional_bottom_primal_direction_add_ae M m t Q ω
    (e 0 • basisVec 0) (e 1 • basisVec 1)
  have hsmul0 := main_directional_bottom_primal_direction_smul_ae M m t Q ω
    (e 0) (basisVec 0)
  have hsmul1 := main_directional_bottom_primal_direction_smul_ae M m t Q ω
    (e 1) (basisVec 1)
  filter_upwards [hadd, hsmul0, hsmul1] with x hadd hsmul0 hsmul1
  ext i
  rw [he, hadd, hsmul0, hsmul1]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The actual reciprocal bottom defect has the same basis-linear expansion;
the affine load subtraction is included in the a.e. identities. -/
private theorem main_directional_bottom_reciprocal_direction_basis_expansion_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) :
    (fun x i => mainDirectionalBottomReciprocalDirection M m t Q ω e x i) =ᵐ[
      volume.restrict (cubeSet Q)]
      fun x i => e 0 * mainDirectionalBottomReciprocalDirection M m t Q ω
          (basisVec 0) x i +
        e 1 * mainDirectionalBottomReciprocalDirection M m t Q ω
          (basisVec 1) x i := by
  have he : e = e 0 • basisVec 0 + e 1 • basisVec 1 := by
    ext i
    fin_cases i <;> simp [basisVec]
  have hadd := main_directional_bottom_reciprocal_direction_add_ae M m t Q ω
    (e 0 • basisVec 0) (e 1 • basisVec 1)
  have hsmul0 := main_directional_bottom_reciprocal_direction_smul_ae M m t Q ω
    (e 0) (basisVec 0)
  have hsmul1 := main_directional_bottom_reciprocal_direction_smul_ae M m t Q ω
    (e 1) (basisVec 1)
  filter_upwards [hadd, hsmul0, hsmul1] with x hadd hsmul0 hsmul1
  ext i
  rw [he, hadd, hsmul0, hsmul1]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- For every deterministic direction, the actual bottom covariance matrix's
quadratic form is exactly the sum of its primal and reciprocal weak-Haar
energies. This is the source matrix definition, not merely its basis trace. -/
theorem main_directional_bottom_pair_covariance_quadratic_eq_source
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (e : Vec 2) :
    dotProduct (star e)
        (Matrix.mulVec (mainDirectionalBottomPairCovarianceMatrix M m t Q ω) e) =
      vectorWeakHaarEnergy Q
          (mainDirectionalBottomPrimalDirection M m t Q ω e) +
        vectorWeakHaarEnergy Q
          (mainDirectionalBottomReciprocalDirection M m t Q ω e) := by
  classical
  let P : Fin 2 → Vec 2 → Fin 2 → ℝ := fun l x i =>
    mainDirectionalBottomPrimalDirection M m t Q ω (basisVec l) x i
  let R : Fin 2 → Vec 2 → Fin 2 → ℝ := fun l x i =>
    mainDirectionalBottomReciprocalDirection M m t Q ω (basisVec l) x i
  let NP : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => mainVectorWeakHaarPairing Q (P i) (P j)
  let NR : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => mainVectorWeakHaarPairing Q (R i) (R j)
  have hP : ∀ i k, MemLp (fun x => P i x k) 2 (normalizedCubeMeasure Q) := by
    intro i k
    exact main_directional_bottom_primal_direction_memLp M m t Q ω
      (basisVec i) k
  have hR : ∀ i k, MemLp (fun x => R i x k) 2 (normalizedCubeMeasure Q) := by
    intro i k
    exact main_directional_bottom_reciprocal_direction_memLp M m t Q ω
      (basisVec i) k
  have hPm (k : Fin 2) : MemLp
      (fun x => e 0 * P 0 x k + e 1 * P 1 x k) 2
      (normalizedCubeMeasure Q) :=
    (hP 0 k).const_mul (e 0) |>.add ((hP 1 k).const_mul (e 1))
  have hRm (k : Fin 2) : MemLp
      (fun x => e 0 * R 0 x k + e 1 * R 1 x k) 2
      (normalizedCubeMeasure Q) :=
    (hR 0 k).const_mul (e 0) |>.add ((hR 1 k).const_mul (e 1))
  have hPexp := main_directional_bottom_primal_direction_basis_expansion_ae
    M m t Q ω e
  have hRexp := main_directional_bottom_reciprocal_direction_basis_expansion_ae
    M m t Q ω e
  have hPenergy := main_vector_weak_hair_energy_congr_ae Q
    (fun k => main_directional_bottom_primal_direction_memLp M m t Q ω e k)
    hPm hPexp
  have hRenergy := main_vector_weak_hair_energy_congr_ae Q
    (fun k => main_directional_bottom_reciprocal_direction_memLp M m t Q ω e k)
    hRm hRexp
  have hPquad := main_vector_weak_hair_gram_quadratic_eq_energy Q P hP e
  have hRquad := main_vector_weak_hair_gram_quadratic_eq_energy Q R hR e
  have hmatrix : mainDirectionalBottomPairCovarianceMatrix M m t Q ω = NP + NR := by
    ext i j
    rfl
  rw [hmatrix, Matrix.add_mulVec, dotProduct_add, hPquad, hRquad]
  rw [← hPenergy, ← hRenergy]

/-- The Gram matrix diagonal recovers exactly the existing four-coordinate
actual paired weak-Haar trace. -/
theorem main_directional_bottom_pair_trace_eq_covariance_matrix_trace
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) :
    mainDirectionalBottomPairTrace M m t Q ω =
      Matrix.trace (mainDirectionalBottomPairCovarianceMatrix M m t Q ω) := by
  classical
  let P : Fin 2 → Vec 2 → Fin 2 → ℝ := fun l x i =>
    mainDirectionalBottomPrimalDirection M m t Q ω (basisVec l) x i
  let R : Fin 2 → Vec 2 → Fin 2 → ℝ := fun l x i =>
    mainDirectionalBottomReciprocalDirection M m t Q ω (basisVec l) x i
  have hP (i : Fin 2) : mainVectorWeakHaarPairing Q (P i) (P i) =
      vectorWeakHaarEnergy Q (P i) := by
    apply main_vector_weak_hair_pairing_self_eq_energy
    intro k
    exact main_directional_bottom_primal_direction_memLp M m t Q ω
      (basisVec i) k
  have hR (i : Fin 2) : mainVectorWeakHaarPairing Q (R i) (R i) =
      vectorWeakHaarEnergy Q (R i) := by
    apply main_vector_weak_hair_pairing_self_eq_energy
    intro k
    exact main_directional_bottom_reciprocal_direction_memLp M m t Q ω
      (basisVec i) k
  have hP' (i : Fin 2) :
      mainVectorWeakHaarPairing Q
          (fun x k => mainDirectionalBottomPrimalDirection M m t Q ω
            (basisVec i) x k)
          (fun x k => mainDirectionalBottomPrimalDirection M m t Q ω
            (basisVec i) x k) =
        vectorWeakHaarEnergy Q (fun x k =>
          mainDirectionalBottomPrimalDirection M m t Q ω (basisVec i) x k) := by
    simpa only [P] using hP i
  have hR' (i : Fin 2) :
      mainVectorWeakHaarPairing Q
          (fun x k => mainDirectionalBottomReciprocalDirection M m t Q ω
            (basisVec i) x k)
          (fun x k => mainDirectionalBottomReciprocalDirection M m t Q ω
            (basisVec i) x k) =
        vectorWeakHaarEnergy Q (fun x k =>
          mainDirectionalBottomReciprocalDirection M m t Q ω (basisVec i) x k) := by
    simpa only [R] using hR i
  have htrace : mainDirectionalBottomPairTrace M m t Q ω =
      (∑ i : Fin 2, vectorWeakHaarEnergy Q (P i)) +
        ∑ i : Fin 2, vectorWeakHaarEnergy Q (R i) := by
    simp [mainDirectionalBottomPairTrace, oldSignedPairedDefectField,
      oldSignedPairLoad, blockBasis, basisVec, vectorWeakHaarEnergy,
      Pi.single_apply, mainDirectionalBottomPrimalDirection,
      mainDirectionalBottomReciprocalDirection, P, R,
      Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [htrace, Matrix.trace_fin_two]
  simp only [mainDirectionalBottomPairCovarianceMatrix, P, R,
    Fin.sum_univ_two]
  rw [← hP' 0, ← hR' 0, ← hP' 1, ← hR' 1]
  ring

/-- The source-cell trace is bounded by its actual weak-trace proxy. -/
theorem main_source_bottom_pair_trace_raw_proxy
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) :
    mainSourceBottomPairTrace M m t ω ≤
      rawWeakTraceProxy
        (lemmaVInverseDepthMax (originCube 2 (m - 5))
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)))
        (fun j => descendantsAverage (originCube 2 (m - 5)) j (fun U =>
          traceDefect (openCubeSet U)
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) 1)) := by
  exact main_directional_bottom_pair_trace_raw_proxy M m t
    (originCube 2 (m - 5)) ω

/-- The actual two-load bottom trace is paid by the OLD corrector history.
The inverse-depth proxy is compared with the response history using the
intrinsic inverse-to-response domination, then the corrected weak-history
inequality supplies its exact `1 + alpha` factor. -/
theorem main_source_bottom_pair_trace_le_corrector_history
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) :
    mainSourceBottomPairTrace M m t ω ≤
      oldSignedCorrectorHistory (originCube 2 (m - 5))
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t Q ω)
  let T : ℕ → ℝ := fun j => descendantsAverage Q j
    (fun U => traceDefect (openCubeSet U) a 1)
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t Q ω)
  have hdepth (j : ℕ) :
      Scalar.inverseHistoryDiscount ^ j * lemmaVInverseDepthMax Q a j ≤
        oldSignedResponseHistory Q a := by
    have h := actual_inverse_depth_discount_bound Q a hEll 1
      (by norm_num : 0 ≤ (1 : ℝ)) j
    have hinv : Scalar.inverseHistoryDiscount ^ j * lemmaVInverseDepthMax Q a j ≤
        oldSignedInverseHistory Q a := by
      simpa [oldSignedInverseHistory] using h
    exact hinv.trans (old_signed_inverse_history_le_response_history Q a hEll)
  have hT (j : ℕ) : 0 ≤ T j := by
    dsimp [T]
    exact old_signed_trace_depth_nonneg Q a hEll j
  have hProxySummable : Summable (fun j : ℕ =>
      Scalar.inverseHistoryDiscount ^ (2 * j) * lemmaVInverseDepthMax Q a j * T j) := by
    simpa [T] using old_signed_weak_trace_proxy_summable Q a hEll
  have hTraceSummable : Summable (fun j : ℕ =>
      Scalar.inverseHistoryDiscount ^ j * T j) := by
    simpa [T] using old_signed_trace_depth_series_summable Q a hEll
  have hRaw := raw_weak_trace_proxy_le (lemmaVInverseDepthMax Q a) T
    (oldSignedResponseHistory Q a) hdepth hT hProxySummable hTraceSummable
  rw [old_signed_trace_history_toReal Q a hEll] at hRaw
  have hProxy : rawWeakTraceProxy (lemmaVInverseDepthMax Q a) T ≤
      oldSignedCorrectorHistory Q a := by
    simpa [oldSignedCorrectorHistory] using hRaw
  calc
    mainSourceBottomPairTrace M m t ω ≤
        rawWeakTraceProxy (lemmaVInverseDepthMax Q a) T := by
          simpa [Q, a, T, mainSourceBottomPairTrace, mainDirectionalBottomPairTrace]
            using main_source_bottom_pair_trace_raw_proxy M m t ω
    _ ≤ oldSignedCorrectorHistory Q a := hProxy

/-- Exact source-cell trace payment by the max-history product consumed by
MA-MULTIPLIER-MOMENTS. -/
theorem main_source_bottom_pair_trace_le_multiplier_product
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (ω : CutoffSample 2)
    (hfinite : mainPartialInsertedTraceMaxHistory M m t ω < ⊤) :
    mainSourceBottomPairTrace M m t ω ≤
      mainD * mainPartialInsertedMultiplierHistory M m t ω *
        (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  calc
    mainSourceBottomPairTrace M m t ω ≤
        oldSignedCorrectorHistory (originCube 2 (m - 5))
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) :=
      main_source_bottom_pair_trace_le_corrector_history M m t ω
    _ ≤ mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal :=
      main_directional_corrector_history_le_multiplier_product
        M m t ht ω hfinite

/-- The actual bottom covariance Gram matrix has the same exact max-history
multiplier product trace payment, a.e. under the cutoff sample law. -/
theorem main_source_bottom_pair_covariance_matrix_trace_le_multiplier_product
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Matrix.trace (mainDirectionalBottomPairCovarianceMatrix M m t
        (originCube 2 (m - 5)) ω) ≤
        mainD * mainPartialInsertedMultiplierHistory M m t ω *
          (mainPartialInsertedTraceMaxHistory M m t ω).toReal := by
  have hEnvelope := main_ordinary_trace_max_history_memLp_two_le_mainEnvelopeH
    M h hM hgamma m hpast t ht0 ht1
  have hfinite : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainPartialInsertedTraceMaxHistory M m t ω < ⊤ := by
    simpa only [mainPartialInsertedTraceMaxHistory,
      mainOrdinaryTraceMaxHistory, mainOrdinaryTraceDepthMax,
      Scalar.inverseHistoryDiscount, mainAlpha] using hEnvelope.1
  filter_upwards [hfinite] with ω hω
  have htrace := main_source_bottom_pair_trace_le_multiplier_product
    M m t ⟨ht0, ht1⟩ ω hω
  rw [← main_directional_bottom_pair_trace_eq_covariance_matrix_trace
    M m t (originCube 2 (m - 5)) ω]
  simpa [mainSourceBottomPairTrace] using htrace

end
end ASDExplicitGamma.Main
