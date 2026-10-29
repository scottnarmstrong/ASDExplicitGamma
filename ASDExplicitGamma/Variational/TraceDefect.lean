module

public import ASDExplicitGamma.Statements.TraceDefect
public import ASDExplicitGamma.Statements.CutoffTraceDefect
public import Homogenization.CoarseGraining.BlockMatrixProperties
public import Homogenization.CoarseGraining.CubeMinimizer
public import Homogenization.CoarseGraining.MuAdmissibility
public import Homogenization.CoarseGraining.Translation
public import Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint
public import Homogenization.Geometry.TriadicCubeTranslation
public import Homogenization.Sobolev.PotentialSolenoidalL2OriginCubeBridge
public import Algsuperdiff.Section3.Cutoff.CoefficientFamily
public import Algsuperdiff.Section3.Cutoff.LawCarrier
public import Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine

/-!
# Variational and duality adapters for the frozen trace defect

This module connects the frozen trace observable to CoarseGraining's cube
minimum, records the coefficient-amplitude rescaling, and proves the cutoff
trace defect is nonnegative and measurable.
-/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

/-- The diagonal load rescaling associated with a positive coefficient
amplitude `s²`. -/
noncomputable def loadRescale {d : ℕ} (s : ℝ) (P : BlockVec d) : BlockVec d :=
  (s • P.1, s⁻¹ • P.2)

/-- The corresponding congruence of a coarse block matrix. -/
noncomputable def coarseMatrixRescale {d : ℕ} (s : ℝ) (A : BlockMat d) : BlockMat d :=
  { upperLeft := s ^ 2 • A.upperLeft
    upperRight := A.upperRight
    lowerLeft := A.lowerLeft
    lowerRight := s ^ (-2 : ℤ) • A.lowerRight }

private noncomputable def stateRescale {d : ℕ} (s : ℝ) (X : BlockState d) : BlockState d :=
  { potential := s • X.potential
    flux := s⁻¹ • X.flux }

private theorem blockMatrixOfCoeff_sq_smul {d : ℕ} {lam Lam : ℝ} (A : Mat d) (s : ℝ)
    (hs : 0 < s) (hEll : IsEllipticMatrix lam Lam A) :
    blockMatrixOfCoeff (s ^ 2 • A) =
      { upperLeft := s ^ 2 • (blockMatrixOfCoeff A).upperLeft
        upperRight := (blockMatrixOfCoeff A).upperRight
        lowerLeft := (blockMatrixOfCoeff A).lowerLeft
        lowerRight := s ^ (-2 : ℤ) • (blockMatrixOfCoeff A).lowerRight } := by
  have hpos : 0 < s ^ 2 := sq_pos_of_pos hs
  have hdet : IsUnit (symmPart A).det := isUnit_det_symmPart_of_isEllipticMatrix hEll
  have hsymm : symmPart (s ^ 2 • A) = s ^ 2 • symmPart A := by
    ext i j
    simp [symmPart, Matrix.smul_apply, smul_eq_mul]
    ring
  have hskew : skewPart (s ^ 2 • A) = s ^ 2 • skewPart A := by
    ext i j
    simp [skewPart, Matrix.smul_apply, smul_eq_mul]
    ring
  have hnew : blockMatrixOfCoeff (s ^ 2 • A) =
      blockMatrixOfDeterministicData (s ^ 2 • symmPart A) (s ^ 2 • symmPart A)
        (s ^ 2 • skewPart A) := by
    unfold blockMatrixOfCoeff
    rw [show symmPart (s ^ 2 • A) = s ^ 2 • symmPart A from hsymm,
      show skewPart (s ^ 2 • A) = s ^ 2 • skewPart A from hskew]
    rfl
  have hold : blockMatrixOfCoeff A =
      blockMatrixOfDeterministicData (symmPart A) (symmPart A) (skewPart A) := rfl
  rw [hnew, hold]
  apply blockMat_ext
  · simpa [blockMatrixOfCoeff, blockMatrixOfDeterministicData, symmPart, skewPart,
      smul_eq_mul] using
      (blockMatrixOfDeterministicData_upperLeft_smul (sigma := symmPart A)
        (sigmaStar := symmPart A) (kappa := skewPart A) hdet hpos)
  · simpa [blockMatrixOfCoeff, blockMatrixOfDeterministicData, symmPart, skewPart,
      smul_eq_mul] using
      (blockMatrixOfDeterministicData_upperRight_smul (sigma := symmPart A)
        (sigmaStar := symmPart A) (kappa := skewPart A) hdet hpos)
  · simpa [blockMatrixOfCoeff, blockMatrixOfDeterministicData, symmPart, skewPart,
      smul_eq_mul] using
      (blockMatrixOfDeterministicData_lowerLeft_smul (sigma := symmPart A)
        (sigmaStar := symmPart A) (kappa := skewPart A) hdet hpos)
  · simpa [blockMatrixOfCoeff, blockMatrixOfDeterministicData, symmPart, skewPart,
      smul_eq_mul] using
      (blockMatrixOfDeterministicData_lowerRight_smul (sigma := symmPart A)
        (sigmaStar := symmPart A) (kappa := skewPart A) hdet hpos)

private theorem blockVecDot_coarseMatrixRescale {d : ℕ} (A : BlockMat d)
    (P : BlockVec d) (s : ℝ) (hs : s ≠ 0) :
    blockVecDot P (blockMatVecMul (coarseMatrixRescale s A) P) =
      blockVecDot (loadRescale s P) (blockMatVecMul A (loadRescale s P)) := by
  simp [coarseMatrixRescale, loadRescale, blockVecDot, blockMatVecMul,
    matVecMul_smul, smul_matVecMul, vecDot_add_right, vecDot_smul_left,
    vecDot_smul_right]
  field_simp [hs]

private theorem blockEnergyDensity_sq_smul {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a) {s : ℝ} (hs : 0 < s)
    (X : BlockState d) {x : Vec d} (hx : x ∈ U) :
    blockEnergyDensity (s ^ 2 • a) X x = blockEnergyDensity a (stateRescale s X) x := by
  have hmat := blockMatrixOfCoeff_sq_smul (a x) s hs (hEll.2 x hx)
  unfold blockEnergyDensity blockCoeffField
  simp only [Pi.smul_apply]
  rw [hmat]
  exact congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
    (blockVecDot_coarseMatrixRescale (A := blockMatrixOfCoeff (a x))
      (P := X.eval x) s hs.ne')

private theorem admissible_stateRescale {d : ℕ} {U : Set (Vec d)}
    {P : BlockVec d} {X : BlockState d} {s : ℝ}
    (hX : IsBlockMuAdmissible U P X) :
    IsBlockMuAdmissible U (loadRescale s P) (stateRescale s X) := by
  have hpot : (fun x => (stateRescale s X).potential x - (loadRescale s P).1) =
      s • (fun x => X.potential x - P.1) := by
    funext x
    simp [stateRescale, loadRescale, smul_sub]
  have hflux : (fun x => (stateRescale s X).flux x - (loadRescale s P).2) =
      s⁻¹ • (fun x => X.flux x - P.2) := by
    funext x
    simp [stateRescale, loadRescale, smul_sub]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hpot]
    exact hX.1.const_smul s
  · rw [hpot]
    exact isPotentialZeroTraceOn_smul hX.2.1 s
  · rw [hflux]
    exact hX.2.2.1.const_smul s⁻¹
  · rw [hflux]
    exact isSolenoidalZeroNormalTraceOn_smul hX.2.2.2 s⁻¹

private theorem volumeAverage_blockEnergyDensity_sq_smul {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hU : MeasurableSet U) {s : ℝ} (hs : 0 < s) (X : BlockState d) :
    volumeAverage U (blockEnergyDensity (s ^ 2 • a) X) =
      volumeAverage U (blockEnergyDensity a (stateRescale s X)) := by
  unfold volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem hU] with x hx
  exact blockEnergyDensity_sq_smul hEll hs X hx

private theorem stateRescale_comp_inv {d : ℕ} (X : BlockState d) {s : ℝ} (hs : s ≠ 0) :
    stateRescale s (stateRescale s⁻¹ X) = X := by
  apply BlockState.ext <;> funext x i <;>
    simp [stateRescale, smul_smul, inv_mul_cancel₀ hs, mul_inv_cancel₀ hs]

private theorem loadRescale_inv_comp {d : ℕ} (P : BlockVec d) {s : ℝ} (hs : s ≠ 0) :
    loadRescale s⁻¹ (loadRescale s P) = P := by
  ext <;> simp [loadRescale, smul_smul, inv_mul_cancel₀ hs, mul_inv_cancel₀ hs]

private theorem muValueSet_sq_smul_eq {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hU : MeasurableSet U) {s : ℝ} (hs : 0 < s) (P : BlockVec d) :
    muValueSet U P (s ^ 2 • a) = muValueSet U (loadRescale s P) a := by
  ext t
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨stateRescale s X, admissible_stateRescale hX, ?_⟩
    exact volumeAverage_blockEnergyDensity_sq_smul hEll hU hs X
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨stateRescale s⁻¹ Y, ?_, ?_⟩
    · have hscaled := admissible_stateRescale (s := s⁻¹) hY
      simpa [loadRescale_inv_comp P hs.ne'] using hscaled
    · symm
      have henergy := volumeAverage_blockEnergyDensity_sq_smul hEll hU hs
        (stateRescale s⁻¹ Y)
      rw [stateRescale_comp_inv Y hs.ne'] at henergy
      exact henergy

/-- CoarseGraining's variational minimum obeys the exact amplitude rescaling:
`Mu(U,P,s²a) = Mu(U,(s p,s⁻¹ q),a)` for positive `s`. -/
theorem Mu_sq_smul_eq {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hU : MeasurableSet U) {s : ℝ} (hs : 0 < s) (P : BlockVec d) :
    Mu U P (s ^ 2 • a) = Mu U (loadRescale s P) a := by
  unfold Mu
  rw [muValueSet_sq_smul_eq hEll hU hs P]

/-- Coefficient-amplitude version of `Mu_sq_smul_eq`, with the square root
written as the positive scalar selected by the source coefficient scale. -/
theorem Mu_smul_eq {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    {lam Lam c : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hU : MeasurableSet U) (hc : 0 < c) (P : BlockVec d) :
    Mu U P (c • a) = Mu U (loadRescale (Real.sqrt c) P) a := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hcoef : (Real.sqrt c) ^ 2 • a = c • a := by
    ext x i j
    simp [Real.sq_sqrt (le_of_lt hc)]
  rw [← hcoef]
  exact Mu_sq_smul_eq hEll hU hs P

private theorem isEllipticMatrix_inv_smul {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix 1 (Lam / lam) (lam⁻¹ • A) := by
  rcases hA with ⟨hlam, hle, hlower, hinv⟩
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hle
  have hdet : IsUnit A.det := isUnit_det_of_isEllipticMatrix ⟨hlam, hle, hlower, hinv⟩
  have hinvScale := nonsing_inv_smul lam⁻¹ (inv_ne_zero hlam.ne') hdet
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · have hdiv : lam / lam ≤ Lam / lam := div_le_div_of_nonneg_right hle hlam.le
    simpa [div_self hlam.ne'] using hdiv
  · intro ξ
    rw [smul_matVecMul, vecDot_smul_right]
    calc
      1 * vecNormSq ξ = lam⁻¹ * (lam * vecNormSq ξ) := by field_simp [hlam.ne']
      _ ≤ lam⁻¹ * vecDot ξ (matVecMul A ξ) :=
        mul_le_mul_of_nonneg_left (hlower ξ) (inv_nonneg.mpr hlam.le)
  · intro ξ
    have hscale : (Lam / lam)⁻¹ = lam * Lam⁻¹ := by
      field_simp [hlam.ne', hLam.ne']
    calc
      (Lam / lam)⁻¹ * vecNormSq ξ = lam * (Lam⁻¹ * vecNormSq ξ) := by
        rw [hscale]
        ring
      _ ≤ lam * vecDot ξ (matVecMul A⁻¹ ξ) :=
        mul_le_mul_of_nonneg_left (hinv ξ) hlam.le
      _ = vecDot ξ (matVecMul (lam⁻¹ • A)⁻¹ ξ) := by
        rw [hinvScale]
        simp [smul_matVecMul, vecDot_smul_right, inv_inv]

private theorem isEllipticFieldOn_inv_smul {d : ℕ} {U : Set (Vec d)}
    {lam Lam : ℝ} {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn 1 (Lam / lam) U (lam⁻¹ • a) := by
  classical
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    have hrow : Measurable (fun x => if x ∈ U then a x i j else 0) :=
      (measurable_pi_iff.mp (measurable_pi_iff.mp hEll.1 i)) j
    simpa [Pi.smul_apply, smul_eq_mul] using hrow.const_mul lam⁻¹
  · intro x hx
    exact isEllipticMatrix_inv_smul (hEll.2 x hx)

private theorem isEllipticFieldOn_translateCoeffField_of_translateSet
    {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d} (z : Vec d)
    (hEll : IsEllipticFieldOn lam Lam (translateSet z U) a) :
    IsEllipticFieldOn lam Lam U (translateCoeffField z a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec d => x + z) :=
      (continuous_id.add continuous_const).measurable
    have hcomp :
        Measurable (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) :=
      hEll.1.comp hshift
    have hEq :
        (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) =
          (fun x i j => if x ∈ U then translateCoeffField z a x i j else 0) := by
      funext x i j
      have hadd_sub : x + z - z = x := by
        ext k
        simp [sub_eq_add_neg, add_assoc]
      by_cases hx : x ∈ U
      · have hxt : x + z ∈ translateSet z U := by
          rw [mem_translateSet_iff_sub_mem, hadd_sub]
          exact hx
        simp [hx, hxt]
        rfl
      · have hxt : x + z ∉ translateSet z U := by
          intro hmem
          rw [mem_translateSet_iff_sub_mem] at hmem
          rw [hadd_sub] at hmem
          exact hx hmem
        simp [hx, hxt]
    simpa [hEq] using hcomp
  · intro x hx
    have hadd_sub : x + z - z = x := by
      ext k
      simp [sub_eq_add_neg, add_assoc]
    have hxt : x + z ∈ translateSet z U := by
      rw [mem_translateSet_iff_sub_mem, hadd_sub]
      exact hx
    exact hEll.2 (x + z) hxt

private theorem hasQuadraticMu_triCube_of_isEllipticFieldOn {Q : TriadicCube 2}
    {Θ : ℝ} {a : CoeffField 2}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet Q) a) :
    HasQuadraticMu (cubeSet Q) a := by
  let z := triadicCubeShift Q
  let U := cubeSet (originCube 2 Q.scale)
  have hcube : cubeSet Q = translateSet z U := by
    simpa [z, U] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEll0 : IsEllipticFieldOn 1 Θ U (translateCoeffField z a) := by
    apply isEllipticFieldOn_translateCoeffField_of_translateSet z
    simpa [hcube, U] using hEll
  have hquad0 : HasQuadraticMu U (translateCoeffField z a) :=
    hasQuadraticMu_cube hEll0
  simpa [hcube, U] using (hasQuadraticMu_translateSet_iff z U a).2 hquad0

/-- The origin cube variational identity extends to every translated triadic
square through CoarseGraining's exact translation transport. -/
theorem mu_eq_half_coarseBlockMatrix_triCube {Q : TriadicCube 2} {Θ : ℝ}
    {a : CoeffField 2}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet Q) a) (P : BlockVec 2) :
    Mu (cubeSet Q) P a =
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
  let z := triadicCubeShift Q
  let U := cubeSet (originCube 2 Q.scale)
  have hcube : cubeSet Q = translateSet z U := by
    simpa [z, U] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEll0 : IsEllipticFieldOn 1 Θ U (translateCoeffField z a) := by
    apply isEllipticFieldOn_translateCoeffField_of_translateSet z
    simpa [hcube, U] using hEll
  have hquad0 : HasQuadraticMu U (translateCoeffField z a) := hasQuadraticMu_cube hEll0
  have hA0 : IsCoarseBlockMatrix U (translateCoeffField z a)
      (coarseBlockMatrix U (translateCoeffField z a)) := by
    have hsymm := (isCoarseBlockMatrix_coarseBlockMatrix
      (exists_coarseBlockMatrix_of_hasQuadraticMu hquad0)).1
    refine ⟨hsymm, ?_⟩
    intro P'
    exact mu_eq_half_coarseBlockMatrix_cube hEll0 P'
  have hATranslated : IsCoarseBlockMatrix (translateSet z U) a
      (coarseBlockMatrix U (translateCoeffField z a)) :=
    (isCoarseBlockMatrix_translateSet_iff z U a
      (coarseBlockMatrix U (translateCoeffField z a))).2 hA0
  have hEqFromTranslation : coarseBlockMatrix (translateSet z U) a =
      coarseBlockMatrix U (translateCoeffField z a) :=
    coarseBlockMatrix_translateSet_eq_translateCoeffField z U a
  calc
    Mu (cubeSet Q) P a = Mu (translateSet z U) P a := by rw [hcube]
    _ = (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (coarseBlockMatrix U (translateCoeffField z a)) P) := hATranslated.2 P
    _ = (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
          rw [hcube, hEqFromTranslation]

private theorem coarseMatrixRescale_symmetric {d : ℕ} {s : ℝ} (A : BlockMat d)
    (hA : IsSymmetricBlockMat A) : IsSymmetricBlockMat (coarseMatrixRescale s A) := by
  intro α β
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      have h := hA (Sum.inl i) (Sum.inl j)
      change A.upperLeft i j = A.upperLeft j i at h
      change (s ^ 2 • A.upperLeft) i j = (s ^ 2 • A.upperLeft) j i
      simpa only [Matrix.smul_apply, smul_eq_mul] using congrArg (fun x : ℝ => s ^ 2 * x) h
    | inr j =>
      have h := hA (Sum.inl i) (Sum.inr j)
      change A.upperRight i j = A.lowerLeft j i at h
      change A.upperRight i j = A.lowerLeft j i
      exact h
  | inr i =>
    cases β with
    | inl j =>
      have h := hA (Sum.inr i) (Sum.inl j)
      change A.lowerLeft i j = A.upperRight j i at h
      change A.lowerLeft i j = A.upperRight j i
      exact h
    | inr j =>
      have h := hA (Sum.inr i) (Sum.inr j)
      change A.lowerRight i j = A.lowerRight j i at h
      change (s ^ (-2 : ℤ) • A.lowerRight) i j = (s ^ (-2 : ℤ) • A.lowerRight) j i
      simpa only [Matrix.smul_apply, smul_eq_mul] using
        congrArg (fun x : ℝ => s ^ (-2 : ℤ) * x) h

private theorem coarseBlockMatrix_sq_smul_of_isEllipticFieldOn
    {U : Set (Vec 2)} {a : CoeffField 2} {Θ : ℝ}
    (hEll : IsEllipticFieldOn 1 Θ U a) (hquad : HasQuadraticMu U a)
    (hU : MeasurableSet U) {s : ℝ} (hs : 0 < s) :
    coarseBlockMatrix U (s ^ 2 • a) =
      coarseMatrixRescale s (coarseBlockMatrix U a) := by
  have hAcoarse : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix (exists_coarseBlockMatrix_of_hasQuadraticMu hquad)
  have hscaleMu : ∀ P : BlockVec 2,
      Mu U P (s ^ 2 • a) =
        (1 / 2 : ℝ) * blockVecDot P
          (blockMatVecMul (coarseMatrixRescale s (coarseBlockMatrix U a)) P) := by
    intro P
    rw [Mu_sq_smul_eq hEll hU hs P]
    rw [Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu hquad (loadRescale s P)]
    congr 1
    exact (blockVecDot_coarseMatrixRescale (coarseBlockMatrix U a) P s hs.ne').symm
  have htarget : IsCoarseBlockMatrix U (s ^ 2 • a)
      (coarseMatrixRescale s (coarseBlockMatrix U a)) := by
    exact ⟨coarseMatrixRescale_symmetric _ hAcoarse.1, hscaleMu⟩
  exact (eq_coarseBlockMatrix_of_isCoarseBlockMatrix htarget).symm

/-- The coarse matrix transforms by the same diagonal congruence as the
variational load when the coefficient is multiplied by `s²`. -/
theorem coarseBlockMatrix_sq_smul_triCube {Q : TriadicCube 2} {Θ : ℝ}
    {a : CoeffField 2} (hEll : IsEllipticFieldOn 1 Θ (cubeSet Q) a)
    {s : ℝ} (hs : 0 < s) :
    coarseBlockMatrix (cubeSet Q) (s ^ 2 • a) =
      coarseMatrixRescale s (coarseBlockMatrix (cubeSet Q) a) := by
  exact coarseBlockMatrix_sq_smul_of_isEllipticFieldOn hEll
    (hasQuadraticMu_triCube_of_isEllipticFieldOn hEll)
    (measurableSet_cubeSet Q) hs

/-- For any positive ellipticity lower bound, `Mu` is represented by the
coarse block matrix after normalizing the coefficient and rescaling the load.
The resulting identity is the unnormalized quadratic characterization. -/
theorem mu_eq_half_coarseBlockMatrix_elliptic_triCube {Q : TriadicCube 2}
    {ν Λ : ℝ} {a : CoeffField 2} (hν : 0 < ν)
    (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) (P : BlockVec 2) :
    Mu (cubeSet Q) P a =
      (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
  let a1 : CoeffField 2 := ν⁻¹ • a
  have hEll1 : IsEllipticFieldOn 1 (Λ / ν) (cubeSet Q) a1 := by
    simpa [a1] using isEllipticFieldOn_inv_smul hEll
  have hcoef : ν • a1 = a := by
    ext x i j
    simp [a1, Pi.smul_apply, hν.ne']
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsq : (Real.sqrt ν) ^ 2 = ν := Real.sq_sqrt hν.le
  have hmatrix : coarseBlockMatrix (cubeSet Q) a =
      coarseMatrixRescale (Real.sqrt ν) (coarseBlockMatrix (cubeSet Q) a1) := by
    rw [← hcoef, ← show (Real.sqrt ν) ^ 2 • a1 = ν • a1 by rw [hsq]]
    exact coarseBlockMatrix_sq_smul_triCube hEll1 hs
  calc
    Mu (cubeSet Q) P a = Mu (cubeSet Q) P (ν • a1) := by rw [← hcoef]
    _ = Mu (cubeSet Q) (loadRescale (Real.sqrt ν) P) a1 :=
      Mu_smul_eq hEll1 (measurableSet_cubeSet Q) hν P
    _ = (1 / 2 : ℝ) * blockVecDot (loadRescale (Real.sqrt ν) P)
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a1)
          (loadRescale (Real.sqrt ν) P)) := by
      exact mu_eq_half_coarseBlockMatrix_triCube hEll1
        (loadRescale (Real.sqrt ν) P)
    _ = (1 / 2 : ℝ) * blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
      rw [hmatrix]
      congr 1
      exact (blockVecDot_coarseMatrixRescale _ P (Real.sqrt ν) hs.ne').symm

/-- The coarse matrix in the frame `Mσ = diag(σ⁻¹ᐟ² I, σ¹ᐟ² I)`. -/
noncomputable def frameMatrix (σ : ℝ) (A : BlockMat 2) : BlockMat 2 :=
  { upperLeft := σ⁻¹ • A.upperLeft
    upperRight := A.upperRight
    lowerLeft := A.lowerLeft
    lowerRight := σ • A.lowerRight }

/-- The full block diagonal matrix for `Mσ = diag(σ⁻¹ᐟ² I, σ¹ᐟ² I)`. -/
noncomputable def frameDiagonal (σ : ℝ) : FullBlockMat 2 :=
  Matrix.diagonal (fun α : BlockCoord 2 =>
    match α with
    | Sum.inl _ => (σ.sqrt)⁻¹
    | Sum.inr _ => σ.sqrt)

/-- In full matrix coordinates, `frameMatrix σ A` is exactly `Mσ A Mσ`. -/
theorem toFullBlockMat_frameMatrix_eq_diagonal_congruence (σ : ℝ) (A : BlockMat 2)
    (hσ : 0 < σ) :
    toFullBlockMat (frameMatrix σ A) =
      frameDiagonal σ * toFullBlockMat A * frameDiagonal σ := by
  have hs : σ.sqrt ≠ 0 := Real.sqrt_ne_zero'.mpr hσ
  have hs2 : σ.sqrt ^ 2 = σ := Real.sq_sqrt (le_of_lt hσ)
  have hinv2 : (σ.sqrt)⁻¹ * (σ.sqrt)⁻¹ = σ⁻¹ := by
    rw [← pow_two, inv_pow, hs2]
  have hcross : (σ.sqrt)⁻¹ * σ.sqrt = 1 := inv_mul_cancel₀ hs
  ext α β
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      simp [frameDiagonal, frameMatrix, toFullBlockMat, Matrix.diagonal,
        Matrix.mul_apply]
      calc
        σ⁻¹ * A.upperLeft i j =
            ((σ.sqrt)⁻¹ * (σ.sqrt)⁻¹) * A.upperLeft i j := by rw [hinv2]
        _ = (σ.sqrt)⁻¹ * A.upperLeft i j * (σ.sqrt)⁻¹ := by ring
    | inr j =>
      simp [frameDiagonal, frameMatrix, toFullBlockMat, Matrix.diagonal,
        Matrix.mul_apply]
      calc
        A.upperRight i j = 1 * A.upperRight i j := by ring
        _ = ((σ.sqrt)⁻¹ * σ.sqrt) * A.upperRight i j := by rw [hcross]
        _ = (σ.sqrt)⁻¹ * A.upperRight i j * σ.sqrt := by ring
  | inr i =>
    cases β with
    | inl j =>
      simp [frameDiagonal, frameMatrix, toFullBlockMat, Matrix.diagonal,
        Matrix.mul_apply]
      have hcross' : σ.sqrt * (σ.sqrt)⁻¹ = 1 := mul_inv_cancel₀ hs
      calc
        A.lowerLeft i j = 1 * A.lowerLeft i j := by ring
        _ = (σ.sqrt * (σ.sqrt)⁻¹) * A.lowerLeft i j := by rw [hcross']
        _ = σ.sqrt * A.lowerLeft i j * (σ.sqrt)⁻¹ := by ring
    | inr j =>
      simp [frameDiagonal, frameMatrix, toFullBlockMat, Matrix.diagonal,
        Matrix.mul_apply]
      calc
        σ * A.lowerRight i j = (σ.sqrt * σ.sqrt) * A.lowerRight i j := by
          rw [← pow_two, hs2]
        _ = σ.sqrt * A.lowerRight i j * σ.sqrt := by ring

/-- The four normalized frame loads, parametrized by a coordinate and a sign. -/
noncomputable def orthonormalFrameLoad (i : Fin 2) (ε : ℝ) : BlockVec 2 :=
  ((Real.sqrt 2)⁻¹) •
    (blockBasis (Sum.inl i) + ε • blockBasis (Sum.inr i))

/-- The quadratic energy of an orthonormal frame load, written in the four
coarse-block entries seen by that coordinate. -/
theorem orthonormalFrameLoad_energy (A : BlockMat 2) (σ : ℝ) (i : Fin 2) (ε : ℝ)
    (hε : ε ^ 2 = 1) :
    blockVecDot (orthonormalFrameLoad i ε)
      (blockMatVecMul (frameMatrix σ A) (orthonormalFrameLoad i ε)) =
      (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i +
        ε * (A.upperRight i i + A.lowerLeft i i)) / 2 := by
  have hsq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    nlinarith [hsq]
  simp [orthonormalFrameLoad, frameMatrix, blockMatVecMul, blockVecDot,
    vecDot, matVecMul, blockBasis, Pi.single_apply]
  ring_nf
  rw [hsq, hε]
  ring

/-- The four loads `(eᵢ, ±eᵢ)/√2` are an orthonormal basis of the doubled
two-dimensional load space. -/
theorem orthonormalFrameLoad_inner (i j : Fin 2) (ε δ : ℝ)
    (hε : ε = 1 ∨ ε = -1) (hδ : δ = 1 ∨ δ = -1) :
    blockVecDot (orthonormalFrameLoad i ε) (orthonormalFrameLoad j δ) =
      if i = j ∧ ε = δ then 1 else 0 := by
  classical
  have hsq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = (1 / 2 : ℝ) := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hc : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    nlinarith [hsq]
  rcases hε with hε | hε <;> rcases hδ with hδ | hδ
  all_goals subst_vars
  all_goals
    by_cases hij : i = j
    · subst j
      simp [orthonormalFrameLoad, blockBasis, blockVecDot, vecDot,
        Pi.single_apply, hc]; norm_num
    · have hji : j ≠ i := fun h => hij h.symm
      simp [orthonormalFrameLoad, blockBasis, blockVecDot, vecDot,
        Pi.single_apply, hij, hji, hc]

private theorem mu_ge_pairing_originCube {m : ℤ} {Θ : ℝ} {a : CoeffField 2}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube 2 m)) a)
    (P : BlockVec 2) :
    vecDot P.1 P.2 ≤ Mu (cubeSet (originCube 2 m)) P a := by
  apply IsBlockMuAdmissible.mu_ge_vecDot_cubeSet_originCube_of_isEllipticFieldOn_of_integrabilityBridge hEll
  intro X hX
  exact hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn hEll

private theorem ellipticFieldOn_adjoint_originCube {m : ℤ} {Θ : ℝ}
    {a : CoeffField 2}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube 2 m)) a) :
    IsEllipticFieldOn 1 Θ (cubeSet (originCube 2 m)) (adjointCoeffField a) := by
  classical
  let U : Set (Vec 2) := cubeSet (originCube 2 m)
  have hMeas : Measurable (fun x i j => if x ∈ U then a x i j else 0) := hEll.1
  refine ⟨?_, ?_⟩
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    change Measurable (fun x : Vec 2 => if x ∈ U then a x j i else 0)
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hMeas j) i)
  · intro x hx
    exact isEllipticMatrix_transpose (hEll.2 x hx)

private theorem load_pairing_sum (A : BlockMat 2) (σ : ℝ) (hσ : 0 < σ)
    (i : Fin 2) :
    blockVecDot
        ((σ.sqrt)⁻¹ • blockBasis (Sum.inl i) + σ.sqrt • blockBasis (Sum.inr i))
        (blockMatVecMul A
          ((σ.sqrt)⁻¹ • blockBasis (Sum.inl i) + σ.sqrt • blockBasis (Sum.inr i))) +
      blockVecDot
        ((σ.sqrt)⁻¹ • blockBasis (Sum.inl i) + (-σ.sqrt) • blockBasis (Sum.inr i))
        (blockMatVecMul A
          ((σ.sqrt)⁻¹ • blockBasis (Sum.inl i) + (-σ.sqrt) • blockBasis (Sum.inr i))) =
      2 * (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i) := by
  have hs : σ.sqrt ≠ 0 := Real.sqrt_ne_zero'.mpr hσ
  have hsq : σ.sqrt ^ 2 = σ := Real.sq_sqrt (le_of_lt hσ)
  have hInvSq : (σ.sqrt)⁻¹ ^ 2 = σ⁻¹ := by
    rw [inv_pow, hsq]
  have hplus :
      blockVecDot
          (σ.sqrt⁻¹ • blockBasis (Sum.inl i) + σ.sqrt • blockBasis (Sum.inr i))
          (blockMatVecMul A
            (σ.sqrt⁻¹ • blockBasis (Sum.inl i) + σ.sqrt • blockBasis (Sum.inr i))) =
        σ.sqrt⁻¹ * σ.sqrt⁻¹ * A.upperLeft i i +
          σ.sqrt⁻¹ * σ.sqrt * A.upperRight i i +
          σ.sqrt * σ.sqrt⁻¹ * A.lowerLeft i i +
          σ.sqrt * σ.sqrt * A.lowerRight i i := by
    simp only [blockMatVecMul_add, blockMatVecMul_smul, blockVecDot_add_left,
      blockVecDot_add_right, blockVecDot_smul_left, blockVecDot_smul_right,
      blockBasis_pairing, blockMatEntry]
    ring
  have hminus :
      blockVecDot
          (σ.sqrt⁻¹ • blockBasis (Sum.inl i) + (-σ.sqrt) • blockBasis (Sum.inr i))
          (blockMatVecMul A
            (σ.sqrt⁻¹ • blockBasis (Sum.inl i) + (-σ.sqrt) • blockBasis (Sum.inr i))) =
        σ.sqrt⁻¹ * σ.sqrt⁻¹ * A.upperLeft i i +
          σ.sqrt⁻¹ * (-σ.sqrt) * A.upperRight i i +
          (-σ.sqrt) * σ.sqrt⁻¹ * A.lowerLeft i i +
          (-σ.sqrt) * (-σ.sqrt) * A.lowerRight i i := by
    simp only [blockMatVecMul_add, blockMatVecMul_smul, blockVecDot_add_left,
      blockVecDot_add_right, blockVecDot_smul_left, blockVecDot_smul_right,
      blockBasis_pairing, blockMatEntry]
    ring
  rw [hplus, hminus]
  calc
    (σ.sqrt)⁻¹ * (σ.sqrt)⁻¹ * A.upperLeft i i +
        (σ.sqrt)⁻¹ * σ.sqrt * A.upperRight i i +
        σ.sqrt * (σ.sqrt)⁻¹ * A.lowerLeft i i +
        σ.sqrt * σ.sqrt * A.lowerRight i i +
      ((σ.sqrt)⁻¹ * (σ.sqrt)⁻¹ * A.upperLeft i i +
        (σ.sqrt)⁻¹ * (-σ.sqrt) * A.upperRight i i +
        (-σ.sqrt) * (σ.sqrt)⁻¹ * A.lowerLeft i i +
        (-σ.sqrt) * (-σ.sqrt) * A.lowerRight i i) =
      2 * ((σ.sqrt)⁻¹ ^ 2 * A.upperLeft i i + σ.sqrt ^ 2 * A.lowerRight i i) := by ring
    _ = 2 * (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i) := by
      rw [hInvSq, hsq]

/-- The frozen defect is the trace of `Mσ A Mσ`, minus four. -/
theorem traceDefect_eq_framedTrace (m : ℤ) (a : CoeffField 2) (σ : ℝ) :
    traceDefect (cubeSet (originCube 2 m)) a σ =
      Matrix.trace (toFullBlockMat
        (frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 m)) a))) - 4 := by
  unfold traceDefect frameMatrix
  simp [Matrix.trace, toFullBlockMat, Fintype.sum_sum_type,
    ]
  ring

/-- For a unit-elliptic coefficient on an origin cube, each of the four
orthonormal frame loads `(eᵢ, ±eᵢ) / √2` has coarse quadratic energy at least
one.  Here `frameLoad σ i s` means the physical load obtained by applying
`diag(σ⁻¹ᐟ² I, σ¹ᐟ² I)` to that orthonormal vector. -/
theorem traceDefect_nonneg_of_unitElliptic_originCube {m : ℤ} {Θ σ : ℝ}
    {a : CoeffField 2} (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube 2 m)) a)
    (hσ : 0 < σ) :
    0 ≤ traceDefect (cubeSet (originCube 2 m)) a σ := by
  let U := cubeSet (originCube 2 m)
  let A := coarseBlockMatrix U a
  let s : ℝ := σ.sqrt
  have hs : s ≠ 0 := Real.sqrt_ne_zero'.mpr hσ
  have hEllAdj : IsEllipticFieldOn 1 Θ U (adjointCoeffField a) :=
    ellipticFieldOn_adjoint_originCube hEll
  have hsum :
      4 ≤ σ⁻¹ * Matrix.trace A.upperLeft + σ * Matrix.trace A.lowerRight := by
    have hcomponent : ∀ i : Fin 2,
        2 ≤ σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i := by
      intro i
      let u : BlockVec 2 := blockBasis (Sum.inl i)
      let v : BlockVec 2 := blockBasis (Sum.inr i)
      let Pplus : BlockVec 2 := s⁻¹ • u + s • v
      let Pminus : BlockVec 2 := s⁻¹ • u + (-s) • v
      have hdot : vecDot Pplus.1 Pplus.2 = 1 := by
        simp [Pplus, u, v, blockBasis, vecDot, Pi.smul_apply, Pi.single_apply]
        field_simp [hs]
      have hdotAdj : vecDot Pplus.1 Pplus.2 = 1 := hdot
      have hplus : 1 ≤ Mu U Pplus a := by
        have := mu_ge_pairing_originCube (a := a) hEll Pplus
        linarith
      have hminusAdj : 1 ≤ Mu U Pplus (adjointCoeffField a) := by
        have := mu_ge_pairing_originCube (a := adjointCoeffField a) hEllAdj Pplus
        linarith
      have hminus : 1 ≤ Mu U Pminus a := by
        have hflip : blockVecFlipFlux Pminus = Pplus := by
          simp [Pminus, Pplus, u, v, blockBasis, blockVecFlipFlux]
        rw [← Mu_adjointCoeffField_flipFlux U Pminus a, hflip]
        exact hminusAdj
      have hqplus : 2 ≤ blockVecDot Pplus (blockMatVecMul A Pplus) := by
        rw [mu_eq_half_coarseBlockMatrix_cube hEll Pplus] at hplus
        nlinarith
      have hqminus : 2 ≤ blockVecDot Pminus (blockMatVecMul A Pminus) := by
        rw [mu_eq_half_coarseBlockMatrix_cube hEll Pminus] at hminus
        nlinarith
      have hpair := load_pairing_sum (A := A) σ hσ i
      have hpair' :
          blockVecDot Pplus (blockMatVecMul A Pplus) +
            blockVecDot Pminus (blockMatVecMul A Pminus) =
          2 * (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i) := by
        simpa [Pplus, Pminus, u, v, s] using hpair
      nlinarith
    calc
      4 = ∑ _i : Fin 2, (2 : ℝ) := by norm_num
      _ ≤ ∑ i : Fin 2, (σ⁻¹ * A.upperLeft i i + σ * A.lowerRight i i) :=
        Finset.sum_le_sum fun i _ => hcomponent i
      _ = σ⁻¹ * Matrix.trace A.upperLeft + σ * Matrix.trace A.lowerRight := by
        simp [Matrix.trace, mul_add, add_left_comm, add_assoc]
  unfold traceDefect
  change 0 ≤ σ⁻¹ * Matrix.trace A.upperLeft + σ * Matrix.trace A.lowerRight - 4
  exact sub_nonneg.mpr hsum

private theorem traceDefect_smul_eq {Q : TriadicCube 2} {Θ c : ℝ} {a : CoeffField 2}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet Q) a) (hc : 0 < c) (σ : ℝ) :
    traceDefect (cubeSet Q) (c • a) σ = traceDefect (cubeSet Q) a (σ / c) := by
  let s := Real.sqrt c
  have hs : 0 < s := Real.sqrt_pos.2 hc
  have hcoef : s ^ 2 • a = c • a := by
    ext x i j
    simp [s, Real.sq_sqrt (le_of_lt hc)]
  have hA := coarseBlockMatrix_sq_smul_triCube hEll hs
  have hMatrix : coarseBlockMatrix (cubeSet Q) (c • a) =
      coarseMatrixRescale s (coarseBlockMatrix (cubeSet Q) a) := by
    rw [← hcoef]
    exact hA
  have hscale : s ^ (-2 : ℤ) = c⁻¹ := by
    rw [zpow_neg, zpow_ofNat, Real.sq_sqrt (le_of_lt hc)]
  have hsq : s ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
  have hUL : Matrix.trace (coarseMatrixRescale s (coarseBlockMatrix (cubeSet Q) a)).upperLeft =
      c * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft := by
    rw [coarseMatrixRescale, Matrix.trace_smul]
    simp [smul_eq_mul, hsq]
  have hLR : Matrix.trace (coarseMatrixRescale s (coarseBlockMatrix (cubeSet Q) a)).lowerRight =
      c⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
    rw [coarseMatrixRescale, Matrix.trace_smul, hscale]
    simp [smul_eq_mul]
  unfold traceDefect
  rw [hMatrix, hUL, hLR]
  have hleft : σ⁻¹ * c = (σ / c)⁻¹ := by
    by_cases hσ : σ = 0
    · simp [hσ]
    · field_simp [hσ, hc.ne']
  have hright : σ * c⁻¹ = σ / c := by
    exact (div_eq_mul_inv σ c).symm
  calc
    σ⁻¹ * (c * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft) +
        σ * (c⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight) - 4 =
      (σ⁻¹ * c) * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft +
        (σ * c⁻¹) * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight - 4 := by ring
    _ = (σ / c)⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft +
        (σ / c) * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight - 4 := by
          rw [hleft, hright]

/-- Nonnegativity on any translated triadic square follows by transporting the
normalized coefficient to its centered origin cube. -/
theorem traceDefect_nonneg_of_unitElliptic_triCube {Q : TriadicCube 2}
    {Θ σ : ℝ} {a : CoeffField 2}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet Q) a) (hσ : 0 < σ) :
    0 ≤ traceDefect (cubeSet Q) a σ := by
  let z := triadicCubeShift Q
  let U := cubeSet (originCube 2 Q.scale)
  have hcube : cubeSet Q = translateSet z U := by
    simpa [z, U] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEll0 : IsEllipticFieldOn 1 Θ U (translateCoeffField z a) := by
    apply isEllipticFieldOn_translateCoeffField_of_translateSet z
    simpa [hcube, U] using hEll
  have hTrace : traceDefect (cubeSet Q) a σ =
      traceDefect U (translateCoeffField z a) σ := by
    unfold traceDefect
    rw [hcube, coarseBlockMatrix_translateSet_eq_translateCoeffField z U a]
  rw [hTrace]
  exact traceDefect_nonneg_of_unitElliptic_originCube hEll0 hσ

/-- The trace defect is nonnegative for every locally elliptic coefficient on
a bounded triadic square, at every positive frame scale. -/
theorem traceDefect_nonneg_of_ellipticFieldOn_triCube {Q : TriadicCube 2}
    {ν Λ σ : ℝ} {a : CoeffField 2}
    (hν : 0 < ν) (hEll : IsEllipticFieldOn ν Λ (cubeSet Q) a) (hσ : 0 < σ) :
    0 ≤ traceDefect (cubeSet Q) a σ := by
  let a1 : CoeffField 2 := ν⁻¹ • a
  have hEll1 : IsEllipticFieldOn 1 (Λ / ν) (cubeSet Q) a1 := by
    simpa [a1] using isEllipticFieldOn_inv_smul hEll
  have hcoef : ν • a1 = a := by
    ext x i j
    simp [a1, Pi.smul_apply, hν.ne']
  rw [← hcoef]
  rw [traceDefect_smul_eq hEll1 hν σ]
  exact traceDefect_nonneg_of_unitElliptic_triCube hEll1 (div_pos hσ hν)

/-- Every cutoff sample is pointwise elliptic on every bounded triadic cube.
The upper constant is selected by a deterministic compact cover of the cube. -/
theorem cutoff_isEllipticFieldOn_cube (M : ABKModel 2) (n : ℤ)
    (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2) :
    ∃ Λ : ℝ, IsEllipticFieldOn M.nu Λ (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu n ω).toFun := by
  let K : Set (Vec 2) := closure (cubeSet Q)
  have hK : IsCompact K := (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨N, hcover⟩ := Cutoff.exists_nat_openOriginCube_of_isCompact hK
  have hentry : ∀ x ∈ cubeSet Q, ∀ i j,
      |Cutoff.coefficientCutoff M.nu n ω x i j| ≤
        M.nu + Cutoff.cutoffLocalControl (N : ℤ) n ω := by
    intro x hx i j
    exact Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le (N : ℤ) n ω
      (hcover (subset_closure hx)) i j
  refine ⟨((2 : ℝ) * 2 * (M.nu + Cutoff.cutoffLocalControl (N : ℤ) n ω) ^ 2 +
    M.nu ^ 2) / M.nu, ?_⟩
  simpa using Cutoff.isEllipticFieldOn_coefficientCutoff_of_entry_bound M n ω
    (measurableSet_cubeSet Q) (M.nu + Cutoff.cutoffLocalControl (N : ℤ) n ω) hentry

/-- The frozen cutoff trace defect is nonnegative for all parameters and every
sample; the cutoff ellipticity hypotheses are established pathwise above. -/
theorem cutoffTraceDefect_nonneg (M : ABKModel 2) (n k : ℤ)
    (ω : Cutoff.CutoffSample 2) :
    0 ≤ cutoffTraceDefect M n k ω := by
  change 0 ≤ traceDefect (cubeSet (originCube 2 k))
    (Cutoff.coefficientCutoff M.nu n ω).toFun (Annealed.sigmaBar M n : ℝ)
  obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M n ω (originCube 2 k)
  exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
    (Annealed.sigmaBar_characterization M n).1

/-- The frozen cutoff trace defect is genuinely measurable on its sample
space, using CoarseGraining's coefficient measurability adapters. -/
theorem cutoffTraceDefect_measurable (M : ABKModel 2) (n k : ℤ) :
    Measurable (cutoffTraceDefect M n k) := by
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu n
  have hX : Measurable X := by simpa [X] using Cutoff.measurable_coefficientCutoff M.nu n
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) := by
    intro ω
    simpa [X] using Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω
  let Q : TriadicCube 2 := originCube 2 k
  have hUL := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseB_cubeSet
    hX hEll Q
  have hLR := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet
    hX hEll Q
  have hTraceUL : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i
  have hTraceLR : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i
  change Measurable (fun ω =>
    (Annealed.sigmaBar M n : ℝ)⁻¹ *
        Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft +
      (Annealed.sigmaBar M n : ℝ) *
        Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight - 4)
  exact (hTraceUL.const_mul _).add (hTraceLR.const_mul _) |>.sub measurable_const

end ASDExplicitGamma.Variational
