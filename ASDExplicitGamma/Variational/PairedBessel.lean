module

public import ASDExplicitGamma.Variational.AdapterDuality
public import ASDExplicitGamma.Variational.EnergyMap
public import ASDExplicitGamma.Triadic.KPRiesz
public import ASDExplicitGamma.Scalar.DualSpaces
public import Homogenization.CoarseGraining.Translation
public import Homogenization.Geometry.TriadicCubeTranslation
public import Homogenization.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-! Paired Bessel bounds for compatible doubled fields. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory
open ASDExplicitGamma.Scalar

noncomputable section

/-- Polarization identifies the energy pairing of the actual linear Mu minimizers
with the canonical coarse block form. -/
theorem linearMuMinimizerFamily_pairing_eq_coarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (F : LinearMuMinimizerFamily U a) (P Q : BlockVec d) :
    blockPairingAverage U a (F.field P) (F.field Q) =
      blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) Q) := by
  let B : BlockVec d → BlockVec d → ℝ := fun X Y =>
    blockPairingAverage U a (F.field X) (F.field Y)
  let q : BlockVec d → ℝ := fun X =>
    blockVecDot X (blockMatVecMul (coarseBlockMatrix U a) X)
  have hdiag (X : BlockVec d) : B X X = q X := by
    have hB : Mu U X a = (1 / 2 : ℝ) * B X X := by
      rw [F.realizes X, blockEnergyAverage_eq_half_blockPairingAverage_self]
    have hmat := F.mu_eq_half_blockVecDot_coarseBlockMatrix X
    calc
      B X X = 2 * Mu U X a := by rw [hB]; ring
      _ = q X := by
        rw [hmat]
        dsimp [q]
        ring
  have hsym (X Y : BlockVec d) : B X Y = B Y X := by
    dsimp [B, blockPairingAverage, volumeAverage]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    exact blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat
      (isSymmetricBlockMat_blockMatrixOfCoeff (a x))
      ((F.field X).eval x) ((F.field Y).eval x)
  have hBadd (X Y : BlockVec d) :
      B (X + Y) (X + Y) = B X X + B X Y + B Y X + B Y Y := by
    change blockPairingAverage U a (F.field (X + Y)) (F.field (X + Y)) = _
    rw [F.map_add]
    have hsumX : MeasureTheory.IntegrableOn
        (blockPairingIntegrand a (F.field X + F.field Y) (F.field X)) U := by
      simpa only [F.map_add] using F.pairingIntegrable (X + Y) X
    have hsumY : MeasureTheory.IntegrableOn
        (blockPairingIntegrand a (F.field X + F.field Y) (F.field Y)) U := by
      simpa only [F.map_add] using F.pairingIntegrable (X + Y) Y
    calc
      blockPairingAverage U a (F.field X + F.field Y) (F.field X + F.field Y) =
          blockPairingAverage U a (F.field X + F.field Y) (F.field X) +
            blockPairingAverage U a (F.field X + F.field Y) (F.field Y) := by
        exact blockPairingAverage_add_right U a (F.field X + F.field Y)
          (F.field X) (F.field Y) hsumX hsumY
      _ = (blockPairingAverage U a (F.field X) (F.field X) +
            blockPairingAverage U a (F.field X) (F.field Y)) +
          (blockPairingAverage U a (F.field Y) (F.field X) +
            blockPairingAverage U a (F.field Y) (F.field Y)) := by
        rw [blockPairingAverage_add_left U a (F.field X) (F.field Y) (F.field X)
              (F.pairingIntegrable X X) (F.pairingIntegrable Y X),
            blockPairingAverage_add_left U a (F.field X) (F.field Y) (F.field Y)
              (F.pairingIntegrable X Y) (F.pairingIntegrable Y Y)]
        ring
      _ = _ := by ring
  have hqadd (X Y : BlockVec d) :
      q (X + Y) = q X + 2 * blockVecDot X (blockMatVecMul (coarseBlockMatrix U a) Y) + q Y := by
    change blockVecDot (X + Y)
      (blockMatVecMul (coarseBlockMatrix U a) (X + Y)) = _
    simp only [blockMatVecMul_add, blockVecDot_add_left, blockVecDot_add_right]
    rw [blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat
      (coarseBlockMatrix_symmetric U a) Y X]
    ring
  have hdiagAdd := hdiag (P + Q)
  have hdiagP := hdiag P
  have hdiagQ := hdiag Q
  rw [hBadd, hsym, hqadd] at hdiagAdd
  dsimp [B, q] at hdiagAdd hdiagP hdiagQ ⊢
  nlinarith [hdiagAdd, hdiagP, hdiagQ, hsym P Q]

/-- Coefficient dual reflection `R A X` on the actual block field. -/
noncomputable def pairedReflectState {d : ℕ} (a : CoeffField d)
    (X : BlockState d) : BlockState d :=
  { potential := fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
    flux := fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 }

private theorem pairedReflectState_eval {d : ℕ} (a : CoeffField d)
    (X : BlockState d) (x : Vec d) :
    (pairedReflectState a X).eval x =
      (blockMatVecMul (blockCoeffField a x) (X.eval x)).swap := by
  rfl

private theorem blockCoeff_pairing_symmetric {d : ℕ} (a : CoeffField d)
    (X Y : BlockState d) (x : Vec d) :
    blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (Y.eval x)) =
      blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) :=
  blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat
    (isSymmetricBlockMat_blockMatrixOfCoeff (a x)) (X.eval x) (Y.eval x)

private theorem blockCoeff_pairingAverage_symmetric {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (X Y : BlockState d) :
    blockPairingAverage U a X Y = blockPairingAverage U a Y X := by
  unfold blockPairingAverage blockPairingIntegrand volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact blockCoeff_pairing_symmetric a X Y x

/-- Cauchy--Schwarz for the actual integrated doubled energy pairing. -/
theorem blockPairingAverage_sq_le_product {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hU : MeasurableSet U) (X Y : BlockState d)
    (hXX : MeasureTheory.IntegrableOn (blockPairingIntegrand a X X) U)
    (hXY : MeasureTheory.IntegrableOn (blockPairingIntegrand a X Y) U)
    (hYY : MeasureTheory.IntegrableOn (blockPairingIntegrand a Y Y) U) :
    (blockPairingAverage U a X Y) ^ 2 ≤
      blockPairingAverage U a X X * blockPairingAverage U a Y Y := by
  have hYX : MeasureTheory.IntegrableOn (blockPairingIntegrand a Y X) U := by
    apply hXY.congr
    filter_upwards with x
    exact blockCoeff_pairing_symmetric a X Y x
  have hXbar (t : ℝ) : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a X (X + t • Y)) U := by
    rw [blockPairingIntegrand_add_right, blockPairingIntegrand_smul_right]
    exact hXX.add (hXY.smul t)
  have hYbar (t : ℝ) : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a Y (X + t • Y)) U := by
    rw [blockPairingIntegrand_add_right, blockPairingIntegrand_smul_right]
    exact hYX.add (hYY.smul t)
  have hYtbar (t : ℝ) : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a (t • Y) (X + t • Y)) U := by
    have h := (hYbar t).smul t
    apply h.congr
    filter_upwards with x
    simp [blockPairingIntegrand_smul_left]
  have hXYt (t : ℝ) : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a X (t • Y)) U := by
    have h := (hXY).smul t
    apply h.congr
    filter_upwards with x
    simp [blockPairingIntegrand_smul_right]
  have hBoth (t : ℝ) : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a (X + t • Y) (X + t • Y)) U := by
    rw [blockPairingIntegrand_add_left]
    exact (hXbar t).add (hYtbar t)
  have hExpand (t : ℝ) : blockPairingAverage U a (X + t • Y) (X + t • Y) =
      blockPairingAverage U a X X +
        2 * t * blockPairingAverage U a X Y +
        t ^ 2 * blockPairingAverage U a Y Y := by
    rw [blockPairingAverage_add_left U a X (t • Y) (X + t • Y)
      (hXbar t) (hYtbar t)]
    have hYXs : MeasureTheory.IntegrableOn
        (blockPairingIntegrand a (t • Y) X) U := by
      have h := hYX.smul t
      apply h.congr
      filter_upwards with x
      simp [blockPairingIntegrand_smul_left]
    have hYYs : MeasureTheory.IntegrableOn
        (blockPairingIntegrand a (t • Y) (t • Y)) U := by
      have h := hYY.smul (t * t)
      apply h.congr
      filter_upwards with x
      simp [blockPairingIntegrand_smul_left, blockPairingIntegrand_smul_right,
        smul_eq_mul, mul_assoc]
    rw [blockPairingAverage_add_right U a X X (t • Y) hXX (hXYt t),
      blockPairingAverage_add_right U a (t • Y) X (t • Y) hYXs hYYs]
    rw [blockPairingAverage_smul_left, blockPairingAverage_smul_right,
      blockPairingAverage_smul_left,
      blockPairingAverage_smul_right]
    rw [blockCoeff_pairingAverage_symmetric U a Y X]
    ring
  have hquad (t : ℝ) : 0 ≤
      blockPairingAverage U a Y Y * (t * t) +
        2 * blockPairingAverage U a X Y * t +
        blockPairingAverage U a X X := by
    have hnonneg : 0 ≤ blockEnergyAverage U a (X + t • Y) := by
      unfold blockEnergyAverage
      apply volumeAverage_nonneg_of_nonneg_on hU
      intro x hx
      unfold blockEnergyDensity
      have hpoint : 0 ≤ blockVecDot ((X + t • Y).eval x)
          (blockMatVecMul (blockCoeffField a x) ((X + t • Y).eval x)) := by
        simpa [blockCoeffField] using blockMatrixOfCoeff_quadratic_nonneg
          (hEll.2 x hx) ((X + t • Y).eval x)
      exact mul_nonneg (by norm_num) hpoint
    rw [blockEnergyAverage_eq_half_blockPairingAverage_self, hExpand t] at hnonneg
    nlinarith
  have hdisc := discrim_le_zero hquad
  dsimp [discrim] at hdisc
  nlinarith [hdisc]

private theorem blockMatVecMul_blockMatrixOfCoeff_reflect {d : ℕ} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (X : BlockVec d) :
    blockMatVecMul (blockMatrixOfCoeff A)
      ((blockMatVecMul (blockMatrixOfCoeff A) X).2,
        (blockMatVecMul (blockMatrixOfCoeff A) X).1) = X.swap := by
  rcases X with ⟨p, q⟩
  let s := symmPart A
  let k := skewPart A
  let u := (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).1
  let v := (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).2
  have hdet : IsUnit s.det := by
    exact isUnit_det_symmPart_of_isEllipticMatrix hA
  have hv : v = matVecMul s⁻¹ (q - matVecMul k p) := by
    dsimp [v, s, k]
    exact blockMatVecMul_blockMatrixOfCoeff_snd A p q
  have hu : u = matVecMul s p + matVecMul k v := by
    change (blockMatVecMul (blockMatrixOfCoeff A) (p, q)).1 = _
    rw [blockMatVecMul_blockMatrixOfCoeff_fst, hv]
  have hmid : matVecMul s⁻¹ (u - matVecMul k v) = p := by
    calc
      matVecMul s⁻¹ (u - matVecMul k v) = matVecMul s⁻¹ (matVecMul s p) := by
        rw [hu]
        simp [sub_eq_add_neg, add_assoc]
      _ = p := by
        rw [matVecMul_mul, Matrix.nonsing_inv_mul s hdet]
        funext i
        simp [matVecMul, Matrix.one_apply]
  have htop : matVecMul s v + matVecMul k p = q := by
    calc
      matVecMul s v + matVecMul k p =
          matVecMul s (matVecMul s⁻¹ (q - matVecMul k p)) + matVecMul k p := by
            rw [hv]
      _ = q := by
        rw [matVecMul_mul, Matrix.mul_nonsing_inv s hdet]
        funext i
        simp [matVecMul, Matrix.one_apply, sub_add_cancel]
  apply Prod.ext
  · calc
      (blockMatVecMul (blockMatrixOfCoeff A) (v, u)).1 =
          matVecMul s v + matVecMul k (matVecMul s⁻¹ (u - matVecMul k v)) := by
            simpa [s, k] using blockMatVecMul_blockMatrixOfCoeff_fst A v u
      _ = q := by rw [hmid, htop]
  · calc
      (blockMatVecMul (blockMatrixOfCoeff A) (v, u)).2 =
          matVecMul s⁻¹ (u - matVecMul k v) := by
            simpa [s, k] using blockMatVecMul_blockMatrixOfCoeff_snd A v u
      _ = p := hmid

/-- Applying the coefficient after dual reflection recovers the component swap. -/
theorem pairedReflectState_action {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (X : BlockState d) {x : Vec d} (hx : x ∈ U) :
    blockMatVecMul (blockCoeffField a x) ((pairedReflectState a X).eval x) =
      (X.eval x).swap := by
  simpa [pairedReflectState_eval, blockCoeffField, Prod.swap] using
    blockMatVecMul_blockMatrixOfCoeff_reflect (hEll.2 x hx) (X.eval x)

private theorem memVectorL2_upperImage {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {X : BlockState d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hX : BlockResponseSpace a U X) (hFlux : MemVectorL2 U X.flux) :
    MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) := by
  have hPot : MemVectorL2 U X.potential := blockResponse_potential_memL2_of_mem_responseSpace hX
  have hLower := blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    hX hFlux hEll
  have hSymm := memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hPot
  have hSkew := memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hLower
  have hsum : MemVectorL2 U
      (fun x => matVecMul (symmPart (a x)) (X.potential x) +
        matVecMul (skewPart (a x))
          ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := hSymm.add hSkew
  have hEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) =
        (fun x => matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x))
            ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := by
    funext x
    change (blockMatVecMul (blockMatrixOfCoeff (a x))
        (X.potential x, X.flux x)).1 =
      matVecMul (symmPart (a x)) (X.potential x) +
        matVecMul (skewPart (a x))
          ((blockMatVecMul (blockMatrixOfCoeff (a x))
            (X.potential x, X.flux x)).2)
    rw [blockMatVecMul_blockMatrixOfCoeff_fst,
      blockMatVecMul_blockMatrixOfCoeff_snd]
  simpa [hEq] using hsum

private theorem pairedReflectState_mem_responseSpace {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {X : BlockState d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hX : BlockResponseSpace a U X) (hFlux : MemVectorL2 U X.flux) :
    BlockResponseSpace a U (pairedReflectState a X) := by
  have hLower := blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    hX hFlux hEll
  have hLowerPot : IsPotentialOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
    apply IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain hConv) hLower
    intro g hg hsol
    exact blockResponse_lowerImage_orthogonal_of_mem_responseSpace hX hsol
  have hUpperSol : IsSolenoidalOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) :=
    blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace hX
  refine ⟨?_, ?_, ?_⟩
  · change IsPotentialOn U (pairedReflectState a X).potential
    simpa [pairedReflectState] using hLowerPot
  · change IsSolenoidalOn U (pairedReflectState a X).flux
    simpa [pairedReflectState] using hUpperSol
  · intro Y hY
    have hpoint : ∀ x ∈ U,
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x) ((pairedReflectState a X).eval x)) =
          vecDot (Y.potential x) (X.flux x) + vecDot (Y.flux x) (X.potential x) := by
      intro x hx
      rw [pairedReflectState_action hEll X hx]
      simp [BlockState.eval, blockVecDot, vecDot_comm]
    have hzero₁ : ∫ x in U, vecDot (Y.potential x) (X.flux x)
        ∂MeasureTheory.volume = 0 := by
      rcases hY.1 with ⟨φ, hφ⟩
      have hz := hX.2.1 φ
      simpa [hφ, vecDot_comm] using hz
    have hzero₂ : ∫ x in U, vecDot (Y.flux x) (X.potential x)
        ∂MeasureTheory.volume = 0 := by
      rcases hX.1 with ⟨φ, hφ⟩
      have hz := hY.2 φ
      simpa [hφ, vecDot_comm] using hz
    have hYpotL2 : MemVectorL2 U Y.potential := by
      rcases hY.1 with ⟨φ, hφ⟩
      simpa [hφ] using φ.grad_memVectorL2
    have hTerm1Int : MeasureTheory.IntegrableOn
        (fun x => vecDot (Y.potential x) (X.flux x)) U :=
      integrableOn_vecDot_of_memVectorL2 hYpotL2 hFlux
    have hrewrite :
        ∫ x in U, blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x)
            ((pairedReflectState a X).eval x)) ∂MeasureTheory.volume =
        ∫ x in U,
          (vecDot (Y.potential x) (X.flux x) +
            vecDot (Y.flux x) (X.potential x)) ∂MeasureTheory.volume := by
      apply setIntegral_congr_fun (measurableSet_of_isEllipticFieldOn hEll)
      intro x hx
      simpa only [Function.comp_apply] using hpoint x hx
    rw [hrewrite]
    by_cases hTerm2Int : MeasureTheory.IntegrableOn
        (fun x => vecDot (Y.flux x) (X.potential x)) U
    · rw [MeasureTheory.integral_add hTerm1Int hTerm2Int, hzero₁, hzero₂]
      simp
    · have hSumNotInt : ¬ MeasureTheory.IntegrableOn
          (fun x => vecDot (Y.potential x) (X.flux x) +
            vecDot (Y.flux x) (X.potential x)) U := by
        intro hSumInt
        exact hTerm2Int ((MeasureTheory.integrable_add_iff_integrable_right'
          (μ := MeasureTheory.volume.restrict U) hTerm1Int).mp hSumInt)
      rw [MeasureTheory.integral_undef hSumNotInt]

/-- Mean potential component of a compatible block field. -/
noncomputable def pairedPotentialMean {d : ℕ} (U : Set (Vec d))
    (X : BlockState d) : Vec d := volumeAverageVec U X.potential

/-- Mean second component of the coefficient image of a compatible block field. -/
noncomputable def pairedFluxImageMean {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (X : BlockState d) : Vec d :=
  volumeAverageVec U (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2)

private theorem admissibleCorrection_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {P : BlockVec d}
    {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    MemBlockL2 U (fun x =>
      ((hX.toCorrectionFieldDataOfAdmissible).potential x,
        (hX.toCorrectionFieldDataOfAdmissible).flux x)) := by
  exact memBlockL2_blockField (hX.toCorrectionFieldDataOfAdmissible).potential_memL2
    (hX.toCorrectionFieldDataOfAdmissible).flux_memL2

/-- The mean of the second coefficient image is represented by an actual
pure-bottom minimizer. -/
private theorem pureBottom_represents_fluxImageMean {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (F : LinearMuMinimizerFamily U a)
    (W : BlockState d) (hW : BlockResponseSpace a U W)
    (hWmem : MemBlockL2 U W.eval) (e : Vec d) :
    blockPairingAverage U a W (F.field (0, e)) =
      vecDot e (pairedFluxImageMean U a W) := by
  let S := F.field (0, e)
  let C : BlockState d := { potential := fun _ => 0, flux := fun _ => e }
  have hAdm : IsBlockMuAdmissible U (0, e) S := F.admissible (0, e)
  let Y : BlockState d :=
    { potential := hAdm.toCorrectionFieldDataOfAdmissible.potential
      flux := hAdm.toCorrectionFieldDataOfAdmissible.flux }
  have hYmem : MemBlockL2 U Y.eval := by
    change MemBlockL2 U (fun x => (Y.potential x, Y.flux x))
    simpa [Y] using admissibleCorrection_memBlockL2 hAdm
  have hYS : MeasureTheory.IntegrableOn (blockPairingIntegrand a Y W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hYmem hWmem hEll
  have hCS : MeasureTheory.IntegrableOn (blockPairingIntegrand a C W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (by
        change MemBlockL2 U (blockField C.potential C.flux)
        exact memBlockL2_blockField
          (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := (0 : Vec d)))
          (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := e)))
      hWmem hEll
  have hsplit : S = Y + C := by
    apply BlockState.ext
    · funext x
      change S.potential x = Y.potential x + C.potential x
      simp [Y, C, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible]
    · funext x
      change S.flux x = S.flux x - e + e
      exact (sub_add_cancel _ _).symm
  have htest : IsBlockTestOn U Y := by
    exact ⟨hAdm.isPotentialZeroTrace, hAdm.isSolenoidalZeroNormalTrace⟩
  have hzeroInt :
      ∫ x in U, blockPairingIntegrand a Y W x ∂MeasureTheory.volume = 0 :=
    hW.2.2 Y htest
  have hzero : blockPairingAverage U a Y W = 0 := by
    exact volumeAverage_eq_zero_of_integral_eq_zero hzeroInt
  have hconst : blockPairingAverage U a C W =
      vecDot e (pairedFluxImageMean U a W) := by
    have hcoord : ∀ i, MeasureTheory.IntegrableOn
        (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2 i) U := by
      intro i
      exact CorrectionFieldData.integrableOn_coord_of_memVectorL2
        (blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
          hW (by
            simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hWmem) hEll) i
    calc
      blockPairingAverage U a C W = volumeAverage U
          (fun x => vecDot e ((blockMatVecMul (blockCoeffField a x) (W.eval x)).2)) := by
        unfold blockPairingAverage
        congr 1
        funext x
        simp [C, blockPairingIntegrand, BlockState.eval, blockVecDot,
          blockCoeffField, vecDot]
      _ = vecDot e (pairedFluxImageMean U a W) := by
        exact volumeAverage_vecDot_left e
          (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) hcoord
  calc
    blockPairingAverage U a W S = blockPairingAverage U a S W :=
      blockCoeff_pairingAverage_symmetric U a W S
    _ = blockPairingAverage U a (Y + C) W := by rw [← hsplit]
    _ = blockPairingAverage U a Y W + blockPairingAverage U a C W :=
      blockPairingAverage_add_left U a Y C W hYS hCS
    _ = vecDot e (pairedFluxImageMean U a W) := by rw [hzero, hconst]; ring

/-- The first-component mean is represented by the reflected actual
pure-bottom minimizer. -/
private theorem reflectedBottom_represents_potentialMean {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hConv : IsOpenBoundedConvexDomain U)
    (F : LinearMuMinimizerFamily U a)
    (hFresp : ∀ P : BlockVec d, BlockResponseSpace a U (F.field P))
    (W : BlockState d) (hWpot : IsBlockPotentialOn U W)
    (hWsol : IsBlockSolenoidalOn U W)
    (hWmem : MemBlockL2 U W.eval) (e : Vec d) :
    blockPairingAverage U a W (pairedReflectState a (F.field (0, e))) =
      vecDot e (pairedPotentialMean U W) := by
  let S := F.field (0, e)
  let J := pairedReflectState a S
  let ha := F.admissible (0, e)
  have hSmem : MemBlockL2 U S.eval := ha.memBlockL2_eval
  have hSflux : MemVectorL2 U S.flux := by
    simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hSmem
  have hSresp : BlockResponseSpace a U S := hFresp (0, e)
  have hJresp := pairedReflectState_mem_responseSpace hConv hEll hSresp hSflux
  have hJpot : MemVectorL2 U J.potential :=
    blockResponse_potential_memL2_of_mem_responseSpace hJresp
  have hJflux : MemVectorL2 U J.flux := memVectorL2_upperImage hEll hSresp hSflux
  have hJmem : MemBlockL2 U J.eval := by
    change MemBlockL2 U (fun x => (J.potential x, J.flux x))
    exact memBlockL2_blockField hJpot hJflux
  have hInt : MeasureTheory.IntegrableOn (blockPairingIntegrand a W J) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hJmem hEll
  change IsPotentialOn U W.potential at hWpot
  rcases hWpot with ⟨w, hw⟩
  have hWpotMem : MemVectorL2 U W.potential := by
    rw [← hw]
    exact w.grad_memVectorL2
  have hcoordPot : ∀ i, MeasureTheory.IntegrableOn (fun x => W.potential x i) U := by
    intro i
    exact CorrectionFieldData.integrableOn_coord_of_memVectorL2
      hWpotMem i
  have hSpot : MemVectorL2 U S.potential := by
    simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 hSmem
  have hfluxCorr : MemVectorL2 U (fun x => S.flux x - e) := ha.fluxCorrection_memL2
  have hprod₁ : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.potential x) (S.flux x - e)) U :=
    integrableOn_vecDot_of_memVectorL2
      hWpotMem hfluxCorr
  have hprod₂ : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.flux x) (S.potential x)) U :=
    integrableOn_vecDot_of_memVectorL2
      (by simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hWmem) hSpot
  have hzero₁ : ∫ x in U, vecDot (W.potential x) (S.flux x - e)
      ∂MeasureTheory.volume = 0 := by
    have hz := ha.isSolenoidalZeroNormalTrace w
    simpa [hw, vecDot_comm] using hz
  have hzero₂ : ∫ x in U, vecDot (W.flux x) (S.potential x)
      ∂MeasureTheory.volume = 0 := by
    change IsSolenoidalOn U W.flux at hWsol
    rcases ha.isPotentialZeroTrace with ⟨u, hu⟩
    have hz := hWsol u
    simpa [hu] using hz
  have hzeroAvg₁ : volumeAverage U
      (fun x => vecDot (W.potential x) (S.flux x - e)) = 0 :=
    volumeAverage_eq_zero_of_integral_eq_zero hzero₁
  have hzeroAvg₂ : volumeAverage U
      (fun x => vecDot (W.flux x) (S.potential x)) = 0 :=
    volumeAverage_eq_zero_of_integral_eq_zero hzero₂
  have hconstInt : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.potential x) e) U :=
    integrableOn_vecDot_of_memVectorL2
      hWpotMem
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := e))
  have hsumInt : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.potential x) (S.flux x - e) +
        vecDot (W.potential x) e) U := hprod₁.add hconstInt
  have hsumPoint : (fun x => vecDot (W.potential x) (S.flux x)) =
      fun x => vecDot (W.potential x) (S.flux x - e) +
        vecDot (W.potential x) e := by
    funext x
    calc
      vecDot (W.potential x) (S.flux x) =
          vecDot (W.potential x) ((S.flux x - e) + e) := by
            congr 1
            exact (sub_add_cancel _ _).symm
      _ = vecDot (W.potential x) (S.flux x - e) +
          vecDot (W.potential x) e := vecDot_add_right _ _ _
  have hprodFirst : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.potential x) (S.flux x)) U := by
    apply hsumInt.congr
    filter_upwards with x
    exact (congrFun hsumPoint x).symm
  have hmain : blockPairingAverage U a W J =
      volumeAverage U (fun x => vecDot (W.potential x) (S.flux x)) +
        volumeAverage U (fun x => vecDot (W.flux x) (S.potential x)) := by
    have hRaw : ∫ x in U, blockPairingIntegrand a W J x ∂MeasureTheory.volume =
        ∫ x in U, vecDot (W.potential x) (S.flux x) +
          vecDot (W.flux x) (S.potential x) ∂MeasureTheory.volume := by
      apply setIntegral_congr_fun (measurableSet_of_isEllipticFieldOn hEll)
      intro x hx
      change blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField a x)
          ((pairedReflectState a S).eval x)) = _
      rw [pairedReflectState_action hEll S hx]
      simp [BlockState.eval, blockVecDot]
    calc
      blockPairingAverage U a W J = volumeAverage U
          (fun x => vecDot (W.potential x) (S.flux x) +
            vecDot (W.flux x) (S.potential x)) := by
        unfold blockPairingAverage volumeAverage
        rw [hRaw]
      _ = volumeAverage U (fun x => vecDot (W.potential x) (S.flux x)) +
          volumeAverage U (fun x => vecDot (W.flux x) (S.potential x)) :=
        volumeAverage_add hprodFirst hprod₂
  have hmeanSource : volumeAverage U
      (fun x => vecDot (W.potential x) (S.flux x)) = volumeAverage U
        (fun x => vecDot (W.potential x) (S.flux x - e) +
          vecDot (W.potential x) e) := by
    have hRaw : ∫ x in U, vecDot (W.potential x) (S.flux x) ∂MeasureTheory.volume =
        ∫ x in U, vecDot (W.potential x) (S.flux x - e) +
          vecDot (W.potential x) e ∂MeasureTheory.volume := by
      apply setIntegral_congr_fun (measurableSet_of_isEllipticFieldOn hEll)
      intro x hx
      exact congrFun hsumPoint x
    unfold volumeAverage
    rw [hRaw]
  rw [hmain, hzeroAvg₂, hmeanSource]
  change volumeAverage U
      ((fun x => vecDot (W.potential x) (S.flux x - e)) +
        (fun x => vecDot (W.potential x) e)) + 0 =
      vecDot e (pairedPotentialMean U W)
  rw [volumeAverage_add hprod₁ hconstInt, hzeroAvg₁]
  rw [volumeAverage_vecDot_right W.potential e hcoordPot]
  rw [vecDot_comm]
  simp only [zero_add, add_zero]
  change vecDot e (fun i => volumeAverage U (fun x => W.potential x i)) =
    vecDot e (volumeAverageVec U W.potential)
  apply congrArg (vecDot e)
  funext i
  rfl

/-- Dual reflection preserves the integrated doubled energy pairing. -/
theorem pairedReflect_pairingAverage_isometry {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (X Y : BlockState d) :
    blockPairingAverage U a (pairedReflectState a X) (pairedReflectState a Y) =
      blockPairingAverage U a X Y := by
  unfold blockPairingAverage volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)]
    with x hx
  change blockVecDot ((pairedReflectState a X).eval x)
      (blockMatVecMul (blockCoeffField a x) ((pairedReflectState a Y).eval x)) =
    blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (Y.eval x))
  rw [pairedReflectState_action hEll Y hx, pairedReflectState_eval]
  calc
    blockVecDot ((blockMatVecMul (blockCoeffField a x) (X.eval x)).swap)
        ((Y.eval x).swap) =
      blockVecDot (blockMatVecMul (blockCoeffField a x) (X.eval x)) (Y.eval x) := by
        rcases blockMatVecMul (blockCoeffField a x) (X.eval x) with ⟨p, q⟩
        rcases Y.eval x with ⟨r, s⟩
        simp [blockVecDot, add_comm]
    _ = blockVecDot (Y.eval x)
        (blockMatVecMul (blockCoeffField a x) (X.eval x)) := blockVecDot_comm _ _
    _ = blockVecDot (X.eval x)
        (blockMatVecMul (blockCoeffField a x) (Y.eval x)) :=
      (blockCoeff_pairing_symmetric a X Y x).symm

/-- A pure-bottom minimizer has zero mean potential. -/
theorem pureBottom_potentialMean_eq_zero {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : (MeasureTheory.volume U).toReal ≠ 0) {a : CoeffField d}
    (F : LinearMuMinimizerFamily U a) (e : Vec d) :
    pairedPotentialMean U (F.field (0, e)) = 0 := by
  let S := F.field (0, e)
  let hAdm := F.admissible (0, e)
  have hmean := hAdm.toCorrectionFieldDataOfAdmissible.average_potential_affine
    hvol (0 : Vec d)
  funext i
  have hi := congrFun hmean i
  change volumeAverage U (fun x => S.potential x i) = 0
  simpa [pairedPotentialMean, volumeAverage, Homogenization.integralAverage,
    S, hAdm, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible] using hi

/-- Abstract paired Bessel estimate from an actual linear family of Mu minimizers.
The only structural inputs beyond ellipticity are the response-space property of
that family and positivity of its actual coarse lower-right block. -/
private theorem pairedBessel_of_linearMuMinimizerFamily
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ}
    (hConv : IsOpenBoundedConvexDomain U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (F : LinearMuMinimizerFamily U a)
    (hFresp : ∀ P : BlockVec d, BlockResponseSpace a U (F.field P))
    (W : BlockState d) (hWresp : BlockResponseSpace a U W)
    (hWmem : MemBlockL2 U W.eval)
    (hD : (coarseBlockMatrix U a).lowerRight.PosDef) :
    vecDot (pairedPotentialMean U W)
        (matVecMul (coarseBlockMatrix U a).lowerRight⁻¹ (pairedPotentialMean U W)) +
      vecDot (pairedFluxImageMean U a W)
        (matVecMul (coarseBlockMatrix U a).lowerRight⁻¹ (pairedFluxImageMean U a W)) ≤
      blockPairingAverage U a W W := by
  let D : Mat d := (coarseBlockMatrix U a).lowerRight
  let p := pairedPotentialMean U W
  let g := pairedFluxImageMean U a W
  let e := matVecMul D⁻¹ g
  let f := matVecMul D⁻¹ p
  let S : BlockState d := F.field (0, e)
  let R : BlockState d := pairedReflectState a (F.field (0, f))
  let T : BlockState d := S + R
  let q := vecDot p (matVecMul D⁻¹ p) + vecDot g (matVecMul D⁻¹ g)
  have hdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hDe : matVecMul D e = g := by
    dsimp [e]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hDf : matVecMul D f = p := by
    dsimp [f]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hSmem : MemBlockL2 U S.eval := (F.admissible (0, e)).memBlockL2_eval
  have hSresp : BlockResponseSpace a U S := hFresp (0, e)
  have hSflux : MemVectorL2 U S.flux := by
    simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hSmem
  have hRresp : BlockResponseSpace a U R := by
    exact pairedReflectState_mem_responseSpace hConv hEll
      (hFresp (0, f)) (by
        simpa [BlockState.eval] using
          memVectorL2_snd_of_memBlockL2 (F.admissible (0, f)).memBlockL2_eval)
  have hRpot : MemVectorL2 U R.potential :=
    blockResponse_potential_memL2_of_mem_responseSpace hRresp
  have hRflux : MemVectorL2 U R.flux :=
    memVectorL2_upperImage hEll (hFresp (0, f)) (by
      simpa [BlockState.eval] using
        memVectorL2_snd_of_memBlockL2 (F.admissible (0, f)).memBlockL2_eval)
  have hRmem : MemBlockL2 U R.eval := by
    change MemBlockL2 U (fun x => (R.potential x, R.flux x))
    exact memBlockL2_blockField hRpot hRflux
  have hSpot : MemVectorL2 U S.potential := by
    simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 hSmem
  have hTmem : MemBlockL2 U T.eval := by
    change MemBlockL2 U (fun x => (S.potential x + R.potential x,
      S.flux x + R.flux x))
    exact memBlockL2_blockField (hSpot.add hRpot) (hSflux.add hRflux)
  have hWW : MeasureTheory.IntegrableOn (blockPairingIntegrand a W W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hWmem hEll
  have hWS : MeasureTheory.IntegrableOn (blockPairingIntegrand a W S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hSmem hEll
  have hWR : MeasureTheory.IntegrableOn (blockPairingIntegrand a W R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hRmem hEll
  have hSS : MeasureTheory.IntegrableOn (blockPairingIntegrand a S S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hSmem hEll
  have hSR : MeasureTheory.IntegrableOn (blockPairingIntegrand a S R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hRmem hEll
  have hRS : MeasureTheory.IntegrableOn (blockPairingIntegrand a R S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hSmem hEll
  have hRR : MeasureTheory.IntegrableOn (blockPairingIntegrand a R R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hRmem hEll
  have hST : MeasureTheory.IntegrableOn (blockPairingIntegrand a S T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hTmem hEll
  have hRT : MeasureTheory.IntegrableOn (blockPairingIntegrand a R T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hTmem hEll
  have hWT : MeasureTheory.IntegrableOn (blockPairingIntegrand a W T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hTmem hEll
  have hTT : MeasureTheory.IntegrableOn (blockPairingIntegrand a T T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hTmem hTmem hEll
  have hmeanS : pairedPotentialMean U S = 0 := by
    exact pureBottom_potentialMean_eq_zero hvol F e
  have hcross : blockPairingAverage U a S R = 0 := by
    calc
      blockPairingAverage U a S R = vecDot f (pairedPotentialMean U S) :=
        reflectedBottom_represents_potentialMean hEll hConv F hFresp
          S hSresp.1 hSresp.2.1 hSmem f
      _ = 0 := by rw [hmeanS]; exact vecDot_zero_right _
  have hSgram : blockPairingAverage U a S S = vecDot e (matVecMul D e) := by
    have hbase := linearMuMinimizerFamily_pairing_eq_coarse F (0, e) (0, e)
    have hblock : blockVecDot (0, e)
        (blockMatVecMul (coarseBlockMatrix U a) (0, e)) =
          vecDot e (matVecMul D e) := by
      simp [blockVecDot, blockMatVecMul, D, matVecMul_zero, vecDot_zero_left]
    exact hbase.trans hblock
  have hRgram : blockPairingAverage U a R R = vecDot f (matVecMul D f) := by
    calc
      blockPairingAverage U a R R =
          blockPairingAverage U a (pairedReflectState a (F.field (0, f)))
            (pairedReflectState a (F.field (0, f))) := rfl
      _ = blockPairingAverage U a (F.field (0, f)) (F.field (0, f)) :=
        pairedReflect_pairingAverage_isometry hEll _ _
      _ = vecDot f (matVecMul D f) := by
        have hbase := linearMuMinimizerFamily_pairing_eq_coarse F (0, f) (0, f)
        have hblock : blockVecDot (0, f)
            (blockMatVecMul (coarseBlockMatrix U a) (0, f)) =
              vecDot f (matVecMul D f) := by
          simp [blockVecDot, blockMatVecMul, D, matVecMul_zero, vecDot_zero_left]
        exact hbase.trans hblock
  have hTgram : blockPairingAverage U a T T = q := by
    dsimp [T]
    rw [blockPairingAverage_add_left U a S R (S + R) hST hRT,
      blockPairingAverage_add_right U a S S R hSS hSR,
      blockPairingAverage_add_right U a R S R hRS hRR,
      hSgram, hRgram, hcross]
    rw [blockCoeff_pairingAverage_symmetric U a R S, hcross]
    simp only [zero_add, add_zero]
    calc
      vecDot e (matVecMul D e) + vecDot f (matVecMul D f) =
          vecDot e g + vecDot f p := by rw [hDe, hDf]
      _ = vecDot g (matVecMul D⁻¹ g) + vecDot p (matVecMul D⁻¹ p) := by
        change vecDot (matVecMul D⁻¹ g) g + vecDot (matVecMul D⁻¹ p) p = _
        rw [vecDot_comm (matVecMul D⁻¹ g) g,
          vecDot_comm (matVecMul D⁻¹ p) p]
      _ = q := by dsimp [q]; ring
  have hWpair : blockPairingAverage U a W T = q := by
    dsimp [T]
    rw [blockPairingAverage_add_right U a W S R hWS hWR,
      pureBottom_represents_fluxImageMean hEll F W hWresp hWmem e,
      reflectedBottom_represents_potentialMean hEll hConv F hFresp W
        hWresp.1 hWresp.2.1 hWmem f]
    dsimp [q, e, f]
    rw [vecDot_comm (matVecMul D⁻¹ g) g,
      vecDot_comm (matVecMul D⁻¹ p) p]
    ring
  have hCS := blockPairingAverage_sq_le_product hEll
    (measurableSet_of_isEllipticFieldOn hEll) W T hWW hWT hTT
  rw [hWpair, hTgram] at hCS
  have hDinv : D⁻¹.PosDef := hD.inv
  have hqnonneg : 0 ≤ q := by
    have hp : 0 ≤ vecDot p (matVecMul D⁻¹ p) := by
      by_cases hp0 : p = 0
      · simp [hp0, matVecMul_zero, vecDot_zero_left]
      · have hstrict := hDinv.dotProduct_mulVec_pos hp0
        exact le_of_lt (by
          simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hstrict)
    have hg : 0 ≤ vecDot g (matVecMul D⁻¹ g) := by
      by_cases hg0 : g = 0
      · simp [hg0, matVecMul_zero, vecDot_zero_left]
      · have hstrict := hDinv.dotProduct_mulVec_pos hg0
        exact le_of_lt (by
          simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hstrict)
    dsimp [q]
    exact add_nonneg hp hg
  have hEnergy : 0 ≤ blockEnergyAverage U a W := by
    unfold blockEnergyAverage
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    unfold blockEnergyDensity
    have hp : 0 ≤ blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField a x) (W.eval x)) := by
      simpa [blockCoeffField] using
        blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (W.eval x)
    exact mul_nonneg (by norm_num) hp
  have hWWnonneg : 0 ≤ blockPairingAverage U a W W := by
    have hhalf := blockEnergyAverage_eq_half_blockPairingAverage_self U a W
    have hdouble : blockPairingAverage U a W W =
        2 * blockEnergyAverage U a W := by rw [hhalf]; ring
    rw [hdouble]
    positivity
  change q ≤ blockPairingAverage U a W W
  by_cases hq : q = 0
  · rw [hq]
    exact hWWnonneg
  · have hqpos : 0 < q := lt_of_le_of_ne hqnonneg (Ne.symm hq)
    by_contra hnot
    have hlt : blockPairingAverage U a W W < q := lt_of_not_ge hnot
    have hprod : 0 < q * (q - blockPairingAverage U a W W) :=
      mul_pos hqpos (sub_pos.mpr hlt)
    nlinarith [hCS]

theorem pairedBessel_isElliptic_translateCoeffField
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {lam Lam : ℝ}
    (z : Vec d) (hEll : IsEllipticFieldOn lam Lam (translateSet z U) a) :
    IsEllipticFieldOn lam Lam U (translateCoeffField z a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec d => x + z) :=
      (continuous_id.add continuous_const).measurable
    have hcomp : Measurable (fun x i j =>
        if x + z ∈ translateSet z U then a (x + z) i j else 0) :=
      hEll.1.comp hshift
    have hEq : (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) =
        (fun x i j => if x ∈ U then translateCoeffField z a x i j else 0) := by
      funext x i j
      have hcancel : x + z - z = x := by ext k; simp [sub_eq_add_neg, add_assoc]
      by_cases hx : x ∈ U
      · have hxt : x + z ∈ translateSet z U := by
          rw [mem_translateSet_iff_sub_mem, hcancel]
          exact hx
        simp [hx, hxt]
        rfl
      · have hxt : x + z ∉ translateSet z U := by
          intro hmem
          rw [mem_translateSet_iff_sub_mem, hcancel] at hmem
          exact hx hmem
        simp [hx, hxt]
    simpa [hEq] using hcomp
  · intro x hx
    have hxt : x + z ∈ translateSet z U := by
      have hcancel : x + z - z = x := by ext k; simp [sub_eq_add_neg, add_assoc]
      rw [mem_translateSet_iff_sub_mem, hcancel]
      exact hx
    have hxz : (fun i => x i + z i) = x + z := rfl
    simpa only [translateCoeffField, hxz] using hEll.2 (x + z) hxt

/-- The actual local linear family of coarse minimizers on any triadic cell,
constructed by translating origin-cell Hodge recovery. -/
structure PairedBesselOpenCubeFamilyData {Q : TriadicCube 2} {a : CoeffField 2}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) where
  family : LinearMuMinimizerFamily (openCubeSet Q) a
  response : ∀ P : BlockVec 2,
    BlockResponseSpace a (openCubeSet Q) (family.field P)

/-- Every triadic open cell has the canonical actual linear Mu-minimizer
family and its homogeneous response property. -/
noncomputable def pairedBesselOpenCubeFamilyData
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    PairedBesselOpenCubeFamilyData hEll := by
  classical
  let U : Set (Vec 2) := openCubeSet Q
  let z : Vec 2 := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  let U0 : Set (Vec 2) := openCubeSet (originCube 2 Q.scale)
  let a0 : CoeffField 2 := translateCoeffField z a
  have hTranslate : U = translateSet z U0 :=
    openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEll0 : IsEllipticFieldOn lam Lam U0 a0 := by
    have hEllTarget : IsEllipticFieldOn lam Lam (translateSet z U0) a := by
      simpa [U, hTranslate] using hEll
    exact pairedBessel_isElliptic_translateCoeffField z hEllTarget
  let pairedBesselFamilyVolumeFact : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨volume_openCubeSet_lt_top Q⟩
  let pairedBesselFamilyFiniteMeasure : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    infer_instance
  let pairedBesselFamilyOriginVolumeFact : Fact (MeasureTheory.volume U0 < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := 2) Q.scale⟩
  let pairedBesselFamilyOriginFiniteMeasure :
      MeasureTheory.IsFiniteMeasure (volumeMeasureOn U0) := by infer_instance
  have hvol0 : 0 < (MeasureTheory.volume U0).toReal :=
    volume_openCubeSet_originCube_toReal_pos (d := 2) Q.scale
  let recoveryExists := openCubeOriginEllipticRecoveryExistence (d := 2)
    (lam := lam) (Lam := Lam) Q.scale a0 hEll0
  let R0 := Classical.choose recoveryExists
  have hData := Classical.choose_spec recoveryExists
  let hEllR := hData.1
  let hCompat := hData.2
  let system : MuOperatorSystemData U0 a0 :=
    R0.toMuOperatorSystemDataOfIsEllipticFieldOn hEllR hvol0
  let F0 : LinearMuMinimizerFamily U0 a0 :=
    R0.toLinearMuMinimizerFamily system hCompat
  let F : LinearMuMinimizerFamily U a := by
    refine ⟨fun P => (F0.field P).translate z, ?_, ?_, ?_, ?_, ?_⟩
    · intro P P'
      apply BlockState.ext
      · funext x
        rw [F0.map_add]
        rfl
      · funext x
        rw [F0.map_add]
        rfl
    · intro c P
      apply BlockState.ext
      · funext x
        rw [F0.map_smul]
        rfl
      · funext x
        rw [F0.map_smul]
        rfl
    · intro P
      have hAdmissible : IsBlockMuAdmissible (translateSet z U0) P
          ((F0.field P).translate z) := isBlockMuAdmissible_translateSet (F0.admissible P) z
      simpa [U, hTranslate] using hAdmissible
    · intro P P'
      have hP : IsBlockMuAdmissible U P ((F0.field P).translate z) := by
        have hAdmissible := isBlockMuAdmissible_translateSet (F0.admissible P) z
        simpa [U, hTranslate] using hAdmissible
      have hP' : IsBlockMuAdmissible U P' ((F0.field P').translate z) := by
        have hAdmissible := isBlockMuAdmissible_translateSet (F0.admissible P') z
        simpa [U, hTranslate] using hAdmissible
      exact blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        hP.memBlockL2_eval hP'.memBlockL2_eval hEll
    · intro P
      rw [hTranslate, Mu_translateSet_eq_translateCoeffField]
      rw [blockEnergyAverage, volumeAverage_blockEnergyDensity_translate_forward]
      exact F0.realizes P
  have hFresp : ∀ P : BlockVec 2, BlockResponseSpace a U (F.field P) := by
    intro P
    have hBase : BlockResponseSpace a0 U0 (F0.field P) :=
      R0.toMuCorrectionSpaceRecoveryData.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        system (isOpenBoundedConvexDomain_openCubeSet (originCube 2 Q.scale))
        hEllR hvol0.ne' P
    have hShifted := blockResponseSpace_translateSet z hBase
    simpa [F, U, hTranslate] using hShifted
  exact ⟨F, hFresp⟩

/-- The source shift in the forced paired Bessel estimate. Its coordinates
pair the load with the actual zero-trace potential modes of the local
minimizer family. -/
noncomputable def pairedBesselSourceCorrectionVector {Q : TriadicCube 2}
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (G : Vec 2 → Vec 2) : Vec 2 :=
  let F := (pairedBesselOpenCubeFamilyData hEll).family
  fun i => volumeAverage (openCubeSet Q) (fun x =>
    vecDot (G x) ((F.field (0, Pi.single i 1)).potential x))

/-- The local source pairing is the Euclidean pairing with the correction
vector. -/
theorem pairedBessel_sourcePairing_eq_dot {Q : TriadicCube 2}
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {G : Vec 2 → Vec 2} (hG : MemVectorL2 (openCubeSet Q) G) (e : Vec 2) :
    volumeAverage (openCubeSet Q) (fun x => vecDot (G x)
        (((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x)) =
      vecDot e (pairedBesselSourceCorrectionVector hEll G) := by
  let pairedBesselSourceFiniteMeasure : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let U := openCubeSet Q
  let F := (pairedBesselOpenCubeFamilyData hEll).family
  let b₀ : Vec 2 := Pi.single 0 1
  let b₁ : Vec 2 := Pi.single 1 1
  have he : e = e 0 • b₀ + e 1 • b₁ := by
    ext i
    fin_cases i <;> simp [b₀, b₁]
  have hinput : ((0 : Vec 2), e) = ((0, e 0 • b₀) + (0, e 1 • b₁)) := by
    apply Prod.ext
    · simp
    · exact he
  have hinput0 : ((0 : Vec 2), e 0 • b₀) = e 0 • (0, b₀) := by
    ext i <;> simp
  have hinput1 : ((0 : Vec 2), e 1 • b₁) = e 1 • (0, b₁) := by
    ext i <;> simp
  have hfamily : F.field (0, e) =
      e 0 • F.field (0, b₀) + e 1 • F.field (0, b₁) := by
    calc
      F.field (0, e) = F.field ((0, e 0 • b₀) + (0, e 1 • b₁)) :=
        congrArg F.field hinput
      _ = F.field (e 0 • (0, b₀) + e 1 • (0, b₁)) := by rw [← hinput0, ← hinput1]
      _ = F.field (e 0 • (0, b₀)) + F.field (e 1 • (0, b₁)) := F.map_add _ _
      _ = e 0 • F.field (0, b₀) + e 1 • F.field (0, b₁) := by
        rw [F.map_smul, F.map_smul]
  have hG0 : IntegrableOn
      (fun x => vecDot (G x) ((F.field (0, b₀)).potential x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG
      (memVectorL2_fst_of_memBlockL2 (F.admissible (0, b₀)).memBlockL2_eval)
  have hG1 : IntegrableOn
      (fun x => vecDot (G x) ((F.field (0, b₁)).potential x)) U :=
    integrableOn_vecDot_of_memVectorL2 hG
      (memVectorL2_fst_of_memBlockL2 (F.admissible (0, b₁)).memBlockL2_eval)
  have hpot : (F.field (0, e)).potential =
      fun x => e 0 • (F.field (0, b₀)).potential x + e 1 • (F.field (0, b₁)).potential x :=
    congrArg BlockState.potential hfamily
  have hsumPoint (x : Vec 2) :
      vecDot (G x) (e 0 • (F.field (0, b₀)).potential x +
        e 1 • (F.field (0, b₁)).potential x) =
      e 0 * vecDot (G x) ((F.field (0, b₀)).potential x) +
        e 1 * vecDot (G x) ((F.field (0, b₁)).potential x) := by
    rw [vecDot_add_right, vecDot_smul_right, vecDot_smul_right]
  calc
    volumeAverage U (fun x => vecDot (G x) ((F.field (0, e)).potential x))
        = volumeAverage U (fun x =>
            e 0 * vecDot (G x) ((F.field (0, b₀)).potential x) +
              e 1 * vecDot (G x) ((F.field (0, b₁)).potential x)) := by
          congr 1
          funext x
          rw [hpot]
          exact hsumPoint x
    _ = volumeAverage U
          ((e 0 • fun x => vecDot (G x) ((F.field (0, b₀)).potential x)) +
            (e 1 • fun x => vecDot (G x) ((F.field (0, b₁)).potential x))) := by
          congr 1
    _ = e 0 * volumeAverage U
          (fun x => vecDot (G x) ((F.field (0, b₀)).potential x)) +
        e 1 * volumeAverage U
          (fun x => vecDot (G x) ((F.field (0, b₁)).potential x)) := by
          rw [volumeAverage_add (hG0.smul (e 0)) (hG1.smul (e 1)),
            volumeAverage_smul, volumeAverage_smul]
    _ = vecDot e (pairedBesselSourceCorrectionVector hEll G) := by
          simp [pairedBesselSourceCorrectionVector, F, U, b₀, b₁, vecDot]

/-- Paired Bessel bound on every triadic open cell for an actual compatible
finite-energy response. The local linear minimizers are produced from the
origin-cube recovery theorem and translated to the requested cell. -/
theorem pairedBessel_openCubeSet {Q : TriadicCube 2} {a : CoeffField 2}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hWresp : BlockResponseSpace a (openCubeSet Q) W)
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval) :
    vecDot (pairedPotentialMean (openCubeSet Q) W)
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight⁻¹
          (pairedPotentialMean (openCubeSet Q) W)) +
      vecDot (pairedFluxImageMean (openCubeSet Q) a W)
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight⁻¹
          (pairedFluxImageMean (openCubeSet Q) a W)) ≤
      blockPairingAverage (openCubeSet Q) a W W := by
  let U : Set (Vec 2) := openCubeSet Q
  let z : Vec 2 := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  let U0 : Set (Vec 2) := openCubeSet (originCube 2 Q.scale)
  let a0 : CoeffField 2 := translateCoeffField z a
  have hTranslate : U = translateSet z U0 := by
    exact openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEll0 : IsEllipticFieldOn lam Lam U0 a0 := by
    have hEllTarget : IsEllipticFieldOn lam Lam (translateSet z U0) a := by
      simpa [U, hTranslate] using hEll
    exact pairedBessel_isElliptic_translateCoeffField z hEllTarget
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_openCubeSet_lt_top Q⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by infer_instance
  let : Fact (MeasureTheory.volume U0 < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := 2) Q.scale⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U0) := by infer_instance
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hvol0 : 0 < (MeasureTheory.volume U0).toReal :=
    volume_openCubeSet_originCube_toReal_pos (d := 2) Q.scale
  obtain ⟨R0, hData⟩ :=
    openCubeOriginEllipticRecoveryExistence (d := 2) (lam := lam) (Lam := Lam)
      Q.scale a0 hEll0
  obtain ⟨hEllR, hCompat⟩ := hData
  let system : MuOperatorSystemData U0 a0 :=
    R0.toMuOperatorSystemDataOfIsEllipticFieldOn hEllR hvol0
  let F0 : LinearMuMinimizerFamily U0 a0 :=
    R0.toLinearMuMinimizerFamily system hCompat
  let F : LinearMuMinimizerFamily U a := by
    refine ⟨fun P => (F0.field P).translate z, ?_, ?_, ?_, ?_, ?_⟩
    · intro P P'
      apply BlockState.ext
      · funext x
        rw [F0.map_add]
        rfl
      · funext x
        rw [F0.map_add]
        rfl
    · intro c P
      apply BlockState.ext
      · funext x
        rw [F0.map_smul]
        rfl
      · funext x
        rw [F0.map_smul]
        rfl
    · intro P
      have hAdmissible : IsBlockMuAdmissible (translateSet z U0) P
          ((F0.field P).translate z) := isBlockMuAdmissible_translateSet (F0.admissible P) z
      simpa [U, hTranslate] using hAdmissible
    · intro P P'
      have hP : IsBlockMuAdmissible U P ((F0.field P).translate z) := by
        have hAdmissible := isBlockMuAdmissible_translateSet (F0.admissible P) z
        simpa [U, hTranslate] using hAdmissible
      have hP' : IsBlockMuAdmissible U P' ((F0.field P').translate z) := by
        have hAdmissible := isBlockMuAdmissible_translateSet (F0.admissible P') z
        simpa [U, hTranslate] using hAdmissible
      exact blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        hP.memBlockL2_eval hP'.memBlockL2_eval hEll
    · intro P
      rw [hTranslate, Mu_translateSet_eq_translateCoeffField]
      rw [blockEnergyAverage, volumeAverage_blockEnergyDensity_translate_forward]
      exact F0.realizes P
  have hFresp : ∀ P : BlockVec 2, BlockResponseSpace a U (F.field P) := by
    intro P
    have hBase : BlockResponseSpace a0 U0 (F0.field P) :=
      R0.toMuCorrectionSpaceRecoveryData.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        system (isOpenBoundedConvexDomain_openCubeSet (originCube 2 Q.scale))
        hEllR hvol0.ne' P
    have hShifted := blockResponseSpace_translateSet z hBase
    simpa [F, U, hTranslate] using hShifted
  have hConv : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_openCubeSet Q
  obtain ⟨sigma, hCoarse, _, _, _, _, hDpos, _⟩ :=
    exists_energyMap_coarseData hConv hEll hvol
  have hD : (coarseBlockMatrix U a).lowerRight.PosDef := by
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hWresp' : BlockResponseSpace a U W := by simpa [U] using hWresp
  have hWmem' : MemBlockL2 U W.eval := by simpa [U] using hWmem
  simpa [U] using pairedBessel_of_linearMuMinimizerFamily hConv hvol.ne' hEll F
    hFresp W hWresp' hWmem' hD

/-- A forced compatible field has the same potential-mean Riesz identity as a
homogeneous field; the flux-image identity carries the exact load pairing
against the zero-trace minimizer potential. -/
private theorem pairedBessel_forcedBottom_represents_fluxImageMean
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField 2} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (F : LinearMuMinimizerFamily U a)
    (W : BlockState 2)
    (hWmem : MemBlockL2 U W.eval)
    (hWlower : MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2))
    {G : Vec 2 → Vec 2}
    (hforced : ∀ T : BlockState 2, ScalarVariation U T.eval →
      volumeAverage U (blockPairingIntegrand a T W) =
        volumeAverage U (fun x => vecDot (T.potential x) (G x)))
    (e : Vec 2) :
    blockPairingAverage U a W (F.field (0, e)) =
      vecDot e (pairedFluxImageMean U a W) +
        volumeAverage U (fun x => vecDot (G x) ((F.field (0, e)).potential x)) := by
  let S := F.field (0, e)
  let C : BlockState 2 := { potential := fun _ => 0, flux := fun _ => e }
  let Adm := F.admissible (0, e)
  let Corr := Adm.toCorrectionFieldDataOfAdmissible
  let Y : BlockState 2 := { potential := Corr.potential, flux := Corr.flux }
  have hYmem : MemBlockL2 U Y.eval := by
    change MemBlockL2 U (fun x => (Y.potential x, Y.flux x))
    simpa [Y] using admissibleCorrection_memBlockL2 Adm
  have hYvar : ScalarVariation U Y.eval := by
    refine ⟨hYmem, ?_, ?_⟩
    · change IsPotentialZeroTraceOn U Corr.potential
      exact Adm.isPotentialZeroTrace
    · change IsSolenoidalZeroNormalTraceOn U Corr.flux
      exact Adm.isSolenoidalZeroNormalTrace
  have hCmem : MemBlockL2 U C.eval := by
    change MemBlockL2 U (blockField C.potential C.flux)
    exact memBlockL2_blockField
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := (0 : Vec 2)))
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := e))
  have hsplit : S = Y + C := by
    apply BlockState.ext
    · funext x
      change S.potential x = Y.potential x + C.potential x
      simp [S, Y, C, Corr, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible]
    · funext x
      change S.flux x = S.flux x - e + e
      exact (sub_add_cancel _ _).symm
  have hYW : IntegrableOn (blockPairingIntegrand a Y W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hYmem hWmem hEll
  have hCW : IntegrableOn (blockPairingIntegrand a C W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hCmem hWmem hEll
  have hGsource := hforced Y hYvar
  have hsource : blockPairingAverage U a Y W =
      volumeAverage U (fun x => vecDot (G x) (S.potential x)) := by
    change volumeAverage U (blockPairingIntegrand a Y W) = _
    calc
      _ = volumeAverage U (fun x => vecDot (Y.potential x) (G x)) := hGsource
      _ = volumeAverage U (fun x => vecDot (G x) (S.potential x)) := by
        congr 1
        funext x
        rw [vecDot_comm]
        simp [S, Y, Corr, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible]
  have hcoord : ∀ i, IntegrableOn
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2 i) U := by
    intro i
    exact CorrectionFieldData.integrableOn_coord_of_memVectorL2 hWlower i
  have hconst : blockPairingAverage U a C W =
      vecDot e (pairedFluxImageMean U a W) := by
    calc
      blockPairingAverage U a C W = volumeAverage U
          (fun x => vecDot e ((blockMatVecMul (blockCoeffField a x) (W.eval x)).2)) := by
        unfold blockPairingAverage
        congr 1
        funext x
        simp [C, blockPairingIntegrand, BlockState.eval, blockVecDot, blockCoeffField, vecDot]
      _ = vecDot e (pairedFluxImageMean U a W) :=
        volumeAverage_vecDot_left e
          (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) hcoord
  calc
    blockPairingAverage U a W S = blockPairingAverage U a S W :=
      blockCoeff_pairingAverage_symmetric U a W S
    _ = blockPairingAverage U a (Y + C) W := by rw [← hsplit]
    _ = blockPairingAverage U a Y W + blockPairingAverage U a C W :=
      blockPairingAverage_add_left U a Y C W hYW hCW
    _ = _ := by rw [hsource, hconst]; ring

/-- Paired Bessel estimate for a compatible field satisfying a forced weak
response equation. The source shift is determined by the actual local
minimizer family. -/
theorem pairedBessel_forced_openCubeSet {Q : TriadicCube 2} {a : CoeffField 2}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    (hWsol : IsBlockSolenoidalOn (openCubeSet Q) W)
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval)
    (hWlower : MemVectorL2 (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2))
    {G : Vec 2 → Vec 2} (hG : MemVectorL2 (openCubeSet Q) G)
    (hforced : ∀ T : BlockState 2, ScalarVariation (openCubeSet Q) T.eval →
      volumeAverage (openCubeSet Q) (blockPairingIntegrand a T W) =
        volumeAverage (openCubeSet Q) (fun x => vecDot (T.potential x) (G x))) :
    vecDot (pairedPotentialMean (openCubeSet Q) W)
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight⁻¹
          (pairedPotentialMean (openCubeSet Q) W)) +
      vecDot (pairedFluxImageMean (openCubeSet Q) a W +
          pairedBesselSourceCorrectionVector hEll G)
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight⁻¹
          (pairedFluxImageMean (openCubeSet Q) a W +
            pairedBesselSourceCorrectionVector hEll G)) ≤
      blockPairingAverage (openCubeSet Q) a W W := by
  let U : Set (Vec 2) := openCubeSet Q
  let data := pairedBesselOpenCubeFamilyData hEll
  let F := data.family
  letI pairedBesselForcedFinite : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let D : Mat 2 := (coarseBlockMatrix U a).lowerRight
  let p := pairedPotentialMean U W
  let g := pairedFluxImageMean U a W
  let t := pairedBesselSourceCorrectionVector hEll G
  let g' := g + t
  let e := matVecMul D⁻¹ g'
  let f := matVecMul D⁻¹ p
  let S : BlockState 2 := F.field (0, e)
  let R : BlockState 2 := pairedReflectState a (F.field (0, f))
  let T : BlockState 2 := S + R
  let q := vecDot p (matVecMul D⁻¹ p) + vecDot g' (matVecMul D⁻¹ g')
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hConv : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  obtain ⟨_, hCoarse, _, _, _, _, hDpos, _⟩ := exists_energyMap_coarseData hConv hEll hvol
  have hD : D.PosDef := by
    change (coarseBlockMatrix U a).lowerRight.PosDef
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hDe : matVecMul D e = g' := by
    dsimp [e]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hDf : matVecMul D f = p := by
    dsimp [f]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hFresp : ∀ P : BlockVec 2, BlockResponseSpace a U (F.field P) := data.response
  have hSmem : MemBlockL2 U S.eval := (F.admissible (0, e)).memBlockL2_eval
  have hSresp : BlockResponseSpace a U S := hFresp (0, e)
  have hSflux : MemVectorL2 U S.flux := by
    simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hSmem
  have hRresp : BlockResponseSpace a U R := by
    exact pairedReflectState_mem_responseSpace hConv hEll
      (hFresp (0, f)) (by
        simpa [BlockState.eval] using
          memVectorL2_snd_of_memBlockL2 (F.admissible (0, f)).memBlockL2_eval)
  have hRpot : MemVectorL2 U R.potential :=
    blockResponse_potential_memL2_of_mem_responseSpace hRresp
  have hRflux : MemVectorL2 U R.flux :=
    memVectorL2_upperImage hEll (hFresp (0, f)) (by
      simpa [BlockState.eval] using
        memVectorL2_snd_of_memBlockL2 (F.admissible (0, f)).memBlockL2_eval)
  have hRmem : MemBlockL2 U R.eval := by
    change MemBlockL2 U (fun x => (R.potential x, R.flux x))
    exact memBlockL2_blockField hRpot hRflux
  have hSpot : MemVectorL2 U S.potential := by
    simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 hSmem
  have hTmem : MemBlockL2 U T.eval := by
    change MemBlockL2 U (fun x => (S.potential x + R.potential x,
      S.flux x + R.flux x))
    exact memBlockL2_blockField (hSpot.add hRpot) (hSflux.add hRflux)
  have hWW : IntegrableOn (blockPairingIntegrand a W W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hWmem hEll
  have hWS : IntegrableOn (blockPairingIntegrand a W S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hSmem hEll
  have hWR : IntegrableOn (blockPairingIntegrand a W R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hRmem hEll
  have hSS : IntegrableOn (blockPairingIntegrand a S S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hSmem hEll
  have hSR : IntegrableOn (blockPairingIntegrand a S R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hRmem hEll
  have hRS : IntegrableOn (blockPairingIntegrand a R S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hSmem hEll
  have hRR : IntegrableOn (blockPairingIntegrand a R R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hRmem hEll
  have hST : IntegrableOn (blockPairingIntegrand a S T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hTmem hEll
  have hRT : IntegrableOn (blockPairingIntegrand a R T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hTmem hEll
  have hWT : IntegrableOn (blockPairingIntegrand a W T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hTmem hEll
  have hTT : IntegrableOn (blockPairingIntegrand a T T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hTmem hTmem hEll
  have hmeanS : pairedPotentialMean U S = 0 :=
    pureBottom_potentialMean_eq_zero hvol.ne' F e
  have hcross : blockPairingAverage U a S R = 0 := by
    calc
      blockPairingAverage U a S R = vecDot f (pairedPotentialMean U S) :=
        reflectedBottom_represents_potentialMean hEll hConv F hFresp
          S hSresp.1 hSresp.2.1 hSmem f
      _ = 0 := by rw [hmeanS]; exact vecDot_zero_right _
  have hSgram : blockPairingAverage U a S S = vecDot e (matVecMul D e) := by
    have hbase := linearMuMinimizerFamily_pairing_eq_coarse F (0, e) (0, e)
    have hblock : blockVecDot (0, e) (blockMatVecMul (coarseBlockMatrix U a) (0, e)) =
        vecDot e (matVecMul D e) := by
      simp [blockVecDot, blockMatVecMul, D, matVecMul_zero, vecDot_zero_left]
    exact hbase.trans hblock
  have hRgram : blockPairingAverage U a R R = vecDot f (matVecMul D f) := by
    calc
      blockPairingAverage U a R R =
          blockPairingAverage U a (pairedReflectState a (F.field (0, f)))
            (pairedReflectState a (F.field (0, f))) := rfl
      _ = blockPairingAverage U a (F.field (0, f)) (F.field (0, f)) :=
        pairedReflect_pairingAverage_isometry hEll _ _
      _ = vecDot f (matVecMul D f) := by
        have hbase := linearMuMinimizerFamily_pairing_eq_coarse F (0, f) (0, f)
        have hblock : blockVecDot (0, f)
            (blockMatVecMul (coarseBlockMatrix U a) (0, f)) =
              vecDot f (matVecMul D f) := by
          simp [blockVecDot, blockMatVecMul, D, matVecMul_zero, vecDot_zero_left]
        exact hbase.trans hblock
  have hTgram : blockPairingAverage U a T T = q := by
    dsimp [T]
    rw [blockPairingAverage_add_left U a S R (S + R) hST hRT,
      blockPairingAverage_add_right U a S S R hSS hSR,
      blockPairingAverage_add_right U a R S R hRS hRR,
      hSgram, hRgram, hcross]
    rw [blockCoeff_pairingAverage_symmetric U a R S, hcross]
    simp only [zero_add, add_zero]
    calc
      vecDot e (matVecMul D e) + vecDot f (matVecMul D f) =
          vecDot e g' + vecDot f p := by rw [hDe, hDf]
      _ = vecDot g' (matVecMul D⁻¹ g') + vecDot p (matVecMul D⁻¹ p) := by
        change vecDot (matVecMul D⁻¹ g') g' + vecDot (matVecMul D⁻¹ p) p = _
        rw [vecDot_comm (matVecMul D⁻¹ g') g', vecDot_comm (matVecMul D⁻¹ p) p]
      _ = q := by dsimp [q]; ring
  have hWpair : blockPairingAverage U a W T = q := by
    dsimp [T]
    rw [blockPairingAverage_add_right U a W S R hWS hWR,
      pairedBessel_forcedBottom_represents_fluxImageMean hEll F W hWmem hWlower
        hforced e,
      pairedBessel_sourcePairing_eq_dot hEll hG e,
      reflectedBottom_represents_potentialMean hEll hConv F hFresp W
        hWpot hWsol hWmem f]
    dsimp [q, e, f, g', g, p, t]
    calc
      _ = vecDot (matVecMul D⁻¹ (pairedFluxImageMean U a W +
            pairedBesselSourceCorrectionVector hEll G))
            (pairedFluxImageMean U a W + pairedBesselSourceCorrectionVector hEll G) +
          vecDot (matVecMul D⁻¹ (pairedPotentialMean U W)) (pairedPotentialMean U W) := by
        rw [← vecDot_add_right]
      _ = _ := by
        rw [vecDot_comm (matVecMul D⁻¹ (pairedFluxImageMean U a W +
              pairedBesselSourceCorrectionVector hEll G))
            (pairedFluxImageMean U a W + pairedBesselSourceCorrectionVector hEll G),
          vecDot_comm (matVecMul D⁻¹ (pairedPotentialMean U W)) (pairedPotentialMean U W)]
        ring
  have hCS := blockPairingAverage_sq_le_product hEll
    (measurableSet_of_isEllipticFieldOn hEll) W T hWW hWT hTT
  rw [hWpair, hTgram] at hCS
  have hDinv : D⁻¹.PosDef := hD.inv
  have hqnonneg : 0 ≤ q := by
    have hp : 0 ≤ vecDot p (matVecMul D⁻¹ p) := by
      by_cases hp0 : p = 0
      · simp [hp0, matVecMul_zero, vecDot_zero_left]
      · have hstrict := hDinv.dotProduct_mulVec_pos hp0
        exact le_of_lt (by simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hstrict)
    have hg : 0 ≤ vecDot g' (matVecMul D⁻¹ g') := by
      by_cases hg0 : g' = 0
      · simp [hg0, matVecMul_zero, vecDot_zero_left]
      · have hstrict := hDinv.dotProduct_mulVec_pos hg0
        exact le_of_lt (by simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hstrict)
    dsimp [q]
    exact add_nonneg hp hg
  have hEnergy : 0 ≤ blockEnergyAverage U a W := by
    unfold blockEnergyAverage
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    unfold blockEnergyDensity
    have hp : 0 ≤ blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField a x) (W.eval x)) := by
      simpa [blockCoeffField] using
        blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (W.eval x)
    exact mul_nonneg (by norm_num) hp
  have hWWnonneg : 0 ≤ blockPairingAverage U a W W := by
    have hhalf := blockEnergyAverage_eq_half_blockPairingAverage_self U a W
    have hdouble : blockPairingAverage U a W W = 2 * blockEnergyAverage U a W := by
      rw [hhalf]
      ring
    rw [hdouble]
    positivity
  change q ≤ blockPairingAverage U a W W
  by_cases hq : q = 0
  · rw [hq]
    exact hWWnonneg
  · have hqpos : 0 < q := lt_of_le_of_ne hqnonneg (Ne.symm hq)
    by_contra hnot
    have hlt : blockPairingAverage U a W W < q := lt_of_not_ge hnot
    have hprod : 0 < q * (q - blockPairingAverage U a W W) :=
      mul_pos hqpos (sub_pos.mpr hlt)
    nlinarith [hCS]

end

end ASDExplicitGamma.Variational
