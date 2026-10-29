module

public import ASDExplicitGamma.Variational.EnergyMap
public import ASDExplicitGamma.Model.StationaryPhysicalProjection
public import Algsuperdiff.Section3.Provider.Corrector.CubeComparison
public import Algsuperdiff.Section3.Provider.Corrector.RealizationTransfer
public import Homogenization.Internal.Ch02.SymmetricDirichletNeumann.Dirichlet
public import Homogenization.Book.Ch02.Theorems.DeterministicIdentities

@[expose] public section

open MeasureTheory Homogenization Homogenization.Book
open Algsuperdiff.Section3.Provider.Corrector

namespace ASDExplicitGamma.Scalar

/-- Constant vectors annihilate zero-trace potential gradients. -/
theorem integral_vecDot_const_potentialZeroTrace {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {r : Vec d → Vec d}
    (hr : MemVectorL2 U r) (hpot : IsPotentialZeroTraceOn U r) (e : Vec d) :
    (∫ x in U, vecDot e (r x)) = 0 := by
  have hi := hpot.integral_eq_zero
  simp only [vecDot]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i hi'
    rw [integral_const_mul]
    have hz := congrFun hi i
    simp only [Pi.zero_apply] at hz
    rw [hz, mul_zero]
  · intro i hi'
    exact ((memScalarL2_coord_of_memVectorL2 hr i).integrable (by norm_num)).const_mul _

/-- The molecular energy estimate for an actual affine Dirichlet solution,
using any square-integrable field with the same physical divergence as `k e`. -/
theorem affineDirichlet_corrector_energy_le
    {d : ℕ} [NeZero d] (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    {ν : ℝ}
    (hsymm : ∀ x, symmPart (a.toCoeffField x) = ν • (1 : Mat d))
    (e : Vec d) {u : H1Function (U : Set (Vec d))}
    (hu : IsAffineDirichletSolution a.toCoeffField (U : Set (Vec d)) e u)
    {H : Vec d → Vec d} (hH : MemVectorL2 (U : Set (Vec d)) H)
    (hres : IsSolenoidalOn (U : Set (Vec d)) (fun x =>
      matVecMul (a.toCoeffField x) e - ν • e - H x)) :
    ν ^ 2 * (∫ x in (U : Set (Vec d)), vecDot (u.grad x - e) (u.grad x - e)) ≤
      ∫ x in (U : Set (Vec d)), vecDot (H x) (H x) := by
  let r : Vec d → Vec d := fun x => u.grad x - e
  let F : Vec d → Vec d := fun x => matVecMul (a.toCoeffField x) e - ν • e
  have hr : MemVectorL2 (U : Set (Vec d)) r :=
    u.grad_memVectorL2.sub (Internal.Ch02.BookCh02.memVectorL2_const_vec e)
  have hF : MemVectorL2 (U : Set (Vec d)) F :=
    (memVectorL2_matVecMul_of_isEllipticFieldOn hEll (Internal.Ch02.BookCh02.memVectorL2_const_vec e)).sub (Internal.Ch02.BookCh02.memVectorL2_const_vec (ν • e))
  have hrr := integrableOn_vecDot_of_memVectorL2 hr hr
  have hFr := integrableOn_vecDot_of_memVectorL2 hF hr
  have hHr := integrableOn_vecDot_of_memVectorL2 hH hr
  have hHH := integrableOn_vecDot_of_memVectorL2 hH hH
  have her := integrableOn_vecDot_of_memVectorL2 (Internal.Ch02.BookCh02.memVectorL2_const_vec e) hr
  have hz := setIntegral_vecDot_eq_zero_of_isSolenoidalOn hu.1.2 hu.2
  have hzero := integral_vecDot_const_potentialZeroTrace hr hu.2 e
  have hpoint (x : Vec d) : vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (r x) =
      ν * vecDot (r x) (r x) + ν * vecDot e (r x) + vecDot (F x) (r x) := by
    have hug : u.grad x = r x + e := by dsimp [r]; abel
    have hfg : matVecMul (a.toCoeffField x) e = ν • e + F x := by dsimp [F]; abel
    rw [hug, matVecMul_add, vecDot_add_left, hfg, vecDot_add_left, vecDot_smul_left,
      vecDot_comm (matVecMul _ _) (r x), ← vecDot_matVecMul_symmPart, hsymm]
    rw [Internal.Ch02.BookCh02.matVecMul_smul_one, vecDot_smul_right]
    ring
  have hbal : ν * (∫ x in (U : Set (Vec d)), vecDot (r x) (r x)) +
      (∫ x in (U : Set (Vec d)), vecDot (H x) (r x)) = 0 := by
    have hcross := setIntegral_vecDot_eq_zero_of_isSolenoidalOn hres hu.2
    have heq : (∫ x in (U : Set (Vec d)), vecDot (F x) (r x)) =
        ∫ x in (U : Set (Vec d)), vecDot (H x) (r x) := by
      have heq' (x : Vec d) : vecDot (F x - H x) (r x) =
          vecDot (F x) (r x) - vecDot (H x) (r x) := by
        simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      change (∫ x in (U : Set (Vec d)), vecDot (F x - H x) (r x)) = 0 at hcross
      simp_rw [heq'] at hcross
      rw [integral_sub hFr hHr] at hcross
      linarith only [hcross]
    change (∫ x in (U : Set (Vec d)), vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (r x)) = 0 at hz
    simp_rw [hpoint] at hz
    have hs : IntegrableOn (fun x => ν * vecDot (r x) (r x) + ν * vecDot e (r x))
        (U : Set (Vec d)) := (hrr.const_mul ν).add (her.const_mul ν)
    rw [integral_add hs hFr, integral_add (hrr.const_mul ν) (her.const_mul ν),
      integral_const_mul, integral_const_mul, hzero, mul_zero, add_zero, heq] at hz
    exact hz
  have hnonneg : 0 ≤ ∫ x in (U : Set (Vec d)),
      vecDot (H x + ν • r x) (H x + ν • r x) :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have heq (x : Vec d) : vecDot (H x + ν • r x) (H x + ν • r x) =
      vecDot (H x) (H x) + 2 * ν * vecDot (H x) (r x) + ν ^ 2 * vecDot (r x) (r x) := by
    simp only [vecDot_add_left, vecDot_add_right, vecDot_smul_left, vecDot_smul_right]
    rw [vecDot_comm (r x) (H x)]
    ring
  simp_rw [heq] at hnonneg
  have hs : IntegrableOn (fun x => vecDot (H x) (H x) + 2 * ν * vecDot (H x) (r x))
      (U : Set (Vec d)) := hHH.add (hHr.const_mul (2 * ν))
  rw [integral_add hs (hrr.const_mul (ν ^ 2)), integral_add hHH (hHr.const_mul (2 * ν)),
    integral_const_mul, integral_const_mul] at hnonneg
  change ν ^ 2 * (∫ x in (U : Set (Vec d)), vecDot (r x) (r x)) ≤ _
  have hbalν := congrArg (fun z : ℝ => ν * z) hbal
  nlinarith only [hbalν, hnonneg]

/-- The averaged squared gradient of an affine Dirichlet solution splits
into its unit affine slope and its zero-trace correction. -/
theorem affineDirichlet_grad_energy
    {d : ℕ} [NeZero d] (U : Ch02.Domain d) {a : CoeffField d}
    {e : Vec d} (he : vecNormSq e = 1) {u : H1Function (U : Set (Vec d))}
    (hu : IsAffineDirichletSolution a (U : Set (Vec d)) e u) :
    volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (u.grad x)) =
      1 + volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (u.grad x - e)) := by
  let r := fun x => u.grad x - e
  have hr : MemVectorL2 (U : Set (Vec d)) r :=
    u.grad_memVectorL2.sub (Internal.Ch02.BookCh02.memVectorL2_const_vec e)
  have hi := integrableOn_vecDot_of_memVectorL2 hr hr
  have hie := integrableOn_vecDot_of_memVectorL2
    (Internal.Ch02.BookCh02.memVectorL2_const_vec e) hr
  have hz := integral_vecDot_const_potentialZeroTrace hr hu.2 e
  have hpoint (x : Vec d) : vecNormSq (u.grad x) =
      1 + 2 * vecDot e (r x) + vecDot (r x) (r x) := by
    have heq : u.grad x = e + r x := by dsimp [r]; abel
    rw [heq]
    simp only [vecNormSq, vecDot_add_left, vecDot_add_right]
    rw [show vecDot e e = 1 from he, vecDot_comm (r x) e]
    ring
  unfold volumeAverage
  simp_rw [hpoint]
  have hs : IntegrableOn (fun x => (1 : ℝ) + 2 * vecDot e (r x))
      (U : Set (Vec d)) := (integrable_const 1).add (hie.const_mul 2)
  rw [integral_add hs hi, integral_add (integrable_const 1) (hie.const_mul 2),
    integral_const, integral_const_mul, hz, mul_zero, add_zero]
  have hv := Internal.Ch02.BookCh02.domain_volume_pos U
  simp only [measureReal_restrict_apply_univ, smul_eq_mul, mul_one]
  change (volume (U : Set (Vec d))).toReal⁻¹ *
    ((volume (U : Set (Vec d))).toReal + ∫ x in (U : Set (Vec d)), vecDot (r x) (r x)) = _
  simp only [vecNormSq]
  dsimp only [r]
  field_simp [hv.ne']

/-- Every admissible solution is a trial in the genuine scalar response. -/
theorem responseValue_le_responseJ {d : ℕ} (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (p q : Vec d) (v : Ch02.Solution U a) :
    Ch02.responseValue U a p q v ≤ Ch02.responseJ U a p q := by
  obtain ⟨w, hw⟩ := Ch02.responseMaximizerExists U a p q
  rw [Ch02.responseJ_eq_responseValue_of_isResponseMaximizer hw.2]
  exact hw.2 v

/-- Scalar trials in the bottom-block response, evaluated on an actual
unit-slope affine Dirichlet solution. -/
theorem affineDirichlet_response_trial
    {d : ℕ} [NeZero d] (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    {ν : ℝ} (hsymm : ∀ x, symmPart (a.toCoeffField x) = ν • (1 : Mat d))
    {e : Vec d} (he : vecNormSq e = 1) {u : H1Function (U : Set (Vec d))}
    (hu : IsAffineDirichletSolution a.toCoeffField (U : Set (Vec d)) e u) (t : ℝ) :
    Ch02.responseValue U a 0 e (t • hu.toAHarmonicFunction) =
      -(t ^ 2 * ν / 2) *
        (1 + volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (u.grad x - e))) + t := by
  have hv := Internal.Ch02.BookCh02.domain_volume_pos U
  have hi : IntegrableOn (fun x => vecNormSq (u.grad x)) (U : Set (Vec d)) :=
    integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 u.grad_memVectorL2
  have hlinInt := integrableOn_vecDot_of_memVectorL2
    (Internal.Ch02.BookCh02.memVectorL2_const_vec e) u.grad_memVectorL2
  have hlin : volumeAverage (U : Set (Vec d)) (fun x => vecDot e (u.grad x)) = 1 := by
    rw [volumeAverage_vecDot_left e u.grad (fun i => (u.gradMemL2 i).integrable (by norm_num))]
    change vecDot e (volumeAverageVec (U : Set (Vec d)) u.grad) = 1
    rw [hu.averageGradient_eq hv.ne']
    exact he
  have hpoint (x : Vec d) :
      Ch02.responseIntegrand U a 0 e (t • hu.toAHarmonicFunction) x =
        -(t ^ 2 * ν / 2) * vecNormSq (u.grad x) + t * vecDot e (u.grad x) := by
    change -(1 / 2 * vecDot (t • u.grad x)
      (matVecMul (symmPart (a.toCoeffField x)) (t • u.grad x))) -
        vecDot 0 (matVecMul (a.toCoeffField x) (t • u.grad x)) +
        vecDot e (t • u.grad x) = _
    rw [hsymm, Internal.Ch02.BookCh02.matVecMul_smul_one]
    simp only [vecDot_smul_left, vecDot_smul_right, vecDot_zero_left, sub_zero, vecNormSq]
    ring
  change (volume (U : Set (Vec d))).toReal⁻¹ *
    (∫ x in (U : Set (Vec d)), Ch02.responseIntegrand U a 0 e (t • hu.toAHarmonicFunction) x) = _
  simp_rw [hpoint]
  rw [integral_add (hi.const_mul (-(t ^ 2 * ν / 2))) (hlinInt.const_mul t),
    integral_const_mul, integral_const_mul]
  calc
    _ = -(t ^ 2 * ν / 2) *
        volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (u.grad x)) +
        t * volumeAverage (U : Set (Vec d)) (fun x => vecDot e (u.grad x)) := by
      unfold volumeAverage vecNormSq
      ring
    _ = _ := by rw [affineDirichlet_grad_energy U he hu, hlin, mul_one]

/-- The bottom-block molecular trial estimate with a physical field carrying
the divergence of `k e`. Existence of the affine Dirichlet solution is proved
from the coefficient and domain, rather than assumed. -/
theorem molecular_lowerRight_of_physical_projection
    {d : ℕ} [NeZero d] (U : Ch02.Domain d) (a : Ch02.CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    {ν : ℝ} (hν : 0 < ν)
    (hsymm : ∀ x, symmPart (a.toCoeffField x) = ν • (1 : Mat d))
    {e : Vec d} (he : vecNormSq e = 1)
    {H : Vec d → Vec d} (hH : MemVectorL2 (U : Set (Vec d)) H)
    (hres : IsSolenoidalOn (U : Set (Vec d)) (fun x =>
      matVecMul (a.toCoeffField x) e - ν • e - H x)) :
    (ν + volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (H x)) / ν)⁻¹ ≤
      vecDot e (matVecMul (Homogenization.coarseBlockMatrix
        (U : Set (Vec d)) a.toCoeffField).lowerRight e) := by
  obtain ⟨u, hu⟩ := Internal.Ch02.BookCh02.exists_isAffineDirichletSolution_of_isEllipticFieldOn
    U a hEll e
  have hv := Internal.Ch02.BookCh02.domain_volume_pos U
  have hcor := affineDirichlet_corrector_energy_le U a hEll hsymm e hu hH hres
  have hc := mul_le_mul_of_nonneg_left hcor (inv_nonneg.mpr hv.le)
  have hbound : ν * volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (u.grad x - e)) ≤
      volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (H x)) / ν := by
    apply (le_div_iff₀ hν).mpr
    unfold volumeAverage vecNormSq
    convert hc using 1; ring
  let C := ν + volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (H x)) / ν
  have hZ : 0 ≤ volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (H x)) :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg) (integral_nonneg fun x => vecNormSq_nonneg _)
  have hC : 0 < C := add_pos_of_pos_of_nonneg hν (div_nonneg hZ hν.le)
  have hE : ν * (1 + volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (u.grad x - e))) ≤ C := by
    dsimp [C]
    linarith only [hbound]
  have hmul := mul_le_mul_of_nonneg_left hE (div_nonneg (sq_nonneg C⁻¹) (by norm_num : (0 : ℝ) ≤ 2))
  have htrial : (1 / (2 * C)) ≤ Ch02.responseJ U a 0 e := by
    calc
      1 / (2 * C) = -(C⁻¹ ^ 2 / 2) * C + C⁻¹ := by field_simp; ring
      _ ≤ -(C⁻¹ ^ 2 / 2) *
          (ν * (1 + volumeAverage (U : Set (Vec d)) (fun x => vecNormSq (u.grad x - e)))) + C⁻¹ := by
        linarith only [hmul]
      _ = Ch02.responseValue U a 0 e (C⁻¹ • hu.toAHarmonicFunction) := by
        rw [affineDirichlet_response_trial U a hsymm he hu]
        ring
      _ ≤ _ := responseValue_le_responseJ U a 0 e _
  have hmatrix : Ch02.responseJ U a 0 e = (1 / 2 : ℝ) *
      vecDot e (matVecMul (Homogenization.coarseBlockMatrix
        (U : Set (Vec d)) a.toCoeffField).lowerRight e) := by
    rw [Internal.Ch02.BookCh02.responseJ_eq_block_quadratic,
      ASDExplicitGamma.Variational.energyMap_coarseBlockMatrix_eq U a hEll]
    simp [blockVecDot, blockMatVecMul, vecDot_zero_left, matVecMul_zero]
  rw [hmatrix] at htrial
  change C⁻¹ ≤ _
  have heq : 1 / (2 * C) = C⁻¹ / 2 := by field_simp
  rw [heq] at htrial
  linarith only [htrial]

end ASDExplicitGamma.Scalar
