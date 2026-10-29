module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorForcedJoint
public import ASDExplicitGamma.Triadic.PositiveNormAggregation

/-! Aggregation of the joint source disk over an arbitrary source mesh. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

theorem pureFlux_forcedSourceCircleEnergy_le (Q : TriadicCube 2) (F : Vec 2 → Vec 2) :
    forcedSourceCircleEnergy Q F ≤ vectorPositiveHaarEnergy Q F := by
  have heq : vectorPositiveHaarEnergy Q F =
      (∑ i : Fin 2, energy Q (cubeIncrement Q 0 (fun x => F x i))) +
        forcedSourceCircleEnergy Q F := by
    unfold vectorPositiveHaarEnergy forcedSourceCircleEnergy primalEnergy
    rw [Finset.sum_add_distrib]
  have hn : 0 ≤ ∑ i : Fin 2, energy Q (cubeIncrement Q 0 (fun x => F x i)) :=
    Finset.sum_nonneg fun i _ => energy_nonneg Q _
  linarith

/-- The local joint disks combine before the single global source test. -/
theorem pureFlux_tiled_feedback_aggregation (Q : TriadicCube 2) (m : ℕ)
    (F G V : Vec 2 → Vec 2) (X E : TriadicCube 2 → ℝ) (B E0 : ℝ)
    (hB : 0 ≤ B) (hE0 : 0 ≤ E0)
    (hX : ∀ R ∈ descendantsAtDepth Q m, 0 ≤ X R)
    (hjoint : ∀ R ∈ descendantsAtDepth Q m,
      X R + vectorWeakHaarEnergy R G ≤ B * E R)
    (hgrad : ∀ R ∈ descendantsAtDepth Q m,
      Real.sqrt (vectorWeakHaarEnergy R V) ≤ Real.sqrt (X R) +
        (3 : ℝ)^(-(1/4:ℝ))*B*Real.sqrt (vectorPositiveHaarEnergy R F))
    (hE : descendantsAverage Q m E = E0)
    (htest : E0 ≤ Real.sqrt (lemmaVTiledWeakEnergy Q m G) *
      Real.sqrt (lemmaVTiledPositiveEnergy Q m F)) :
    E0 ≤ B * lemmaVTiledPositiveEnergy Q m F ∧
    Real.sqrt (lemmaVTiledWeakEnergy Q m V) ≤
      (1/2+(3:ℝ)^(-(1/4:ℝ)))*B*Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := by
  let P := lemmaVTiledPositiveEnergy Q m F
  let K := lemmaVTiledWeakEnergy Q m G
  let A := descendantsAverage Q m X
  have hP : 0 ≤ P := lemmaVTiledPositiveEnergy_nonneg Q m F
  have hK : 0 ≤ K := lemmaVTiledWeakEnergy_nonneg Q m G
  have hA : 0 ≤ A := by
    dsimp [A, descendantsAverage]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg hX)
  have hj : A + K ≤ B * E0 := by
    rw [← hE]
    dsimp only [A, K, lemmaVTiledWeakEnergy, descendantsAverage]
    have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hjoint)
      (show 0 ≤ ((descendantsAtDepth Q m).card:ℝ)⁻¹ by positivity)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
    nlinarith only [hh]
  have htest' : E0 ≤ Real.sqrt K * Real.sqrt P := htest
  have hKn : Real.sqrt K ≤ B * Real.sqrt P := by
    have hsK := Real.sq_sqrt hK
    have hsP := Real.sq_sqrt hP
    have hb : K ≤ B*(Real.sqrt K*Real.sqrt P) :=
      (le_add_of_nonneg_left hA).trans (hj.trans (mul_le_mul_of_nonneg_left htest' hB))
    have hnon := Real.sqrt_nonneg K
    nlinarith [mul_nonneg hB (Real.sqrt_nonneg P)]
  have henergy : E0 ≤ B*P := by
    calc
      E0 ≤ Real.sqrt K * Real.sqrt P := htest'
      _ ≤ (B*Real.sqrt P)*Real.sqrt P := mul_le_mul_of_nonneg_right hKn (Real.sqrt_nonneg P)
      _ = B*P := by rw [mul_assoc, ← sq, Real.sq_sqrt hP]
  have hhalf : Real.sqrt A ≤ B*Real.sqrt P/2 := by
    apply forcedSource_half_gain_of_joint_energy (X := Real.sqrt A)
      (G := Real.sqrt K) hB (Real.sqrt_nonneg P)
    rw [Real.sq_sqrt hA, Real.sq_sqrt hK]
    calc
      A+K ≤ B*E0 := hj
      _ ≤ B*(Real.sqrt K*Real.sqrt P) := mul_le_mul_of_nonneg_left htest' hB
      _ = B*Real.sqrt P*Real.sqrt K := by ring
  have ha : 0 ≤ (3:ℝ)^(-(1/4:ℝ))*B := mul_nonneg (by positivity) hB
  have hag := sqrt_descendantsAverage_energy_bound_three Q m
    (fun R => vectorWeakHaarEnergy R V) X
    (fun R => vectorPositiveHaarEnergy R F) (fun _ => 0)
    (by norm_num : (0:ℝ) ≤ 1) ha (by norm_num : (0:ℝ) ≤ 0)
    (fun R _ => vectorWeakHaarEnergy_nonneg R V) hX
    (fun R _ => vectorPositiveHaarEnergy_nonneg R F) (fun _ _ => le_rfl)
    (fun R hR => by simpa only [one_mul, zero_mul, add_zero] using hgrad R hR)
  simp only [one_mul, zero_mul, add_zero] at hag
  refine ⟨henergy, ?_⟩
  change Real.sqrt (descendantsAverage Q m (fun R => vectorWeakHaarEnergy R V)) ≤ _
  calc
    _ ≤ Real.sqrt A + (3:ℝ)^(-(1/4:ℝ))*B*Real.sqrt P := hag
    _ ≤ B*Real.sqrt P/2+(3:ℝ)^(-(1/4:ℝ))*B*Real.sqrt P := add_le_add hhalf le_rfl
    _ = _ := by ring

/-- A parent forced equation yields the sharp broken source estimates. -/
theorem pureFlux_forced_pair_tiled_bound (Q : TriadicCube 2) (m : ℕ)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2)
    (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    (hWsol : IsBlockSolenoidalOn (openCubeSet Q) W)
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval)
    (hWlower : MemVectorL2 (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2))
    {F : Vec 2 → Vec 2} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ R ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
      Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy R (cubeIncrement R (j + 1) (fun x => F x i))))
    (hforced : ∀ T : BlockState 2, ScalarVariation (openCubeSet Q) T.eval →
      volumeAverage (openCubeSet Q) (blockPairingIntegrand a T W) =
        volumeAverage (openCubeSet Q) (fun x => vecDot (T.potential x) (F x)))
    (u : H1Function (openCubeSet Q))
    (hu : (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] u.grad)
    (htest : blockPairingAverage (openCubeSet Q) a W W =
      cubeAverage Q (fun x => vecDot (W.potential x) (F x)))
    (B : ℝ) (hB : 0 ≤ B)
    (hhist : ∀ R ∈ descendantsAtDepth Q m,
      lemmaVInverseHistory R a ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    blockPairingAverage (openCubeSet Q) a W W ≤
      B * lemmaVTiledPositiveEnergy Q m F ∧
    Real.sqrt (lemmaVTiledWeakEnergy Q m u.grad) ≤
      (1/2+(3:ℝ)^(-(1/4:ℝ)))*B*Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := by
  classical
  letI pureFluxTiledParentFiniteMeasure : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let U := openCubeSet Q
  have hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hlocal (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q m) :
      ∃ X : ℝ, 0 ≤ X ∧ X + vectorWeakHaarEnergy R W.potential ≤
        B * cubeAverage R (blockPairingIntegrand a W W) ∧
        Real.sqrt (vectorWeakHaarEnergy R u.grad) ≤ Real.sqrt X +
          (3:ℝ)^(-(1/4:ℝ))*B*Real.sqrt (vectorPositiveHaarEnergy R F) := by
    let Vset := openCubeSet R
    letI pureFluxTiledCellFiniteMeasure : IsFiniteMeasure (volumeMeasureOn Vset) :=
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
    have hRQ : Vset ⊆ U := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
    have hWmemR : MemBlockL2 Vset W.eval :=
      hWmem.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hWpotentialMemR : MemVectorL2 Vset W.potential :=
      memVectorL2_fst_of_memBlockL2 hWmemR
    have hWfluxMemR : MemVectorL2 Vset W.flux :=
      memVectorL2_snd_of_memBlockL2 hWmemR
    have hWpotR : IsBlockPotentialOn Vset W := by
      change IsPotentialOn U W.potential at hWpot
      change IsPotentialOn Vset W.potential
      obtain ⟨z, hz⟩ := hWpot
      have hgradMemR : MemVectorL2 Vset z.grad := by
        simpa only [hz] using hWpotentialMemR
      simpa only [hz] using z.isPotentialOn.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hgradMemR
    have hWsolR : IsBlockSolenoidalOn Vset W := by
      change IsSolenoidalOn U W.flux at hWsol
      change IsSolenoidalOn Vset W.flux
      exact hWsol.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hWfluxMemR
    have hWlowerR : MemVectorL2 Vset
        (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) :=
      hWlower.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hGmemR : MemVectorL2 Vset F :=
      hFvec.mono_measure (Measure.restrict_mono_set volume hRQ)

    let uR := u.restrictToOpenSubcube hR
    have huR : (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) =ᵐ[
        volumeMeasureOn Vset] uR.grad :=
      ae_restrict_of_ae_restrict_of_subset hRQ hu
    have hFR : MemLp F 2 (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic hR hF
    obtain ⟨X, hX, hj, hg⟩ := pureFlux_forced_pair_joint_bound R hEllR W
      hWpotR hWsolR hWmemR hWlowerR hFR (hFpos R hR)
      (forcedSource_weakEquation_onDescendant Q m R hR W F hforced) uR huR
    have heq : blockPairingAverage Vset a W W =
        cubeAverage R (blockPairingIntegrand a W W) := by
      rw [blockPairingAverage, cubeAverage_eq_integralAverage_openCubeSet]
      rfl
    refine ⟨X, hX, ?_, ?_⟩
    · rw [← heq]
      exact hj.trans (mul_le_mul_of_nonneg_right (hhist R hR)
        (compatible_blockPairingAverage_nonneg hEllR W))
    · calc
        _ ≤ Real.sqrt X + (3:ℝ)^(-(1/4:ℝ))*
            lemmaVInverseHistory R a ((3:ℝ)^(1/4:ℝ))*
              Real.sqrt (forcedSourceCircleEnergy R F) := hg
        _ ≤ Real.sqrt X + (3:ℝ)^(-(1/4:ℝ))*B*
              Real.sqrt (forcedSourceCircleEnergy R F) := by
          apply add_le_add le_rfl
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left (hhist R hR) (by positivity)
        _ ≤ _ := by
          apply add_le_add le_rfl
          exact mul_le_mul_of_nonneg_left
            (Real.sqrt_le_sqrt (pureFlux_forcedSourceCircleEnergy_le R F))
            (mul_nonneg (by positivity) hB)
  let X : TriadicCube 2 → ℝ := fun R => if hR : R ∈ descendantsAtDepth Q m then
    (hlocal R hR).choose else 0
  have hXs (R) (hR : R ∈ descendantsAtDepth Q m) := (hlocal R hR).choose_spec
  have hXeq (R) (hR : R ∈ descendantsAtDepth Q m) :
      X R = (hlocal R hR).choose := dif_pos hR
  have hE : descendantsAverage Q m (fun R => cubeAverage R (blockPairingIntegrand a W W)) =
      blockPairingAverage U a W W := by
    have hInt := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hWmem hEll
    rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q m _
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hInt)]
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    rfl
  have hWcoord (i : Fin 2) : MemLp (fun x => W.potential x i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hWmem) i)
  have hFcoord (i : Fin 2) : MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hFvec i)
  have hd := lemmaV_tiled_pairing_le Q m hWcoord hFcoord hFpos
  have ht : blockPairingAverage U a W W ≤
      Real.sqrt (lemmaVTiledWeakEnergy Q m W.potential)*
        Real.sqrt (lemmaVTiledPositiveEnergy Q m F) := by
    rw [htest]
    exact (le_abs_self _).trans hd
  exact pureFlux_tiled_feedback_aggregation Q m F W.potential u.grad X
    (fun R => cubeAverage R (blockPairingIntegrand a W W)) B
    (blockPairingAverage U a W W) hB (compatible_blockPairingAverage_nonneg hEll W)
    (fun R hR => by rw [hXeq R hR]; exact (hXs R hR).1)
    (fun R hR => by rw [hXeq R hR]; exact (hXs R hR).2.1)
    (fun R hR => by rw [hXeq R hR]; exact (hXs R hR).2.2) hE ht

end
end ASDExplicitGamma.Inverse
