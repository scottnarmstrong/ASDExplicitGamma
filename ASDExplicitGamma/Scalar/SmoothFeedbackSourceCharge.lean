module

public import ASDExplicitGamma.Native.OldSignedResidualReciprocalEnergy
public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Native.OldSignedCompatibleMeans
public import ASDExplicitGamma.Native.OldSignedQ3SourceAdmissibility
public import ASDExplicitGamma.Scalar.SmoothFeedbackLambda8Source
public import ASDExplicitGamma.Scalar.SmoothFeedbackGapSourceForce
public import ASDExplicitGamma.Native.OldSignedPairingPartition
public import ASDExplicitGamma.Native.OldSignedCellAverageCauchy
public import ASDExplicitGamma.Native.OldSignedPatchedCellPairing

/-! Compatible-source weak-Haar charge for the literal OLD local cell solve. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Response Triadic Variational
open ASDExplicitGamma.Native

noncomputable section

private theorem smooth_feedback_pairing_congr_ae (Q : TriadicCube 2)
    (f : Vec 2 → ℝ) {g h : Vec 2 → ℝ}
    (hgh : g =ᵐ[volumeMeasureOn (openCubeSet Q)] h) :
    pairing Q f g = pairing Q f h := by
  rw [pairing, pairing, cubeAverage_eq_integralAverage_openCubeSet,
    cubeAverage_eq_integralAverage_openCubeSet]
  unfold integralAverage
  congr 1
  apply integral_congr_ae
  exact hgh.mono fun x hx => congrArg (fun y => f x * y) hx

/-- A parent source pairing against its actual finite patch of OLD cell
residuals is exactly the average of the literal cell pairings. -/
theorem smooth_feedback_source_local_residual_pairing_partition
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (f : Vec 2 → Vec 2)
    (hf : MemVectorL2 (openCubeSet Q) f) :
    scalarSourcePairing (openCubeSet Q) f
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun x => (f x, 0)) (memBlockL2_blockField hf MemLp.zero)) =
      oldSignedCellAverage Q depth (fun U =>
        scalarSourcePairing (openCubeSet U.val) f
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            nu sigma hnu hsigma k (fun x => (f x, 0))
            (memBlockL2_blockField hf MemLp.zero))) := by
  classical
  let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
  let hF : MemBlockL2 (openCubeSet Q) F := memBlockL2_blockField hf MemLp.zero
  let Y := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  have hY : MemBlockL2 (openCubeSet Q) Y :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k F hF
  have hfCoord (i : Fin 2) : MemLp (fun x => f x i) 2
      (normalizedCubeMeasure Q) := memLp_normalized_of_memL2On (hf.eval i)
  have hYVec : MemVectorL2 (openCubeSet Q) (fun x => (Y x).1) :=
    memVectorL2_fst_of_memBlockL2 hY
  have hYCoord (i : Fin 2) : MemLp (fun x => (Y x).1 i) 2
      (normalizedCubeMeasure Q) := memLp_normalized_of_memL2On (hYVec.eval i)
  have hParentPair : scalarSourcePairing (openCubeSet Q) f Y =
      ∑ i : Fin 2, pairing Q (fun x => f x i) (fun x => (Y x).1 i) := by
    simpa [scalarSourcePairing] using
      old_signed_vector_average_pairing Q f (fun x => (Y x).1) hf hYVec
  have hCellPair (U : OldSignedCellIndex Q depth) :
      scalarSourcePairing (openCubeSet U.val) f
          (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            nu sigma hnu hsigma k F hF) =
        ∑ i : Fin 2, pairing U.val (fun x => f x i)
          (fun x => (oldSignedCellResidual Q U.val
            (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
            nu sigma hnu hsigma k F hF x).1 i) := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let Z := oldSignedCellResidual Q U.val hRQ nu sigma hnu hsigma k F hF
    have hZ := Z.property
    have hZVec : MemVectorL2 (openCubeSet U.val) (fun x => (Z x).1) :=
      memVectorL2_fst_of_memBlockL2 hZ
    have hfU : MemVectorL2 (openCubeSet U.val) f :=
      hf.mono_measure (Measure.restrict_mono_set volume hRQ)
    change volumeAverage (openCubeSet U.val)
      (fun x => vecDot (f x) (Z x).1) = _
    exact old_signed_vector_average_pairing U.val f (fun x => (Z x).1) hfU hZVec
  have hcoord (i : Fin 2) :
      pairing Q (fun x => f x i) (fun x => (Y x).1 i) =
        oldSignedCellAverage Q depth (fun U =>
          pairing U.val (fun x => f x i)
            (fun x => (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              nu sigma hnu hsigma k F hF x).1 i)) := by
    rw [old_signed_pairing_partition Q depth (fun x => f x i)
      (fun x => (Y x).1 i) (hfCoord i) (hYCoord i),
      ← old_signed_cell_average_eq_descendantsAverage]
    congr 1
    funext U
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    have hRestr := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k F hF
      U.val U.property
    have hRestrCoord : (fun x => (Y x).1 i) =ᵐ[volumeMeasureOn (openCubeSet U.val)]
        (fun x => (oldSignedCellResidual Q U.val hRQ nu sigma hnu hsigma k F hF x).1 i) :=
      hRestr.mono fun x hx => congrArg (fun z : BlockVec 2 => z.1 i) hx
    exact smooth_feedback_pairing_congr_ae U.val (fun x => f x i) hRestrCoord
  calc
    scalarSourcePairing (openCubeSet Q) f Y =
        ∑ i : Fin 2, pairing Q (fun x => f x i) (fun x => (Y x).1 i) := hParentPair
    _ = ∑ i : Fin 2, oldSignedCellAverage Q depth (fun U =>
          pairing U.val (fun x => f x i)
            (fun x => (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              nu sigma hnu hsigma k F hF x).1 i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hcoord i
    _ = oldSignedCellAverage Q depth (fun U =>
          ∑ i : Fin 2, pairing U.val (fun x => f x i)
            (fun x => (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              nu sigma hnu hsigma k F hF x).1 i)) := by
      rw [← old_signed_cell_average_sum]
    _ = oldSignedCellAverage Q depth (fun U =>
          scalarSourcePairing (openCubeSet U.val) f
            (oldSignedCellResidual Q U.val
              (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
              nu sigma hnu hsigma k F hF)) := by
      congr 1
      funext U
      exact (hCellPair U).symm

/-- The complete OLD response history supremum across the physical depth-cell
family for a fixed parent coefficient. -/
noncomputable def smoothFeedbackSourceHistoryMaximum (Q : TriadicCube 2)
    (depth : ℕ) (nu sigma : ℝ) (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  Book.Ch02.finsetSupReal Finset.univ (fun U : OldSignedCellIndex Q depth =>
    lemmaVInverseHistory U
      (responseFramePlanarCoefficientField nu sigma
        (oldSignedCellCoefficient Q U
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
      ((3 : ℝ) ^ (1 / 4 : ℝ)))

theorem smooth_feedback_source_history_maximum_member_le
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) :
    lemmaVInverseHistory U
      (responseFramePlanarCoefficientField nu sigma
        (oldSignedCellCoefficient Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) k))
      ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
      smoothFeedbackSourceHistoryMaximum Q depth nu sigma k := by
  unfold smoothFeedbackSourceHistoryMaximum Book.Ch02.finsetSupReal
  let Ui : OldSignedCellIndex Q depth := ⟨U, hU⟩
  exact le_csSup (((Set.toFinite _).image _).bddAbove)
    ⟨Ui, Finset.mem_univ Ui, rfl⟩

theorem smooth_feedback_source_history_maximum_nonneg
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    0 ≤ smoothFeedbackSourceHistoryMaximum Q depth nu sigma k := by
  unfold smoothFeedbackSourceHistoryMaximum
  apply Book.Ch02.finsetSupReal_nonneg
  intro U _
  exact lemmaVInverseHistory_nonneg U.val
    (responseFramePlanarCoefficientField nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
    (Real.one_lt_rpow (by norm_num) (by norm_num))

/-- The first-block weak-Haar charge of the actual OLD cell residual is paid
by the inverse history on that cell and its actual cell energy. Compatibility
of the source is inherited by the residual because the removed field is an
actual zero-trace/zero-normal variation. -/
theorem smooth_feedback_old_cell_residual_weak_energy_of_compatible
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hCompat : ScalarCompatible (openCubeSet Q) F) :
    vectorWeakHaarEnergy R (fun x i =>
      (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF x).1 i) ≤
      lemmaVInverseHistory R
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q R hRQ k)) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        oldSignedEnergyPairing R nu sigma (oldSignedCellCoefficient Q R hRQ k)
          (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF)
          (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF) := by
  let kR := oldSignedCellCoefficient Q R hRQ k
  let Y := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF
  have hFcell : ScalarCompatible (openCubeSet R) F :=
    old_signed_compatible_restrict Q R hRQ hCompat
  have hRemoved := old_signed_cell_removed_variation Q R hRQ
    nu sigma hnu hsigma k F hF
  have hCorrection : ScalarCompatible (openCubeSet R) (fun x => F x - Y x) :=
    scalar_variation_compatible hRemoved
  have hYcompat : ScalarCompatible (openCubeSet R) Y := by
    have hsub := old_signed_compatible_sub hFcell hCorrection
    change ScalarCompatible (openCubeSet R)
      (fun x => F x - (F x - Y x)) at hsub
    simpa only [sub_sub_cancel] using hsub
  let aR := responseFramePlanarCoefficientField nu sigma kR
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet R) nu sigma hnu hsigma kR
  have hsqrt : 1 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hquarter : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hdiscount : (Real.sqrt 3)⁻¹ ≤ ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ := by
    apply (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num)) (by positivity)).2
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hhistory := lemmaVInverseHistory_le_of_inverse_discount R hEll
    hsqrt hquarter hdiscount
  have henergy : 0 ≤ oldSignedEnergyPairing R nu sigma kR Y Y := by
    exact old_signed_energy_pairing_nonneg R nu sigma hnu hsigma kR Y
  calc
    vectorWeakHaarEnergy R (fun x i => (Y x).1 i) ≤
        lemmaVInverseHistory R aR (Real.sqrt 3) *
          oldSignedEnergyPairing R nu sigma kR Y Y := by
      simpa [Y, aR, kR] using
        old_signed_compatible_weak_energy R nu sigma hnu hsigma kR hYcompat
    _ ≤ lemmaVInverseHistory R aR ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          oldSignedEnergyPairing R nu sigma kR Y Y :=
      mul_le_mul_of_nonneg_right hhistory henergy

/-- In particular, the charge estimate applies to an actual H10 projected
source potential on the parent square. The source field is its literal
gradient, and compatibility is obtained from that potential rather than
assumed as a separate estimate. -/
theorem smooth_feedback_h10_source_residual_weak_energy
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (u : H10Function (openCubeSet Q)) :
    vectorWeakHaarEnergy R (fun x i =>
      (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
        (fun x => (u.toH1Function.grad x, 0))
        (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero) x).1 i) ≤
      lemmaVInverseHistory R
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q R hRQ k)) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        oldSignedEnergyPairing R nu sigma (oldSignedCellCoefficient Q R hRQ k)
          (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
            (fun x => (u.toH1Function.grad x, 0))
            (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero))
          (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
            (fun x => (u.toH1Function.grad x, 0))
            (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero)) := by
  let F : Vec 2 → BlockVec 2 := fun x => (u.toH1Function.grad x, 0)
  have hF : MemBlockL2 (openCubeSet Q) F :=
    memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero
  have hCompat : ScalarCompatible (openCubeSet Q) F := by
    exact ⟨hF, ⟨u.toH1Function, rfl⟩, isSolenoidalOn_zero⟩
  simpa [F, hF] using
    smooth_feedback_old_cell_residual_weak_energy_of_compatible
      Q R hRQ nu sigma hnu hsigma k F hF hCompat

/-- For an actual H² parent source, the literal OLD cell source pairing pays
its squared cell mean up to the source's quarter-Haar oscillation times the
geometric mean of the local inverse-history charge and the actual local
residual energy. This is the local error term used in the depth-five source
patch. -/
theorem smooth_feedback_h2_cell_source_pairing_lower
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (u : H10Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    scalarSourcePairing (openCubeSet R) (fun x => u.toH1Function.grad x)
      (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
        (fun x => (u.toH1Function.grad x, 0))
        (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero)) ≥
      vecNormSq (fun i => cubeAverage R (fun x => u.toH1Function.grad x i)) -
      Real.sqrt (lemmaVInverseHistory R
          (responseFramePlanarCoefficientField nu sigma
            (oldSignedCellCoefficient Q R hRQ k)) ((3 : ℝ) ^ (1 / 4 : ℝ))) *
          Real.sqrt (oldSignedEnergyPairing R nu sigma
            (oldSignedCellCoefficient Q R hRQ k)
            (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
              (fun x => (u.toH1Function.grad x, 0))
              (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero))
            (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
              (fun x => (u.toH1Function.grad x, 0))
              (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero))) *
          Real.sqrt (vectorPositiveHaarEnergy R
            (fun x => u.toH1Function.grad x -
              fun i => cubeAverage R (fun y => u.toH1Function.grad y i))) := by
  let f : Vec 2 → Vec 2 := fun x => u.toH1Function.grad x
  let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
  have hfQ : MemLp f 2 (normalizedCubeMeasure Q) := by
    apply memLp_pi_iff.mpr
    intro i
    exact u.toH1Function.grad_memL2_normalizedCubeMeasure i
  have hfQvec : MemVectorL2 (openCubeSet Q) f := u.toH1Function.grad_memVectorL2
  have hfRvec : MemVectorL2 (openCubeSet R) f :=
    hfQvec.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hfRcoord (i : Fin 2) : MemLp (fun x => f x i) 2
      (normalizedCubeMeasure R) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hfRvec i)
  have hfR : MemLp f 2 (normalizedCubeMeasure R) := memLp_pi_iff.mpr hfRcoord
  have hadm := smooth_feedback_h2_projected_source_admissible Q R hRQ u H
  have hcenterQuarter' := hadm.2.2.1
  have hcenterQuarter : ScalarQuarterHaarAdmissible R
      (fun x => f x - fun i => cubeAverage R (fun y => f y i)) := by
    change ScalarQuarterHaarAdmissible R
      (fun x => u.toH1Function.grad x -
        fun i => cubeAverage R (fun y => u.toH1Function.grad y i)) at hcenterQuarter'
    simpa [f] using hcenterQuarter'
  have hpair := smooth_feedback_old_signed_cell_source_pairing_lower
    Q R hRQ nu sigma hnu hsigma k f hfQ hfR hcenterQuarter
  have hweak := smooth_feedback_h10_source_residual_weak_energy
    Q R hRQ nu sigma hnu hsigma k u
  let B := lemmaVInverseHistory R
    (responseFramePlanarCoefficientField nu sigma
      (oldSignedCellCoefficient Q R hRQ k)) ((3 : ℝ) ^ (1 / 4 : ℝ))
  let E := oldSignedEnergyPairing R nu sigma
    (oldSignedCellCoefficient Q R hRQ k)
    (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F
      (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero))
    (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F
      (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero))
  have hB : 0 ≤ B := by
    dsimp [B]
    exact lemmaVInverseHistory_nonneg R
      (responseFramePlanarCoefficientField nu sigma
        (oldSignedCellCoefficient Q R hRQ k))
      (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hE : 0 ≤ E := by
    dsimp [E]
    exact old_signed_energy_pairing_nonneg R nu sigma hnu hsigma
      (oldSignedCellCoefficient Q R hRQ k) _
  have hweak' : vectorWeakHaarEnergy R (fun x i =>
      (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F
        (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero) x).1 i) ≤
      B * E := by
    simpa [B, E, F, f] using hweak
  have hroot := Real.sqrt_le_sqrt hweak'
  have hrootMul : Real.sqrt (B * E) = Real.sqrt B * Real.sqrt E :=
    Real.sqrt_mul hB E
  have herror := mul_le_mul_of_nonneg_right hroot
    (Real.sqrt_nonneg (vectorPositiveHaarEnergy R
      (fun x => f x - fun i => cubeAverage R (fun y => f y i))))
  rw [hrootMul] at herror
  have hpair' :
      vecNormSq (fun i => cubeAverage R (fun x => f x i)) -
        Real.sqrt (vectorWeakHaarEnergy R (fun x i =>
          (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F
            (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero) x).1 i)) *
          Real.sqrt (vectorPositiveHaarEnergy R
            (fun x => f x - fun i => cubeAverage R (fun y => f y i))) ≤
        scalarSourcePairing (openCubeSet R) f
          (oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F
            (memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero)) := by
    simpa [F, f] using hpair
  apply le_trans ?_ hpair'
  exact sub_le_sub_left herror _

/-- The source cross term for a genuine H² parent potential is paid by its
actual finite OLD lift patch: local mean squares survive, while the summed
oscillatory error is bounded by the maximum actual cell history times the
patch energy and the source's positive-Haar oscillation. -/
theorem smooth_feedback_h2_source_patch_pairing_lower
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (u : H10Function (openCubeSet Q))
    (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function) :
    let f : Vec 2 → Vec 2 := u.toH1Function.grad
    let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
    let hF : MemBlockL2 (openCubeSet Q) F :=
      memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero
    let Y := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
    scalarSourcePairing (openCubeSet Q) f Y ≥
      oldSignedCellAverage Q depth (fun U =>
        vecNormSq (fun i => cubeAverage U.val (fun x => f x i))) -
        Real.sqrt (smoothFeedbackSourceHistoryMaximum Q depth nu sigma k *
          oldSignedEnergyPairing Q nu sigma k Y Y) *
          Real.sqrt (oldSignedCellAverage Q depth (fun U =>
            vectorPositiveHaarEnergy U.val
              (fun x => f x - fun i => cubeAverage U.val (fun y => f y i)))) := by
  classical
  dsimp only
  let f : Vec 2 → Vec 2 := fun x => u.toH1Function.grad x
  let F : Vec 2 → BlockVec 2 := fun x => (f x, 0)
  let hF : MemBlockL2 (openCubeSet Q) F :=
    memBlockL2_blockField u.toH1Function.grad_memVectorL2 MemLp.zero
  let Y : Vec 2 → BlockVec 2 :=
    oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  let I := OldSignedCellIndex Q depth
  let B (U : I) : ℝ := lemmaVInverseHistory U.val
    (responseFramePlanarCoefficientField nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k))
    ((3 : ℝ) ^ (1 / 4 : ℝ))
  let E (U : I) : ℝ := oldSignedEnergyPairing U.val nu sigma
    (oldSignedCellCoefficient Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
    (oldSignedCellResidual Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k F hF)
    (oldSignedCellResidual Q U.val
      (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
      nu sigma hnu hsigma k F hF)
  let P (U : I) : ℝ := vectorPositiveHaarEnergy U.val
    (fun x => f x - fun i => cubeAverage U.val (fun y => f y i))
  let C (U : I) : ℝ := vecNormSq (fun i => cubeAverage U.val (fun x => f x i))
  let Bmax := smoothFeedbackSourceHistoryMaximum Q depth nu sigma k
  let Pavg := oldSignedCellAverage Q depth P
  let Cavg := oldSignedCellAverage Q depth C
  let Eavg := oldSignedCellAverage Q depth E
  let pairAvg := oldSignedCellAverage Q depth (fun U =>
    scalarSourcePairing (openCubeSet U.val) f
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k F hF))
  have hPairPartition : scalarSourcePairing (openCubeSet Q) f Y = pairAvg := by
    simpa [Y, F, hF, pairAvg] using
      smooth_feedback_source_local_residual_pairing_partition
        Q depth nu sigma hnu hsigma k f u.toH1Function.grad_memVectorL2
  have hEnergyPartition : oldSignedEnergyPairing Q nu sigma k Y Y = Eavg := by
    simpa [Y, F, hF, E, Eavg] using
      old_signed_local_residual_cell_pairing Q depth nu sigma hnu hsigma k F F hF hF
  have hBmax : 0 ≤ Bmax := by
    exact smooth_feedback_source_history_maximum_nonneg Q depth nu sigma k
  have hLocal (U : I) : C U - Real.sqrt (B U * E U) * Real.sqrt (P U) ≤
      scalarSourcePairing (openCubeSet U.val) f
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k F hF) := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    have h := smooth_feedback_h2_cell_source_pairing_lower
      Q U.val hRQ nu sigma hnu hsigma k u H
    have hB0 : 0 ≤ B U := by
      dsimp [B]
      exact lemmaVInverseHistory_nonneg U.val
        (responseFramePlanarCoefficientField nu sigma
          (oldSignedCellCoefficient Q U.val hRQ k))
        (Real.one_lt_rpow (by norm_num) (by norm_num))
    have hRoot : Real.sqrt (B U * E U) = Real.sqrt (B U) * Real.sqrt (E U) :=
      Real.sqrt_mul hB0 (E U)
    have h' : C U ≤ scalarSourcePairing (openCubeSet U.val) f
        (oldSignedCellResidual Q U.val hRQ nu sigma hnu hsigma k F hF) +
        Real.sqrt (B U * E U) * Real.sqrt (P U) := by
      rw [hRoot]
      simpa [f, F, hF, C, B, E, P, hRQ] using h
    linarith [h']
  have hLocalAverage := old_signed_cell_average_mono Q depth hLocal
  have hLocalAverage' : Cavg -
      oldSignedCellAverage Q depth (fun U => Real.sqrt (B U * E U) * Real.sqrt (P U)) ≤ pairAvg := by
    simpa [Cavg, pairAvg, old_signed_cell_average_sub] using hLocalAverage
  have hB (U : I) : B U ≤ Bmax := by
    dsimp [B, Bmax, smoothFeedbackSourceHistoryMaximum]
    exact smooth_feedback_source_history_maximum_member_le Q depth nu sigma k
      U.val U.property
  have hE (U : I) : 0 ≤ E U := by
    dsimp [E]
    exact old_signed_energy_pairing_nonneg U.val nu sigma hnu hsigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) _
  have hP (U : I) : 0 ≤ P U := by
    dsimp [P]
    exact vectorPositiveHaarEnergy_nonneg U.val _
  have hErrPoint (U : I) : Real.sqrt (B U * E U) * Real.sqrt (P U) ≤
      Real.sqrt (Bmax * E U) * Real.sqrt (P U) := by
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg (P U))
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hB U) (hE U))
  have hErrPointwiseAverage := old_signed_cell_average_mono Q depth hErrPoint
  have hCauchy := old_signed_cell_average_root_cauchy Q depth
    (fun U => Bmax * E U) P
    (fun U => mul_nonneg hBmax (hE U)) hP
  have hErr : oldSignedCellAverage Q depth
        (fun U => Real.sqrt (B U * E U) * Real.sqrt (P U)) ≤
      Real.sqrt (Bmax * Eavg) * Real.sqrt Pavg := by
    calc
      _ ≤ oldSignedCellAverage Q depth
          (fun U => Real.sqrt (Bmax * E U) * Real.sqrt (P U)) := hErrPointwiseAverage
      _ ≤ Real.sqrt (oldSignedCellAverage Q depth (fun U => Bmax * E U)) *
          Real.sqrt Pavg := by simpa [Pavg, P] using hCauchy
      _ = Real.sqrt (Bmax * Eavg) * Real.sqrt Pavg := by
        rw [old_signed_cell_average_mul]
  have hEavg : Eavg = oldSignedEnergyPairing Q nu sigma k Y Y :=
    hEnergyPartition.symm
  calc
    scalarSourcePairing (openCubeSet Q) f Y = pairAvg := hPairPartition
    _ ≥ Cavg - Real.sqrt (Bmax * Eavg) * Real.sqrt Pavg := by
      have h := sub_le_sub_left hErr Cavg
      exact h.trans hLocalAverage'
    _ = Cavg - Real.sqrt (Bmax * oldSignedEnergyPairing Q nu sigma k Y Y) *
          Real.sqrt Pavg := by rw [hEavg]

/-- A finite family of actual H² parent sources obeys the same source-patch
lower bound, with the cell energies and source oscillations combined by one
Cauchy--Schwarz step. This is the source-cross-term estimate in the
finite-load form used by the smooth-feedback gap. -/
theorem smooth_feedback_h2_source_patch_family_pairing_lower
    {ι : Type*} (S : Finset ι)
    (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (u : ι → H10Function (openCubeSet Q))
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function) :
    let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
    let F : ι → Vec 2 → BlockVec 2 := fun i x => (f i x, 0)
    let hF : ∀ i, MemBlockL2 (openCubeSet Q) (F i) := fun i =>
      memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero
    let Y : ι → Vec 2 → BlockVec 2 := fun i =>
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k (F i) (hF i)
    let Cavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
      vecNormSq (fun j => cubeAverage U.val (fun x => f i x j)))
    let Eavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i)))
    let Pavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
      vectorPositiveHaarEnergy U.val
        (fun x => f i x - fun j => cubeAverage U.val (fun y => f i y j)))
    let Bmax := smoothFeedbackSourceHistoryMaximum Q depth nu sigma k
    (∑ i ∈ S, scalarSourcePairing (openCubeSet Q) (f i) (Y i)) ≥
      (∑ i ∈ S, Cavg i) -
        Real.sqrt (Bmax * (∑ i ∈ S, Eavg i)) *
          Real.sqrt (∑ i ∈ S, Pavg i) := by
  classical
  dsimp only
  let f : ι → Vec 2 → Vec 2 := fun i x => (u i).toH1Function.grad x
  let F : ι → Vec 2 → BlockVec 2 := fun i x => (f i x, 0)
  let hF : ∀ i, MemBlockL2 (openCubeSet Q) (F i) := fun i =>
    memBlockL2_blockField (u i).toH1Function.grad_memVectorL2 MemLp.zero
  let Y : ι → Vec 2 → BlockVec 2 := fun i =>
    oldSignedLocalResidual Q depth nu sigma hnu hsigma k (F i) (hF i)
  let Cavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
    vecNormSq (fun j => cubeAverage U.val (fun x => f i x j)))
  let Eavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
    oldSignedEnergyPairing U.val nu sigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (F i) (hF i))
      (oldSignedCellResidual Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        nu sigma hnu hsigma k (F i) (hF i)))
  let Pavg : ι → ℝ := fun i => oldSignedCellAverage Q depth (fun U =>
    vectorPositiveHaarEnergy U.val
      (fun x => f i x - fun j => cubeAverage U.val (fun y => f i y j)))
  let Bmax := smoothFeedbackSourceHistoryMaximum Q depth nu sigma k
  have hBmax : 0 ≤ Bmax :=
    smooth_feedback_source_history_maximum_nonneg Q depth nu sigma k
  have hEavg (i : ι) : 0 ≤ Eavg i := by
    change 0 ≤ oldSignedCellAverage Q depth (fun U =>
      oldSignedEnergyPairing U.val nu sigma
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k)
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i))
        (oldSignedCellResidual Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
          nu sigma hnu hsigma k (F i) (hF i)))
    apply old_signed_cell_average_nonneg Q depth
    intro U
    exact old_signed_energy_pairing_nonneg U.val nu sigma hnu hsigma
      (oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) _
  have hPavg (i : ι) : 0 ≤ Pavg i := by
    change 0 ≤ oldSignedCellAverage Q depth (fun U =>
      vectorPositiveHaarEnergy U.val
        (fun x => f i x - fun j => cubeAverage U.val (fun y => f i y j)))
    apply old_signed_cell_average_nonneg Q depth
    intro U
    exact vectorPositiveHaarEnergy_nonneg U.val _
  have hSingle (i : ι) :
      Cavg i - Real.sqrt (Bmax * Eavg i) * Real.sqrt (Pavg i) ≤
        scalarSourcePairing (openCubeSet Q) (f i) (Y i) := by
    have h := smooth_feedback_h2_source_patch_pairing_lower
      Q depth nu sigma hnu hsigma k (u i) (H i)
    have hEnergyPartition : oldSignedEnergyPairing Q nu sigma k (Y i) (Y i) =
        Eavg i := by
      simpa [Y, Eavg, F, hF] using
        old_signed_local_residual_cell_pairing Q depth nu sigma hnu hsigma k
          (F i) (F i) (hF i) (hF i)
    dsimp only at h
    rw [hEnergyPartition] at h
    simpa [f, F, hF, Y, Cavg, Eavg, Pavg, Bmax] using h
  have hsum := Finset.sum_le_sum (s := S) (fun i _ => hSingle i)
  have hsum' :
      (∑ i ∈ S, Cavg i) -
          (∑ i ∈ S, Real.sqrt (Bmax * Eavg i) * Real.sqrt (Pavg i)) ≤
        ∑ i ∈ S, scalarSourcePairing (openCubeSet Q) (f i) (Y i) := by
    simpa only [Finset.sum_sub_distrib] using hsum
  have hCauchy := Real.sum_sqrt_mul_sqrt_le (s := S)
    (f := fun i => Bmax * Eavg i) (g := Pavg)
    (fun i => mul_nonneg hBmax (hEavg i)) hPavg
  have hCauchy' :
      (∑ i ∈ S, Real.sqrt (Bmax * Eavg i) * Real.sqrt (Pavg i)) ≤
        Real.sqrt (Bmax * (∑ i ∈ S, Eavg i)) *
          Real.sqrt (∑ i ∈ S, Pavg i) := by
    calc
      _ ≤ Real.sqrt (∑ i ∈ S, Bmax * Eavg i) *
          Real.sqrt (∑ i ∈ S, Pavg i) := hCauchy
      _ = _ := by rw [Finset.mul_sum]
  nlinarith [hsum', hCauchy']

end

end ASDExplicitGamma.Scalar
