module

public import ASDExplicitGamma.Variational.ProjectedSource
public import ASDExplicitGamma.Variational.LemmaVTiles
public import ASDExplicitGamma.Variational.LemmaVMinimizer
public import ASDExplicitGamma.Triadic.PlanarConstants
public import ASDExplicitGamma.Triadic.DiagBessel
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge

/-! Half-gain feedback for the first potential of a projected pure source. -/

@[expose] public section
namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable section

theorem forcedSource_half_gain_of_joint_energy
    {B P X G : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P)
    (h : X ^ 2 + G ^ 2 ≤ B * P * G) : X ≤ B * P / 2 := by
  have hBP : 0 ≤ B * P := mul_nonneg hB hP
  have hGmax : B * P * G - G ^ 2 ≤ (B * P / 2) ^ 2 := by
    have hsq : 0 ≤ (G - B * P / 2) ^ 2 := sq_nonneg _
    nlinarith
  have hXsq : X ^ 2 ≤ (B * P / 2) ^ 2 := by nlinarith
  nlinarith

noncomputable def forcedSourceCircleEnergy (Q : TriadicCube 2)
    (F : Vec 2 → Vec 2) : ℝ :=
  ∑ i : Fin 2, ∑' k : ℕ, (Real.sqrt 3) ^ (k + 1) *
    energy Q (cubeIncrement Q (k + 1) (fun x => F x i))

theorem forcedSourceCircleEnergy_nonneg (Q : TriadicCube 2)
    (F : Vec 2 → Vec 2) : 0 ≤ forcedSourceCircleEnergy Q F := by
  unfold forcedSourceCircleEnergy
  apply Finset.sum_nonneg
  intro i hi
  apply tsum_nonneg
  intro k
  exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (energy_nonneg Q _)

private theorem forcedSource_cubeIncrement_local_eq (Q R : TriadicCube 2)
    (j n : ℕ) (F : Vec 2 → ℝ) (hR : R ∈ descendantsAtDepth Q j) :
    ∀ x ∈ cubeSet R,
      cubeIncrement R (n + 1) F x = cubeIncrement Q (j + (n + 1)) F x := by
  intro x hx
  have hproj (k : ℕ) : cubeProjection R k F x = cubeProjection Q (j + k) F x := by
    obtain ⟨S, hS, hxS⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet k hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth F hS hxS,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth F
        (mem_descendantsAtDepth_add hR hS) hxS]
  simp only [cubeIncrement]
  rw [hproj (n + 1), hproj n]
  congr 1

theorem forcedSource_energy_localIncrement_eq (Q R : TriadicCube 2)
    (j n : ℕ) (F : Vec 2 → ℝ) (hR : R ∈ descendantsAtDepth Q j) :
    energy R (cubeIncrement R (n + 1) F) =
      energy R (cubeIncrement Q (j + (n + 1)) F) := by
  unfold energy pairing
  apply cubeAverage_congr_on_cubeSet
  intro x hx
  rw [forcedSource_cubeIncrement_local_eq Q R j n F hR x hx]

/-- Positive Haar convergence of a source is inherited by every descendant.
The descendant increments are the corresponding tail of the parent martingale,
and the cell energy is bounded by the full descendant average. -/
theorem forcedSource_positiveSeries_onDescendant (Q : TriadicCube 2) (j : ℕ)
    {F : Vec 2 → Vec 2} (hFpos : ∀ i : Fin 2, Summable (fun k : ℕ =>
      (Real.sqrt 3) ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) (fun x => F x i))))
    (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) (i : Fin 2) :
    Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy R (cubeIncrement R (k + 1) (fun x => F x i))) := by
  let q : ℝ := Real.sqrt 3
  let D := descendantsAtDepth Q j
  have hqpos : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hlocalTail : Summable (fun k : ℕ => q ^ (j + k + 1) *
      energy Q (cubeIncrement Q (j + k + 1) (fun x => F x i))) := by
    have hs := (summable_nat_add_iff j).2 (hFpos i)
    simpa [q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hcard : 0 < (D.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j))
  have hdom (k : ℕ) : 0 ≤ q ^ (k + 1) *
      energy R (cubeIncrement R (k + 1) (fun x => F x i)) :=
    mul_nonneg (pow_nonneg hqpos.le _) (energy_nonneg R _)
  have hbound (k : ℕ) : q ^ (k + 1) *
      energy R (cubeIncrement R (k + 1) (fun x => F x i)) ≤
      ((D.card : ℝ) * q⁻¹ ^ j) *
        (q ^ (j + k + 1) * energy Q
          (cubeIncrement Q (j + k + 1) (fun x => F x i))) := by
    have hmem : MemLp (cubeIncrement Q (j + (k + 1)) (fun x => F x i))
        2 (normalizedCubeMeasure Q) := increment_memLp Q (j + (k + 1)) _
    have havg : energy Q (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) =
        descendantsAverage Q j (fun S => energy S
          (cubeIncrement Q (j + (k + 1)) (fun x => F x i))) :=
      energy_eq_descendantsAverage Q j hmem
    have hsum := Finset.single_le_sum
      (s := D) (f := fun S => energy S
        (cubeIncrement Q (j + (k + 1)) (fun x => F x i)))
      (fun S hS => energy_nonneg S _) hR
    have hcell : energy R (cubeIncrement R (k + 1) (fun x => F x i)) ≤
        (D.card : ℝ) * energy Q
          (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) := by
      rw [forcedSource_energy_localIncrement_eq Q R j k _ hR]
      calc
        energy R (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) ≤
            ∑ S ∈ D, energy S (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) := hsum
        _ = (D.card : ℝ) * energy Q
            (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) := by
              rw [havg]
              simp only [descendantsAverage, D]
              have hcardne : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := ne_of_gt hcard
              field_simp
    have hpow : q ^ (k + 1) = q⁻¹ ^ j * q ^ (j + (k + 1)) := by
      rw [inv_pow]
      have hsum : q ^ (j + (k + 1)) = q ^ j * q ^ (k + 1) := by rw [pow_add]
      rw [hsum, pow_succ]
      field_simp [pow_ne_zero _ hqpos.ne']
    rw [hpow]
    have hfactor : 0 ≤ q⁻¹ ^ j * q ^ (j + (k + 1)) :=
      mul_nonneg (pow_nonneg (inv_nonneg.mpr hqpos.le) j) (pow_nonneg hqpos.le _)
    calc
      q⁻¹ ^ j * q ^ (j + (k + 1)) *
          energy R (cubeIncrement R (k + 1) (fun x => F x i)) ≤
          q⁻¹ ^ j * q ^ (j + (k + 1)) *
            ((D.card : ℝ) * energy Q
              (cubeIncrement Q (j + (k + 1)) (fun x => F x i))) :=
        mul_le_mul_of_nonneg_left hcell hfactor
      _ = ((D.card : ℝ) * q⁻¹ ^ j) *
          (q ^ (j + k + 1) * energy Q
            (cubeIncrement Q (j + k + 1) (fun x => F x i))) := by
        simp [Nat.add_assoc]
        ring
  exact Summable.of_nonneg_of_le hdom hbound
    (hlocalTail.mul_left ((D.card : ℝ) * q⁻¹ ^ j))

theorem forcedSource_circleRestriction_le (Q : TriadicCube 2) (j : ℕ)
    {F : Vec 2 → Vec 2}
    (hFpos : ∀ i : Fin 2, Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => F x i)))) :
    descendantsAverage Q j (fun R => forcedSourceCircleEnergy R F) ≤
      ((Real.sqrt 3)⁻¹) ^ j * forcedSourceCircleEnergy Q F := by
  let q : ℝ := Real.sqrt 3
  let D := descendantsAtDepth Q j
  have hqpos : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hq1 : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hlocal (R : TriadicCube 2) (hR : R ∈ D) (i : Fin 2) :
      Summable (fun k : ℕ => q ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) (fun x => F x i))) := by
    let f : ℕ → ℝ := fun n => q ^ (n + 1) *
      energy Q (cubeIncrement Q (n + 1) (fun x => F x i))
    let tail : ℕ → ℝ := fun k => q ^ (j + k + 1) *
      energy Q (cubeIncrement Q (j + k + 1) (fun x => F x i))
    have htail : Summable tail := by
      have hs := (summable_nat_add_iff j).2 (hFpos i)
      simpa [tail, f, q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
    have hcard : 0 < (D.card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j))
    have hdom (k : ℕ) : 0 ≤ q ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) (fun x => F x i)) :=
      mul_nonneg (pow_nonneg hqpos.le _) (energy_nonneg R _)
    have hbound (k : ℕ) : q ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) (fun x => F x i)) ≤
        ((D.card : ℝ) * q⁻¹ ^ j) * tail k := by
      have hmem : MemLp (cubeIncrement Q (j + (k + 1)) (fun x => F x i))
          2 (normalizedCubeMeasure Q) := increment_memLp Q (j + (k + 1)) _
      have havg : energy Q (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) =
          descendantsAverage Q j (fun S => energy S
            (cubeIncrement Q (j + (k + 1)) (fun x => F x i))) :=
        energy_eq_descendantsAverage Q j hmem
      have hsum := Finset.single_le_sum
        (s := D) (f := fun S => energy S
          (cubeIncrement Q (j + (k + 1)) (fun x => F x i)))
        (fun S hS => energy_nonneg S _) hR
      have hcell : energy R (cubeIncrement R (k + 1) (fun x => F x i)) ≤
          (D.card : ℝ) * energy Q
            (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) := by
        rw [forcedSource_energy_localIncrement_eq Q R j k _ hR]
        calc
          energy R (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) ≤
              ∑ S ∈ D, energy S (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) := hsum
          _ = (D.card : ℝ) * energy Q
              (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) := by
                rw [havg]
                simp only [descendantsAverage, D]
                have hcardne : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := ne_of_gt hcard
                field_simp
      have hpow : q ^ (k + 1) = q⁻¹ ^ j * q ^ (j + (k + 1)) := by
        rw [inv_pow]
        have hsum : q ^ (j + (k + 1)) = q ^ j * q ^ (k + 1) := by
          rw [pow_add]
        rw [hsum, pow_succ]
        field_simp [pow_ne_zero _ hqpos.ne']
      rw [hpow]
      have hfactor : 0 ≤ q⁻¹ ^ j * q ^ (j + (k + 1)) :=
        mul_nonneg (pow_nonneg (inv_nonneg.mpr hqpos.le) j) (pow_nonneg hqpos.le _)
      calc
        q⁻¹ ^ j * q ^ (j + (k + 1)) *
            energy R (cubeIncrement R (k + 1) (fun x => F x i)) ≤
            q⁻¹ ^ j * q ^ (j + (k + 1)) *
              ((D.card : ℝ) * energy Q
                (cubeIncrement Q (j + (k + 1)) (fun x => F x i))) :=
          mul_le_mul_of_nonneg_left hcell hfactor
        _ = ((D.card : ℝ) * q⁻¹ ^ j) * tail k := by
          simp [tail, Nat.add_assoc]
          ring
    exact Summable.of_nonneg_of_le hdom hbound
      (htail.mul_left ((D.card : ℝ) * q⁻¹ ^ j))
  have hlevel (i : Fin 2) :
      descendantsAverage Q j (fun R => ∑' k : ℕ, q ^ (k + 1) *
          energy R (cubeIncrement R (k + 1) (fun x => F x i))) ≤
        q⁻¹ ^ j * ∑' k : ℕ, q ^ (k + 1) *
          energy Q (cubeIncrement Q (k + 1) (fun x => F x i)) := by
    let localTerm : TriadicCube 2 → ℕ → ℝ := fun R k => q ^ (k + 1) *
      energy R (cubeIncrement R (k + 1) (fun x => F x i))
    have hswap : (∑' k : ℕ, ∑ R ∈ D, localTerm R k) =
        ∑ R ∈ D, ∑' k : ℕ, localTerm R k :=
      Summable.tsum_finsetSum fun R hR => hlocal R hR i
    have havg (k : ℕ) : descendantsAverage Q j
        (fun R => energy R (cubeIncrement R (k + 1) (fun x => F x i))) =
        energy Q (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) := by
      calc
        descendantsAverage Q j
            (fun R => energy R (cubeIncrement R (k + 1) (fun x => F x i))) =
            descendantsAverage Q j
              (fun R => energy R (cubeIncrement Q (j + (k + 1))
                (fun x => F x i))) := by
                  unfold descendantsAverage
                  apply congrArg (fun z : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * z)
                  apply Finset.sum_congr rfl
                  intro R hR
                  exact forcedSource_energy_localIncrement_eq Q R j k _ hR
        _ = energy Q (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) :=
          (energy_eq_descendantsAverage Q j
            (increment_memLp Q (j + (k + 1)) (fun x => F x i))).symm
    unfold descendantsAverage
    dsimp [D]
    calc
      _ = ((↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth Q j, ∑' k, localTerm R k) := by
            rfl
      _ = ((↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
          ∑' k, ∑ R ∈ descendantsAtDepth Q j, localTerm R k) := by rw [← hswap]
      _ = ∑' k, q ^ (k + 1) *
          energy Q (cubeIncrement Q (j + (k + 1)) (fun x => F x i)) := by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro k
            change ((↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
                ∑ R ∈ descendantsAtDepth Q j, q ^ (k + 1) *
                  energy R (cubeIncrement R (k + 1) (fun x => F x i))) = _
            calc
              _ = ((↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
                  (q ^ (k + 1) * ∑ R ∈ descendantsAtDepth Q j,
                    energy R (cubeIncrement R (k + 1) (fun x => F x i)))) := by
                      rw [← Finset.mul_sum]
              _ = q ^ (k + 1) *
                  ((↑(descendantsAtDepth Q j).card : ℝ)⁻¹ *
                    ∑ R ∈ descendantsAtDepth Q j,
                      energy R (cubeIncrement R (k + 1) (fun x => F x i))) := by ring
              _ = q ^ (k + 1) *
                  descendantsAverage Q j (fun R => energy R
                    (cubeIncrement R (k + 1) (fun x => F x i))) := rfl
              _ = _ := by rw [havg k]
      _ ≤ q⁻¹ ^ j * ∑' k, q ^ (k + 1) *
          energy Q (cubeIncrement Q (k + 1) (fun x => F x i)) := by
            have hseries : Summable (fun n : ℕ => q ^ (n + 1) *
                energy Q (cubeIncrement Q (n + 1) (fun x => F x i))) := by
              simpa [q] using hFpos i
            have htail : Summable (fun k : ℕ => q ^ (j + k + 1) *
                energy Q (cubeIncrement Q (j + k + 1) (fun x => F x i))) := by
              have hs := (summable_nat_add_iff j).2 hseries
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
            have htailEq : (∑' k : ℕ, q ^ (k + 1) *
                energy Q (cubeIncrement Q (j + (k + 1)) (fun x => F x i))) =
                q⁻¹ ^ j * ∑' k : ℕ, q ^ (j + k + 1) *
                  energy Q (cubeIncrement Q (j + k + 1) (fun x => F x i)) := by
              rw [← tsum_mul_left]
              apply tsum_congr
              intro k
              have hpow : q ^ (k + 1) = q⁻¹ ^ j * q ^ (j + k + 1) := by
                rw [inv_pow]
                have hsum : q ^ (j + k + 1) = q ^ j * q ^ (k + 1) := by
                  have hidx : j + k + 1 = j + (k + 1) := by omega
                  rw [hidx, pow_add]
                rw [hsum, pow_succ]
                field_simp [pow_ne_zero _ hqpos.ne']
              rw [hpow]
              have hidx : j + (k + 1) = j + k + 1 := by omega
              rw [hidx]
              ring
            have htaille : (∑' k : ℕ, q ^ (j + k + 1) *
                energy Q (cubeIncrement Q (j + k + 1) (fun x => F x i))) ≤
                ∑' n : ℕ, q ^ (n + 1) *
                  energy Q (cubeIncrement Q (n + 1) (fun x => F x i)) := by
              have hsplit := hseries.sum_add_tsum_nat_add j
              have hprefix : 0 ≤ ∑ n ∈ Finset.range j,
                  q ^ (n + 1) * energy Q (cubeIncrement Q (n + 1) (fun x => F x i)) :=
                Finset.sum_nonneg fun n hn =>
                  mul_nonneg (pow_nonneg hqpos.le _) (energy_nonneg Q _)
              have hsplit' :
                  (∑ n ∈ Finset.range j, q ^ (n + 1) *
                    energy Q (cubeIncrement Q (n + 1) (fun x => F x i))) +
                    (∑' k : ℕ, q ^ (j + k + 1) *
                      energy Q (cubeIncrement Q (j + k + 1) (fun x => F x i))) =
                    ∑' n : ℕ, q ^ (n + 1) *
                      energy Q (cubeIncrement Q (n + 1) (fun x => F x i)) := by
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit
              linarith
            rw [htailEq]
            exact mul_le_mul_of_nonneg_left htaille
              (pow_nonneg (inv_nonneg.mpr hqpos.le) j)
  have hsum :
      descendantsAverage Q j (fun R => forcedSourceCircleEnergy R F) =
        ∑ i : Fin 2, descendantsAverage Q j (fun R =>
          ∑' k : ℕ, q ^ (k + 1) * energy R (cubeIncrement R (k + 1)
            (fun x => F x i))) := by
    unfold forcedSourceCircleEnergy
    exact Triadic.descendantsAverage_sum (fun i R => ∑' k : ℕ, q ^ (k + 1) *
      energy R (cubeIncrement R (k + 1) (fun x => F x i)))
  rw [hsum]
  calc
    _ ≤ ∑ i : Fin 2, q⁻¹ ^ j *
        ∑' k : ℕ, q ^ (k + 1) *
          energy Q (cubeIncrement Q (k + 1) (fun x => F x i)) :=
      Finset.sum_le_sum fun i _ => hlevel i
    _ = _ := by
      unfold forcedSourceCircleEnergy
      rw [Finset.mul_sum]

private theorem projectedSourceLoad_eq_components (Q : TriadicCube 2)
    {F : Vec 2 → Vec 2} (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    projectedSourceLoad Q hF =
      toHilbertBlockL2OfComponents (MemLp.zero : MemVectorL2 (openCubeSet Q) 0)
        (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF) := by
  let U := openCubeSet Q
  let hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hzero : MemVectorL2 U (0 : Vec 2 → Vec 2) := MemLp.zero
  have hblock : hilbertBlockL2ToBlockL2 (projectedSourceLoad Q hF) =
      toBlockL2OfComponents hzero hFvec := by
    apply Lp.ext
    filter_upwards [coeFn_hilbertBlockL2ToBlockL2 (F := projectedSourceLoad Q hF),
      (ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn U)
        (L := hilbertPureSecond.toContinuousLinearMap)
        (f := toHilbertVectorL2OfVecField hFvec)),
      coeFn_toHilbertVectorL2OfVecField hFvec,
      coeFn_toBlockL2OfComponents hzero hFvec] with x htransport hpure hvec hcomponents
    rw [htransport, hcomponents]
    change (hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hFvec) x).toBlockVec = _
    have hpure' : hilbertPureSecondL2 U (toHilbertVectorL2OfVecField hFvec) x =
        hilbertPureSecond.toContinuousLinearMap (hilbertifyVecField F x) := by
      simpa [hilbertPureSecondL2, hvec] using hpure
    rw [hpure']
    simp [hilbertPureSecond, blockField, HilbertBlockVec.toBlockVec, hilbertifyVecField]
  apply (continuousLinearEquivBlockL2 (U := U)).symm.injective
  calc
    hilbertBlockL2ToBlockL2 (projectedSourceLoad Q hF) =
        toBlockL2OfComponents hzero hFvec := hblock
    _ = hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfComponents hzero hFvec) := by
      symm
      exact PotentialSolenoidalL2Data.hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents
        (U := U) hzero hFvec

/-- The exact component removed from the pure-flux load by the scalar
projection is represented by the canonical zero-trace/zero-normal correction
field. -/
theorem projectedSource_removedCorrection_exists (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    ∃ corr : CorrectionFieldData (openCubeSet Q),
      corr.toHilbertBlockL2 = projectedSourceLoad Q hF -
        scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF) := by
  let U := openCubeSet Q
  let hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  let H := projectedSourceLoad Q hF
  let R := scalarProjectionResidual Q ν σ hν hσ k H
  let rem : HilbertBlockL2 U := H - R
  have hrem : rem ∈ (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace := by
    change H - scalarProjectionResidual Q ν σ hν hσ k H ∈ _
    exact scalar_projection_removed_mem Q ν σ hν hσ k H
  let recData : PotentialSolenoidalL2RecoveryData U := lemmaVRecoveryData hU
  let muData := recData.toMuCorrectionSpaceRecoveryData
  have hrem' : rem ∈ muData.correctionSpace.toSubmodule := by
    change hilbertBlockL2ToBlockL2 rem ∈
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).blockPotentialZeroTraceSolenoidalZeroNormalTrace
    simpa [muData, recData, lemmaVRecoveryData, scalar_frame_correction_space] using hrem
  let rem' : muData.correctionSpace.toSubmodule := ⟨rem, hrem'⟩
  let corr := muData.repr rem'
  have hcorr : corr.toHilbertBlockL2 = rem := by
    simpa [rem'] using muData.repr_eq rem'
  refine ⟨corr, ?_⟩
  simpa [H, R, rem] using hcorr

/-- Pointwise, the removed correction is the pure-flux load minus its actual
projected residual. -/
theorem projectedSource_removedCorrectionField_exists (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    ∃ corr : CorrectionFieldData (openCubeSet Q),
      corr.toBlockField =ᵐ[volumeMeasureOn (openCubeSet Q)]
        fun x => (0, F x) - projectedSourceField Q ν σ hν hσ k hF x := by
  let U := openCubeSet Q
  let H := projectedSourceLoad Q hF
  let R := scalarProjectionResidual Q ν σ hν hσ k H
  obtain ⟨corr, hcorr⟩ := projectedSource_removedCorrection_exists Q ν σ hν hσ k hF
  have hcorr' : corr.toBlockL2 = hilbertBlockL2ToBlockL2 (H - R) := by
    calc
      corr.toBlockL2 = hilbertBlockL2ToBlockL2 corr.toHilbertBlockL2 := by
        have h := congrArg hilbertBlockL2ToBlockL2 corr.blockL2ToHilbertBlockL2_toBlockL2
        simpa only [hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2] using h
      _ = hilbertBlockL2ToBlockL2 (H - R) := by rw [hcorr]
  rw [map_sub] at hcorr'
  have hfieldClass := MeasureTheory.Lp.ext_iff.mp hcorr'
  have hsubAE := MeasureTheory.Lp.coeFn_sub
    (hilbertBlockL2ToBlockL2 H) (hilbertBlockL2ToBlockL2 R)
  let hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  let hzero : MemVectorL2 U (0 : Vec 2 → Vec 2) := MemLp.zero
  have hload := projectedSourceLoad_eq_components Q hF
  have hloadClass : hilbertBlockL2ToBlockL2 H = toBlockL2OfComponents hzero hFvec := by
    calc
      hilbertBlockL2ToBlockL2 H =
          hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfComponents hzero hFvec) :=
        congrArg hilbertBlockL2ToBlockL2 hload
      _ = toBlockL2OfComponents hzero hFvec :=
        PotentialSolenoidalL2Data.hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents
          (U := U) hzero hFvec
  have hloadAE := MeasureTheory.Lp.ext_iff.mp hloadClass
  have hcomponentsAE := coeFn_toBlockL2OfComponents hzero hFvec
  have hZ : hilbertBlockL2ToBlockL2 R = projectedSourceField Q ν σ hν hσ k hF := rfl
  refine ⟨corr, ?_⟩
  filter_upwards [coeFn_toBlockL2 corr.memBlockL2_toBlockField,
    hfieldClass, hsubAE, hloadAE, hcomponentsAE] with x hcorrField hfield hsub hloadField hcomponents
  calc
    corr.toBlockField x = corr.toBlockL2 x := hcorrField.symm
    _ = (hilbertBlockL2ToBlockL2 H - hilbertBlockL2ToBlockL2 R) x := hfield
    _ = (hilbertBlockL2ToBlockL2 H) x - (hilbertBlockL2ToBlockL2 R) x := hsub
    _ = (toBlockL2OfComponents hzero hFvec) x - projectedSourceField Q ν σ hν hσ k hF x := by
      rw [hloadField, hZ]
    _ = (0, F x) - projectedSourceField Q ν σ hν hσ k hF x := by
      rw [hcomponents]
      simp [blockField]

private theorem integral_cell_of_parent_zeroNormal
    {Q R : TriadicCube 2} (hRQ : openCubeSet R ⊆ openCubeSet Q)
    {f : Vec 2 → Vec 2}
    (hf : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) f)
    (u : H10Function (openCubeSet R)) :
    ∫ x in openCubeSet R, vecDot (f x) (u.toH1Function.grad x) ∂volume = 0 := by
  let U := openCubeSet Q
  let V := openCubeSet R
  let uExt := u.extendByZeroToOpenSuperset (measurableSet_openCubeSet R)
    (isOpen_openCubeSet Q) hRQ
  have hgrad : uExt.toH1Function.grad = V.indicator u.toH1Function.grad := by
    rw [H10Function.extendByZeroToOpenSuperset_grad]
    rfl
  have hpoint : (fun x => vecDot (f x) (uExt.toH1Function.grad x)) =
      V.indicator (fun x => vecDot (f x) (u.toH1Function.grad x)) := by
    funext x
    by_cases hx : x ∈ V
    · simp [hgrad, hx, vecDot]
    · simp [hgrad, hx, vecDot]
  have hzero : ∫ x in U, vecDot (f x) (uExt.toH1Function.grad x) ∂volume = 0 :=
    hf uExt.toH1Function
  rw [hpoint, integral_indicator (measurableSet_openCubeSet R),
    Measure.restrict_restrict (measurableSet_openCubeSet R),
    Set.inter_eq_left.mpr hRQ] at hzero
  exact hzero

/-- The literal projected-source correction has an actual zero-boundary first
potential. The residual itself has its negative gradient in that coordinate. -/
theorem projectedSource_firstPotential_exists (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q)) :
    ∃ v : H10Function (openCubeSet Q),
      (fun x => (projectedSourceField Q ν σ hν hσ k hF x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)]
        v.toH1Function.grad := by
  let U := openCubeSet Q
  let hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  let H := projectedSourceLoad Q hF
  let R := scalarProjectionResidual Q ν σ hν hσ k H
  let rem : HilbertBlockL2 U := H - R
  have hrem : rem ∈ (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace := by
    change H - scalarProjectionResidual Q ν σ hν hσ k H ∈ _
    exact scalar_projection_removed_mem Q ν σ hν hσ k H
  let recData : PotentialSolenoidalL2RecoveryData U := lemmaVRecoveryData hU
  let muData := recData.toMuCorrectionSpaceRecoveryData
  have hrem' : rem ∈ muData.correctionSpace.toSubmodule := by
    change hilbertBlockL2ToBlockL2 rem ∈
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).blockPotentialZeroTraceSolenoidalZeroNormalTrace
    simpa [muData, recData, lemmaVRecoveryData, scalar_frame_correction_space] using hrem
  let rem' : muData.correctionSpace.toSubmodule := ⟨rem, hrem'⟩
  let corr := muData.repr rem'
  have hcorr : corr.toHilbertBlockL2 = rem := by
    simpa [rem'] using muData.repr_eq rem'
  obtain ⟨v₀, hv₀⟩ := corr.isPotentialZeroTrace
  have hdataField : corr.toBlockField =ᵐ[volumeMeasureOn U]
      fun x => hilbertBlockL2ToBlockL2 H x - hilbertBlockL2ToBlockL2 R x := by
    have hcorr' : corr.toBlockL2 = hilbertBlockL2ToBlockL2 rem := by
      calc
        corr.toBlockL2 = hilbertBlockL2ToBlockL2 corr.toHilbertBlockL2 := by
          have h := congrArg hilbertBlockL2ToBlockL2 corr.blockL2ToHilbertBlockL2_toBlockL2
          simpa only [hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2] using h
        _ = hilbertBlockL2ToBlockL2 rem := by rw [hcorr]
    have hremfield : hilbertBlockL2ToBlockL2 rem =
        hilbertBlockL2ToBlockL2 H - hilbertBlockL2ToBlockL2 R := by
      simp [rem, map_sub]
    have hfieldClass := hcorr'.trans hremfield
    have hfieldAE := MeasureTheory.Lp.ext_iff.mp hfieldClass
    have hsubAE := MeasureTheory.Lp.coeFn_sub
      (hilbertBlockL2ToBlockL2 H) (hilbertBlockL2ToBlockL2 R)
    filter_upwards [coeFn_toBlockL2 corr.memBlockL2_toBlockField, hfieldAE, hsubAE]
      with x hx hEq hsub
    calc
      corr.toBlockField x = corr.toBlockL2 x := hx.symm
      _ = (hilbertBlockL2ToBlockL2 H - hilbertBlockL2ToBlockL2 R) x := hEq
      _ = hilbertBlockL2ToBlockL2 H x - hilbertBlockL2ToBlockL2 R x := hsub
  have hsourceFirst : (fun x => (hilbertBlockL2ToBlockL2 H x).1) =ᵐ[volumeMeasureOn U]
      fun _ => 0 := by
    let hFvec : MemVectorL2 U F :=
      memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
    let hzero : MemVectorL2 U (0 : Vec 2 → Vec 2) := MemLp.zero
    have hcomponents := projectedSourceLoad_eq_components Q hF
    have hclass : hilbertBlockL2ToBlockL2 H = toBlockL2OfComponents hzero hFvec := by
      calc
        hilbertBlockL2ToBlockL2 H =
            hilbertBlockL2ToBlockL2 (toHilbertBlockL2OfComponents hzero hFvec) :=
          congrArg hilbertBlockL2ToBlockL2 hcomponents
        _ = toBlockL2OfComponents hzero hFvec :=
          PotentialSolenoidalL2Data.hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents
            (U := U) hzero hFvec
    have hAE := MeasureTheory.Lp.ext_iff.mp hclass
    have hcomponentsAE := coeFn_toBlockL2OfComponents hzero hFvec
    filter_upwards [hAE, hcomponentsAE] with x hx hc
    have hx' := congrArg Prod.fst hx
    rw [hc] at hx'
    simpa [blockField] using hx'
  have hpot : corr.potential =ᵐ[volumeMeasureOn U]
      fun x => -(projectedSourceField Q ν σ hν hσ k hF x).1 := by
    filter_upwards [hdataField, hsourceFirst] with x hx hs
    have hfirst := congrArg Prod.fst hx
    have hfirst' : corr.potential x =
        (hilbertBlockL2ToBlockL2 H x).1 - (hilbertBlockL2ToBlockL2 R x).1 := by
      simpa [CorrectionFieldData.toBlockField, Pi.sub_apply, Prod.fst_sub] using hfirst
    rw [hs] at hfirst'
    have hRfield : hilbertBlockL2ToBlockL2 R = projectedSourceField Q ν σ hν hσ k hF := rfl
    rw [hRfield] at hfirst'
    simpa using hfirst'
  have hgrad : (fun x => (projectedSourceField Q ν σ hν hσ k hF x).1) =ᵐ[volumeMeasureOn U]
      fun x => -v₀.toH1Function.grad x := by
    filter_upwards [hpot] with x hx
    have hneg := congrArg (fun w : Vec 2 => -w) hx
    simpa [hv₀] using hneg.symm
  refine ⟨-v₀, ?_⟩
  have hneg : (-v₀).toH1Function = -v₀.toH1Function := rfl
  filter_upwards [hgrad] with x hx
  simpa [hneg]

/-- On each descendant, the reflected pure-flux projection satisfies the
literal forced weak response equation. The source term is the load paired
with the test potential. -/
theorem projectedSource_forcedResponse_onDescendant
    (Q : TriadicCube 2) (j : ℕ)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j)
    (T : BlockState 2)
    (hT : ScalarVariation (openCubeSet R) (fun x => T.eval x)) :
    ∫ x in openCubeSet R,
      blockPairingIntegrand (responseFramePlanarCoefficientField ν σ k) T
        (projectedSourceCompatibleState Q ν σ hν hσ k hF) x ∂volume =
      ∫ x in openCubeSet R, vecDot (T.potential x) (F x) ∂volume := by
  let U := openCubeSet Q
  let V := openCubeSet R
  let a := responseFramePlanarCoefficientField ν σ k
  let Z := projectedSourceField Q ν σ hν hσ k hF
  let W : BlockState 2 := ⟨fun x => (Z x).1, fun x => (Z x).2⟩
  let Y := projectedSourceCompatibleState Q ν σ hν hσ k hF
  have hRQ : V ⊆ U := openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hEll : IsEllipticFieldOn (ν / σ)
      (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) U a := by
    simpa [a, U] using responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) ν σ hν hσ k
  obtain ⟨v, hv⟩ := projectedSource_firstPotential_exists Q ν σ hν hσ k hF
  obtain ⟨corr, hcorr⟩ := projectedSource_removedCorrectionField_exists Q ν σ hν hσ k hF
  obtain ⟨ψ, hψ⟩ := hT.2.1
  have hfluxEq : W.flux =ᵐ[volumeMeasureOn V] fun x => F x - corr.flux x := by
    have hcorrLocal := ae_restrict_of_ae_restrict_of_subset hRQ hcorr
    filter_upwards [hcorrLocal] with x hx
    have hs := congrArg Prod.snd hx
    have hs' : corr.flux x = F x - (Z x).2 := by
      simpa [CorrectionFieldData.toBlockField, blockField] using hs
    calc
      W.flux x = (Z x).2 := rfl
      _ = F x - corr.flux x := by rw [hs']; abel
  have hvLocal : W.potential =ᵐ[volumeMeasureOn V] v.toH1Function.grad := by
    have hv' := ae_restrict_of_ae_restrict_of_subset hRQ hv
    change (fun x => (Z x).1) =ᵐ[volume.restrict V] v.toH1Function.grad
    exact hv'
  have hcorrZero := integral_cell_of_parent_zeroNormal hRQ
    corr.isSolenoidalZeroNormalTrace ψ
  have hcorrZero' :
      ∫ x in V, vecDot (T.potential x) (corr.flux x) ∂volume = 0 := by
    calc
      _ = ∫ x in V, vecDot (corr.flux x) (ψ.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hψ]
        exact vecDot_comm _ _
      _ = 0 := hcorrZero
  let vR := v.toH1Function.restrictToOpenSubcube hR
  have hsecondZero := hT.2.2 vR
  have hsecondZero' :
      ∫ x in V, vecDot (T.flux x) (W.potential x) ∂volume = 0 := by
    calc
      _ = ∫ x in V, vecDot (T.flux x) (v.toH1Function.grad x) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hvLocal] with x hx
        exact congrArg (vecDot (T.flux x)) hx
      _ = 0 := by simpa [vR, H1Function.restrictToOpenSubcube_grad, BlockState.eval] using hsecondZero
  let hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hFmem : MemVectorL2 V F :=
    hFvec.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hTpotMem : MemVectorL2 V T.potential :=
    memVectorL2_fst_of_memBlockL2 hT.1
  have hTfluxMem : MemVectorL2 V T.flux :=
    memVectorL2_snd_of_memBlockL2 hT.1
  have hCorrFluxMem : MemVectorL2 V corr.flux :=
    corr.flux_memL2.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hZmem : MemBlockL2 U (fun x => Z x) := Lp.memLp Z
  have hWpotMem : MemVectorL2 V W.potential := by
    have h := memVectorL2_fst_of_memBlockL2 hZmem
    exact h.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hWfluxMem : MemVectorL2 V W.flux := by
    have h := memVectorL2_snd_of_memBlockL2 hZmem
    exact h.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hIntF := integrableOn_vecDot_of_memVectorL2 hTpotMem hFmem
  have hIntCorr := integrableOn_vecDot_of_memVectorL2 hTpotMem hCorrFluxMem
  have hIntW := integrableOn_vecDot_of_memVectorL2 hTpotMem hWfluxMem
  have hfirst :
      ∫ x in V, vecDot (T.potential x) (W.flux x) ∂volume =
        ∫ x in V, vecDot (T.potential x) (F x) ∂volume := by
    calc
      _ = ∫ x in V,
          (vecDot (T.potential x) (F x) - vecDot (T.potential x) (corr.flux x)) ∂volume := by
        apply integral_congr_ae
        filter_upwards [hfluxEq] with x hx
        rw [hx]
        simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
      _ = (∫ x in V, vecDot (T.potential x) (F x) ∂volume) -
          ∫ x in V, vecDot (T.potential x) (corr.flux x) ∂volume :=
        integral_sub hIntF hIntCorr
      _ = _ := by rw [hcorrZero']; ring
  have hIntSecond := integrableOn_vecDot_of_memVectorL2 hTfluxMem hWpotMem
  have hsplit :
      ∫ x in V, blockPairingIntegrand a T Y x ∂volume =
        ∫ x in V,
          (vecDot (T.potential x) (W.flux x) + vecDot (T.flux x) (W.potential x)) ∂volume := by
    apply setIntegral_congr_fun (measurableSet_openCubeSet R)
    intro x hx
    have hxU : x ∈ U := hRQ hx
    have hAct : blockMatVecMul (blockCoeffField a x) (Y.eval x) = (W.eval x).swap := by
      simpa [Y, projectedSourceCompatibleState, Z, a, U, W] using
        pairedReflectState_action hEll W hxU
    change blockVecDot (T.eval x)
      (blockMatVecMul (blockCoeffField a x) (Y.eval x)) = _
    rw [hAct]
    simp [BlockState.eval, blockVecDot, vecDot]
  calc
    _ = ∫ x in V,
        (vecDot (T.potential x) (W.flux x) + vecDot (T.flux x) (W.potential x)) ∂volume := hsplit
    _ = (∫ x in V, vecDot (T.potential x) (W.flux x) ∂volume) +
        ∫ x in V, vecDot (T.flux x) (W.potential x) ∂volume :=
      integral_add hIntW hIntSecond
    _ = ∫ x in V, vecDot (T.potential x) (F x) ∂volume := by rw [hfirst, hsecondZero']; ring

private theorem forcedSource_bottomMode_weakEnergy_le_finite (Q : TriadicCube 2)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q))]
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (e : Vec 2) :
    vectorWeakHaarEnergy Q
        (fun x i => ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i) ≤
      (lemmaVInverseHistory Q a (Real.sqrt 3) -
        (1 - (Real.sqrt 3)⁻¹) * lemmaVInverseDepthMax Q a 0) *
        vecDot e (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight e) := by
  let U := openCubeSet Q
  let q : ℝ := Real.sqrt 3
  let w : ℝ := q⁻¹
  let M : ℕ → ℝ := lemmaVInverseDepthMax Q a
  let H : ℝ := lemmaVInverseHistory Q a q
  let F := (pairedBesselOpenCubeFamilyData hEll).family
  let S := F.field (0, e)
  let D : Mat 2 := (coarseBlockMatrix U a).lowerRight
  let E : ℝ := vecDot e (matVecMul D e)
  have hq : 1 < q := by
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hw : 0 ≤ w := inv_nonneg.mpr (by positivity)
  have hw1 : 0 ≤ 1 - w := by
    have hlt : w < 1 := (inv_lt_one₀ (by positivity)).2 hq
    linarith
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let Adm := F.admissible (0, e)
  have hSmem : MemBlockL2 U S.eval := by simpa [S, F] using Adm.memBlockL2_eval
  have hSpot : MemVectorL2 U S.potential := memVectorL2_fst_of_memBlockL2 hSmem
  have hSflux : MemVectorL2 U S.flux := memVectorL2_snd_of_memBlockL2 hSmem
  have hSzeroTrace : IsPotentialZeroTraceOn U S.potential := by
    simpa [S] using Adm.isPotentialZeroTrace
  have hSpotential : IsBlockPotentialOn U S := by
    change IsPotentialOn U S.potential
    exact hSzeroTrace.isPotentialOn
  have hSsolenoidal : IsBlockSolenoidalOn U S := by
    have hzeroMem : MemVectorL2 U (fun x => S.flux x - e) := by
      simpa [S] using Adm.fluxCorrection_memL2
    have hconstMem : MemVectorL2 U (fun _ : Vec 2 => e) :=
      MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := e)
    have hzeroSol : IsSolenoidalOn U (fun x => S.flux x - e) := by
      exact Adm.isSolenoidalZeroNormalTrace.isSolenoidalOn
    have hconstSol : IsSolenoidalOn U (fun _ : Vec 2 => e) :=
      IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain
        (isOpenBoundedConvexDomain_openCubeSet Q).isSobolevRegularDomain hvol.ne' e
    have hsum := isSolenoidalOn_add_of_memVectorL2 hzeroMem hconstMem hzeroSol hconstSol
    have hEq : (fun x => (S.flux x - e) + e) = S.flux := by
      funext x
      exact sub_add_cancel _ _
    change IsSolenoidalOn U S.flux
    rw [← hEq]
    exact hsum
  have hE : blockPairingAverage U a S S = E := by
    have hpair := linearMuMinimizerFamily_pairing_eq_coarse F (0, e) (0, e)
    simpa [S, E, D, blockVecDot, blockMatVecMul, vecDot, matVecMul_zero] using hpair
  have hE_nonneg : 0 ≤ E := by
    have := compatible_blockPairingAverage_nonneg hEll S
    rw [hE] at this
    exact this
  have hmeanS : pairedPotentialMean U S = 0 :=
    pureBottom_potentialMean_eq_zero hvol.ne' F e
  have hmean (i : Fin 2) : cubeAverage Q (fun x => S.potential x i) = 0 := by
    have hi := congrFun hmeanS i
    change volumeAverage U (fun x => S.potential x i) = 0 at hi
    calc
      cubeAverage Q (fun x => S.potential x i) =
          volumeAverage U (fun x => S.potential x i) := by
        rw [cubeAverage_eq_integralAverage_openCubeSet Q]
        rfl
      _ = 0 := hi
  have hroot : (∑ i : Fin 2,
      energy Q (cubeProjection Q 0 (fun x => S.potential x i))) = 0 := by
    rw [Fin.sum_univ_two]
    rw [energy_projection_zero, energy_projection_zero, hmean 0, hmean 1]
    norm_num
  have hproj (k : ℕ) :
      (∑ i : Fin 2, energy Q (cubeProjection Q k (fun x => S.potential x i))) ≤ M k * E := by
    have h := compatible_projectionEnergy_bound hEll S hSpotential hSsolenoidal hSmem k
    have havg : cubeAverage Q (blockPairingIntegrand a S S) = E := by
      rw [cubeAverage_eq_integralAverage_openCubeSet Q]
      exact hE
    simpa [M, E, compatibleInverseHistory, blockPairingAverage, havg] using h
  have hsCoord (i : Fin 2) : Summable (fun k : ℕ => w ^ k *
      energy Q (cubeProjection Q k (fun x => S.potential x i))) :=
    summable_weighted_projections Q hq (memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 hSpot i))
  have hsSum : Summable (fun k : ℕ => w ^ k *
      (∑ i : Fin 2, energy Q (cubeProjection Q k (fun x => S.potential x i)))) := by
    simpa only [Finset.mul_sum] using summable_sum fun i _ => hsCoord i
  have hEq : vectorWeakHaarEnergy Q (fun x i => S.potential x i) =
      (1 - w) * ∑' k : ℕ, w ^ k *
        (∑ i : Fin 2, energy Q (cubeProjection Q k (fun x => S.potential x i))) := by
    have hcoord (i : Fin 2) : MemLp (fun x => S.potential x i) 2
        (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hSpot i)
    unfold vectorWeakHaarEnergy
    calc
      (∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => S.potential x i)) =
          ∑ i : Fin 2, (1 - w) * ∑' k : ℕ, w ^ k *
            energy Q (cubeProjection Q k (fun x => S.potential x i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [w, q] using dualEnergy_eq Q hq (hcoord i)
      _ = (1 - w) * ∑' k : ℕ, w ^ k *
          (∑ i : Fin 2, energy Q (cubeProjection Q k (fun x => S.potential x i))) := by
          rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ => hsCoord i)]
          congr 1
          exact tsum_congr fun k => (Finset.mul_sum _ _ _).symm
  have htail : (∑' k : ℕ, w ^ k *
      (∑ i : Fin 2, energy Q (cubeProjection Q k (fun x => S.potential x i)))) =
      ∑' k : ℕ, w ^ (k + 1) *
        (∑ i : Fin 2, energy Q (cubeProjection Q (k + 1) (fun x => S.potential x i))) := by
    have hzeroadd := hsSum.tsum_eq_zero_add
    simp only [pow_zero, one_mul, hroot, zero_add] at hzeroadd
    exact hzeroadd
  have hhist := lemmaVInverseHistory_summable Q hEll hq
  have hsM : Summable (fun k : ℕ => w ^ (k + 1) * M (k + 1)) := by
    simpa only [Nat.add_comm 1] using (summable_nat_add_iff 1).2 hhist
  have hsTail : Summable (fun k : ℕ => w ^ (k + 1) *
      (∑ i : Fin 2, energy Q (cubeProjection Q (k + 1) (fun x => S.potential x i)))) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff 1).2 hsSum
  have hsMmul : Summable (fun k : ℕ => w ^ (k + 1) * (M (k + 1) * E)) := by
    convert hsM.mul_right E using 1
    ext k
    ring
  have hbound : (∑' k : ℕ, w ^ (k + 1) *
      (∑ i : Fin 2, energy Q (cubeProjection Q (k + 1) (fun x => S.potential x i)))) ≤
      (∑' k : ℕ, w ^ (k + 1) * M (k + 1)) * E := by
    calc
      _ ≤ ∑' k : ℕ, w ^ (k + 1) * (M (k + 1) * E) :=
        hsTail.tsum_le_tsum (fun k =>
          mul_le_mul_of_nonneg_left (hproj (k + 1)) (pow_nonneg hw _)) hsMmul
      _ = _ := by
        calc
          _ = ∑' k : ℕ, (w ^ (k + 1) * M (k + 1)) * E :=
            tsum_congr fun k => by ring
          _ = _ := tsum_mul_right
  have hhistoryTail :
      H - (1 - w) * M 0 = (1 - w) * (∑' k : ℕ, w ^ (k + 1) * M (k + 1)) := by
    have hsum0 : (∑' k : ℕ, w ^ k * M k) =
        M 0 + ∑' k : ℕ, w ^ (k + 1) * M (k + 1) := by
      simpa only [pow_zero, one_mul] using hhist.tsum_eq_zero_add
    dsimp [H, lemmaVInverseHistory]
    rw [hsum0]
    ring
  calc
    vectorWeakHaarEnergy Q (fun x i => S.potential x i) =
        (1 - w) * ∑' k : ℕ, w ^ (k + 1) *
          (∑ i : Fin 2, energy Q (cubeProjection Q (k + 1) (fun x => S.potential x i))) := by
            rw [hEq, htail]
    _ ≤ (1 - w) * ((∑' k : ℕ, w ^ (k + 1) * M (k + 1)) * E) :=
          mul_le_mul_of_nonneg_left hbound hw1
    _ = (H - (1 - w) * M 0) * E := by
          calc
            _ = ((1 - w) * (∑' k : ℕ, w ^ (k + 1) * M (k + 1))) * E := by ring
            _ = _ := by rw [← hhistoryTail]

private theorem forcedSource_bottomMode_weakEnergy_le (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (e : Vec 2) :
    vectorWeakHaarEnergy Q
        (fun x i => ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i) ≤
      (lemmaVInverseHistory Q a (Real.sqrt 3) -
        (1 - (Real.sqrt 3)⁻¹) * lemmaVInverseDepthMax Q a 0) *
        vecDot e (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight e) := by
  exact @forcedSource_bottomMode_weakEnergy_le_finite Q
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
    a lam Lam hEll e

theorem forcedSource_sourcePairing_le_circle_mul_weak (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ i : Fin 2, Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => F x i))))
    (e : Vec 2) :
    |vecDot e (pairedBesselSourceCorrectionVector hEll F)| ≤
      Real.sqrt (forcedSourceCircleEnergy Q F) * Real.sqrt
        (vectorWeakHaarEnergy Q (fun x i =>
          ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i)) := by
  letI forcedSourcePairingFiniteMeasure : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let Fam := (pairedBesselOpenCubeFamilyData hEll).family
  let phi : Vec 2 → Vec 2 := fun x => (Fam.field (0, e)).potential x
  let F0 : Vec 2 → Vec 2 := fun x i => F x i - cubeAverage Q (fun y => F y i)
  have hFvec : MemVectorL2 (openCubeSet Q) F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hFcoord (i : Fin 2) : MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hFvec i)
  have hPhiMemBlock : MemBlockL2 (openCubeSet Q) (Fam.field (0, e)).eval :=
    (Fam.admissible (0, e)).memBlockL2_eval
  have hPhivec : MemVectorL2 (openCubeSet Q) phi := by
    change MemVectorL2 (openCubeSet Q) (Fam.field (0, e)).potential
    exact memVectorL2_fst_of_memBlockL2 hPhiMemBlock
  have hPhiCoord (i : Fin 2) : MemLp (fun x => phi x i) 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hPhivec i)
  have hvol : 0 < (MeasureTheory.volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hPhiMean : pairedPotentialMean (openCubeSet Q) (Fam.field (0, e)) = 0 :=
    pureBottom_potentialMean_eq_zero hvol.ne' Fam e
  have hPhiMeanCoord (i : Fin 2) : cubeAverage Q (fun x => phi x i) = 0 := by
    have hi := congrFun hPhiMean i
    change volumeAverage (openCubeSet Q) (fun x => phi x i) = 0 at hi
    calc
      cubeAverage Q (fun x => phi x i) =
          volumeAverage (openCubeSet Q) (fun x => phi x i) := by
        rw [cubeAverage_eq_integralAverage_openCubeSet Q]
        rfl
      _ = 0 := hi
  have hF0coord (i : Fin 2) : MemLp (fun x => F0 x i) 2 (normalizedCubeMeasure Q) :=
    (hFcoord i).sub (memLp_const _)
  have hF0positive (i : Fin 2) : Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => F0 x i))) := by
    change Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1)
        (fun x => F x i - cubeAverage Q (fun y => F y i))))
    convert hFpos i using 1
    funext k
    rw [diagIncrement_succ_sub_const Q k (hFcoord i)
      (cubeAverage Q (fun y => F y i))]
  have hCircle : vectorPositiveHaarEnergy Q F0 = forcedSourceCircleEnergy Q F := by
    unfold vectorPositiveHaarEnergy forcedSourceCircleEnergy
    apply Finset.sum_congr rfl
    intro i hi
    have hmean : cubeAverage Q (fun x => F0 x i) = 0 := by
      change cubeAverage Q (fun x => F x i - cubeAverage Q (fun y => F y i)) = 0
      rw [cubeAverage_sub_const_of_memLp_two Q (hFcoord i)]
      ring
    unfold primalEnergy
    simp only [cubeIncrement_zero, energy_projection_zero, hmean,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
    exact tsum_congr fun k => by
      rw [diagIncrement_succ_sub_const Q k (hFcoord i)
        (cubeAverage Q (fun y => F y i))]
  have hpairCenter (i : Fin 2) :
      pairing Q (fun x => F0 x i) (fun x => phi x i) =
        pairing Q (fun x => F x i) (fun x => phi x i) := by
    change pairing Q (fun x => F x i - cubeAverage Q (fun y => F y i))
        (fun x => phi x i) = _
    rw [pairing_sub_left Q (hFcoord i) (memLp_const _) (hPhiCoord i)]
    rw [pairing_comm Q (fun _ => cubeAverage Q (fun y => F y i)) _,
      pairing_const_right, hPhiMeanCoord i]
    ring
  have hpairing : vectorPairing Q F0 phi =
      cubeAverage Q (fun x => vecDot (F x) (phi x)) := by
    calc
      vectorPairing Q F0 phi = vectorPairing Q F phi := by
        unfold vectorPairing
        exact Finset.sum_congr rfl (fun i _ => hpairCenter i)
      _ = cubeAverage Q (fun x => vecDot (F x) (phi x)) :=
        (lemmaV_cubeAverage_vecDot_eq_vectorPairing Q
          (fun i => hFcoord i) (fun i => hPhiCoord i)).symm
  have hsource := pairedBessel_sourcePairing_eq_dot hEll hFvec e
  have hsourceCube : vecDot e (pairedBesselSourceCorrectionVector hEll F) =
      cubeAverage Q (fun x => vecDot (F x) (phi x)) := by
    calc
      vecDot e (pairedBesselSourceCorrectionVector hEll F) =
          volumeAverage (openCubeSet Q) (fun x => vecDot (F x) (phi x)) := by
        exact hsource.symm
      _ = cubeAverage Q (fun x => vecDot (F x) (phi x)) := by
        rw [cubeAverage_eq_integralAverage_openCubeSet Q]
        rfl
  have hdual := abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
    Q (fun i => hF0coord i) (fun i => hPhiCoord i) hF0positive
  have hdual' : |vecDot e (pairedBesselSourceCorrectionVector hEll F)| ≤
      Real.sqrt (forcedSourceCircleEnergy Q F) * Real.sqrt
        (vectorWeakHaarEnergy Q phi) := by
    calc
      |vecDot e (pairedBesselSourceCorrectionVector hEll F)| =
          |vectorPairing Q F0 phi| := by
            exact congrArg abs (hsourceCube.trans hpairing.symm)
      _ ≤ vectorPositiveHaarNorm Q F0 * vectorWeakHaarNorm Q phi := hdual
      _ = _ := by simp [vectorPositiveHaarNorm, vectorWeakHaarNorm, hCircle, phi]
  exact hdual'

theorem forcedSource_sourceShift_norm_le (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ i : Fin 2, Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => F x i)))) :
    vecNormSq (pairedBesselSourceCorrectionVector hEll F) ≤
      (Real.sqrt 3)⁻¹ *
        (lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))) ^ 2 *
          forcedSourceCircleEnergy Q F := by
  let q : ℝ := Real.sqrt 3
  let w : ℝ := q⁻¹
  let H : ℝ := lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))
  let H0 : ℝ := lemmaVInverseHistory Q a q
  let D : Mat 2 := (coarseBlockMatrix (openCubeSet Q) a).lowerRight
  let t : Vec 2 := pairedBesselSourceCorrectionVector hEll F
  let e : Vec 2 := matVecMul D⁻¹ t
  letI forcedSourceShiftFiniteMeasure : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hq : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hw : 0 < w := by dsimp [w]; positivity
  have hwle : 1 / 2 ≤ w := by
    have hqle2 : q ≤ 2 := by
      have hs : q ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith [sq_nonneg (q - 2)]
    have hi := (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hqpos).2 hqle2
    norm_num at hi ⊢
    exact hi
  have hH0le : H0 ≤ H := by
    have hq₂ : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
      Real.one_lt_rpow (by norm_num) (by norm_num)
    have hqcomp : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ q := by
      calc
        (3 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = q := by dsimp [q]; exact (Real.sqrt_eq_rpow 3).symm
    have hinv : q⁻¹ ≤ ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hqcomp
    dsimp [H0, H]
    exact lemmaVInverseHistory_le_of_inverse_discount Q hEll hq hq₂ hinv
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    exact lemmaVInverseHistory_nonneg Q a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hH0nonneg : 0 ≤ H0 := by
    dsimp [H0]
    exact lemmaVInverseHistory_nonneg Q a hq
  have hvol : 0 < (MeasureTheory.volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨_, hCoarse, _, _, _, _, hDpos, _⟩ :=
    exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  have hD : D.PosDef := by
    change (coarseBlockMatrix (openCubeSet Q) a).lowerRight.PosDef
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hDinv : D⁻¹.PosDef := hD.inv
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hDleft : ∀ ξ : Vec 2, matVecMul D (matVecMul D⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hDdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hmetricNonneg : 0 ≤ vecDot t (matVecMul D⁻¹ t) := by
    by_cases ht : t = 0
    · simp [t, ht, matVecMul_zero, vecDot_zero_left]
    · have hp := hDinv.dotProduct_mulVec_pos ht
      exact le_of_lt (by simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hp)
  have hsource := forcedSource_sourcePairing_le_circle_mul_weak Q hEll hF hFpos e
  have hsourceSq : (vecDot e t) ^ 2 ≤ forcedSourceCircleEnergy Q F *
      vectorWeakHaarEnergy Q (fun x i =>
        ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i) := by
    have hnonneg : 0 ≤ Real.sqrt (forcedSourceCircleEnergy Q F) * Real.sqrt
        (vectorWeakHaarEnergy Q (fun x i =>
          ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have habs := (abs_le.mp hsource).2
    have hprod : (Real.sqrt (forcedSourceCircleEnergy Q F) * Real.sqrt
        (vectorWeakHaarEnergy Q (fun x i =>
          ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i))) ^ 2 =
        forcedSourceCircleEnergy Q F * vectorWeakHaarEnergy Q (fun x i =>
          ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i) := by
      rw [mul_pow, Real.sq_sqrt (forcedSourceCircleEnergy_nonneg Q F),
        Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q _)]
    have hsource' : |vecDot e t| ≤ Real.sqrt (forcedSourceCircleEnergy Q F) *
        Real.sqrt (vectorWeakHaarEnergy Q (fun x i =>
          ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i)) := by
      simpa [t] using hsource
    have hsquare : |vecDot e t| ^ 2 ≤
        (Real.sqrt (forcedSourceCircleEnergy Q F) * Real.sqrt
          (vectorWeakHaarEnergy Q (fun x i =>
            ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i))) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hsource'
    rw [sq_abs, hprod] at hsquare
    exact hsquare
  have hbottom := forcedSource_bottomMode_weakEnergy_le Q hEll e
  have hDE : vecDot e (matVecMul D e) = vecDot t (matVecMul D⁻¹ t) := by
    dsimp [e]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hDdet]
    have hId : matVecMul (1 : Mat 2) t = t := by
      funext i
      simp [matVecMul, Matrix.one_apply]
    rw [hId]
    exact vecDot_comm _ _
  let b : ℝ := Book.Ch02.matrixNorm D
  have hbnonneg : 0 ≤ b := by dsimp [b]; exact Book.Ch02.matrixNorm_nonneg D
  have hbEq : b = lemmaVInverseDepthMax Q a 0 := by
    change Book.Ch02.matrixNorm (coarseBlockMatrix (openCubeSet Q) a).lowerRight = _
    unfold lemmaVInverseDepthMax
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    unfold Book.Ch02.finsetSupReal
    rw [descendantsAtDepth_zero]
    simp
  have hbLeH0 : b ≤ H0 := by
    rw [hbEq]
    let M : ℕ → ℝ := lemmaVInverseDepthMax Q a
    let r : ℝ := q⁻¹
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hr1 : r < 1 := by
      dsimp [r]
      exact (inv_lt_one₀ hqpos).2 hq
    have hmono (k : ℕ) : M 0 ≤ M k := by
      induction k with
      | zero => rfl
      | succ k ih => exact ih.trans (lemmaVInverseDepthMax_le_succ Q hEll k)
    have hgeomS : Summable (fun k : ℕ => r ^ k) :=
      summable_geometric_of_lt_one hr hr1
    have hconstS : Summable (fun k : ℕ => r ^ k * M 0) := hgeomS.mul_right (M 0)
    have hhistS : Summable (fun k : ℕ => r ^ k * M k) := by
      simpa [r, M] using lemmaVInverseHistory_summable Q hEll hq
    have hle := hconstS.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (hmono k) (pow_nonneg hr k)) hhistS
    have hgeom := tsum_geometric_of_lt_one hr hr1
    dsimp [H0, lemmaVInverseHistory]
    have hsumConst : (∑' k : ℕ, r ^ k * M 0) = M 0 * (1 - r)⁻¹ := by
      calc
        _ = ∑' k : ℕ, M 0 * r ^ k := tsum_congr fun k => by ring
        _ = M 0 * ∑' k : ℕ, r ^ k := tsum_mul_left
        _ = M 0 * (1 - r)⁻¹ := by rw [hgeom]
    have hfactor : 0 ≤ 1 - r := by linarith
    have hcalc : M 0 ≤ (1 - r) * ∑' k : ℕ, r ^ k * M k := by
      calc
        M 0 = (1 - r) * (∑' k : ℕ, r ^ k * M 0) := by
          rw [hsumConst]
          field_simp [ne_of_gt (sub_pos.mpr hr1)]
        _ ≤ (1 - r) * ∑' k : ℕ, r ^ k * M k :=
          mul_le_mul_of_nonneg_left hle hfactor
    simpa [M, r] using hcalc
  have hL : 0 ≤ H0 - (1 - w) * b := by
    have hfac : 0 ≤ 1 - w := by
      have : w ≤ 1 := by
        have hw1 : w < 1 := (inv_lt_one₀ hqpos).2 hq
        exact hw1.le
      linarith
    nlinarith [hbnonneg, hH0nonneg, hbLeH0]
  have hmetricCirc : vecDot t (matVecMul D⁻¹ t) ≤
      (H0 - (1 - w) * b) * forcedSourceCircleEnergy Q F := by
    have hmetricEq : vecDot e t = vecDot t (matVecMul D⁻¹ t) := by
      dsimp [e]
      exact vecDot_comm _ _
    have hsourceSq' := hsourceSq
    rw [hmetricEq] at hsourceSq'
    have hbottom' : vectorWeakHaarEnergy Q (fun x i =>
        ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i) ≤
        (H0 - (1 - w) * b) * vecDot t (matVecMul D⁻¹ t) := by
      have htmp := hbottom
      rw [hDE, ← hbEq] at htmp
      simpa [H0, w] using htmp
    have hprod : (vecDot t (matVecMul D⁻¹ t)) ^ 2 ≤
        (forcedSourceCircleEnergy Q F * (H0 - (1 - w) * b)) *
          vecDot t (matVecMul D⁻¹ t) := by
      calc
        _ ≤ forcedSourceCircleEnergy Q F *
            vectorWeakHaarEnergy Q (fun x i =>
              ((pairedBesselOpenCubeFamilyData hEll).family.field (0, e)).potential x i) := hsourceSq'
        _ ≤ _ := by
          calc
            _ ≤ forcedSourceCircleEnergy Q F *
                ((H0 - (1 - w) * b) * vecDot t (matVecMul D⁻¹ t)) :=
              mul_le_mul_of_nonneg_left hbottom'
                (forcedSourceCircleEnergy_nonneg Q F)
            _ = _ := by ring
    by_cases hz : vecDot t (matVecMul D⁻¹ t) = 0
    · rw [hz]
      exact mul_nonneg hL (forcedSourceCircleEnergy_nonneg Q F)
    · have hpos : 0 < vecDot t (matVecMul D⁻¹ t) :=
        lt_of_le_of_ne hmetricNonneg (Ne.symm hz)
      have hquot := (div_le_iff₀ hpos).2 hprod
      have hcancel : (vecDot t (matVecMul D⁻¹ t)) ^ 2 /
          vecDot t (matVecMul D⁻¹ t) = vecDot t (matVecMul D⁻¹ t) := by
        field_simp [ne_of_gt hpos]
      rw [hcancel] at hquot
      simpa [mul_comm] using hquot
  have hcoef : b * (H0 - (1 - w) * b) ≤ w * H ^ 2 := by
    have hbLeH : b ≤ H := le_trans hbLeH0 hH0le
    have hfac1 : 0 ≤ H - b := sub_nonneg.mpr hbLeH
    have hfac2 : 0 ≤ w * H - (1 - w) * b := by
      have htw : 0 ≤ 2 * w - 1 := by linarith [hwle]
      nlinarith [hHnonneg, hbnonneg, hbLeH]
    have hprod : 0 ≤ (H - b) * (w * H - (1 - w) * b) :=
      mul_nonneg hfac1 hfac2
    have hcmp : b * (H0 - (1 - w) * b) ≤ b * (H - (1 - w) * b) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hH0le _) hbnonneg
    nlinarith [hprod]
  have hnorm := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    hD.posSemidef hDleft t
  calc
    vecNormSq t ≤ b * vecDot t (matVecMul D⁻¹ t) := by simpa [b, D] using hnorm
    _ ≤ b * ((H0 - (1 - w) * lemmaVInverseDepthMax Q a 0) *
        forcedSourceCircleEnergy Q F) := by
          have hmetricCirc' : vecDot t (matVecMul D⁻¹ t) ≤
              (H0 - (1 - w) * lemmaVInverseDepthMax Q a 0) *
                forcedSourceCircleEnergy Q F := by simpa [hbEq] using hmetricCirc
          exact mul_le_mul_of_nonneg_left hmetricCirc' hbnonneg
    _ ≤ w * H ^ 2 * forcedSourceCircleEnergy Q F := by
          have hcoef' : b * (H0 - (1 - w) * lemmaVInverseDepthMax Q a 0) ≤ w * H ^ 2 := by
            rw [← hbEq]
            exact hcoef
          simpa [mul_assoc] using
            mul_le_mul_of_nonneg_right hcoef' (forcedSourceCircleEnergy_nonneg Q F)
    _ = _ := by rfl

end
end ASDExplicitGamma.Variational
