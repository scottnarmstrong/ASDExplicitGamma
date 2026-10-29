module

public import ASDExplicitGamma.Variational.PairedBessel
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import ASDExplicitGamma.Scalar.InverseHistory
public import ASDExplicitGamma.Triadic.HaarNormTriangle

/-! Coercivity of compatible homogeneous fields from the complete inverse history. -/

@[expose] public section
namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Scalar
open scoped BigOperators

noncomputable section

/-- The real complete quarter-discount inverse history used by the source
coercivity inequalities. -/
def compatibleInverseHistory (Q : TriadicCube 2) (a : CoeffField 2) : ℝ :=
  lemmaVInverseHistory Q a (Real.sqrt 3)

private theorem energy_neg_local {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    energy Q (fun x => -f x) = energy Q f := by
  unfold energy pairing
  congr 1
  funext x
  ring

private theorem pairing_neg_right_local {d : ℕ} (Q : TriadicCube d)
    {f g : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    pairing Q f (fun x => -g x) = -pairing Q f g := by
  have h := pairing_sub_right Q hf (memLp_const (0 : ℝ)) hg
  calc
    pairing Q f (fun x => -g x) = pairing Q f (fun x => (0 : ℝ) - g x) := by
      congr 1
      funext x
      ring
    _ = pairing Q f (fun _ => 0) - pairing Q f g := h
    _ = -pairing Q f g := by
      simp [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]

/-- Parallelogram identity for the normalized cube energy. -/
private theorem energy_parallelogram {d : ℕ} (Q : TriadicCube d)
    {f g : Vec d → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x + g x) + energy Q (fun x => f x - g x) =
      2 * energy Q f + 2 * energy Q g := by
  have hplus := energy_sub Q hf hg.neg
  have hminus := energy_sub Q hf hg
  have hpneg := pairing_neg_right_local Q hf hg
  have hneg := energy_neg_local Q g
  have hplus' : energy Q (fun x => f x + g x) =
      energy Q f + 2 * pairing Q f g + energy Q g := by
    calc
      energy Q (fun x => f x + g x) = energy Q (fun x => f x - (-g x)) := by
        congr 1
        funext x
        ring
      _ = energy Q f - 2 * pairing Q f (fun x => -g x) + energy Q (fun x => -g x) := hplus
      _ = energy Q f + 2 * pairing Q f g + energy Q g := by rw [hpneg, hneg]; ring
  nlinarith [hplus', hminus]

/-- Scalar multiplication acts quadratically on the weak Haar energy. -/
private theorem dualEnergy_smul_local {d : ℕ} (Q : TriadicCube d) (c : ℝ)
    (f : Vec d → ℝ) :
    dualEnergy Q (Real.sqrt 3) (fun x => c * f x) = c ^ 2 * dualEnergy Q (Real.sqrt 3) f := by
  unfold dualEnergy primalEnergy
  have hinc (k : ℕ) : cubeIncrement Q k (fun x => c * f x) =
      fun x => c * cubeIncrement Q k f x := by
    cases k with
    | zero => simp [cubeIncrement_zero, projection_smul]
    | succ k => simp [cubeIncrement, projection_smul, mul_sub]
  have henergy (g : Vec d → ℝ) : energy Q (fun x => c * g x) = c ^ 2 * energy Q g := by
    unfold energy pairing
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    have hpoint : (fun x : Vec d => (c * g x) * (c * g x)) =
        fun x => c ^ 2 * (g x * g x) := by
      funext x
      ring
    rw [hpoint, integral_const_mul]
  change energy Q (cubeIncrement Q 0 (fun x => c * f x)) +
      ∑' k, (Real.sqrt 3)⁻¹ ^ (k + 1) *
        energy Q (cubeIncrement Q (k + 1) (fun x => c * f x)) = _
  rw [hinc 0, henergy]
  have hseries : (∑' k, (Real.sqrt 3)⁻¹ ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => c * f x))) =
      c ^ 2 * ∑' k, (Real.sqrt 3)⁻¹ ^ (k + 1) *
        energy Q (cubeIncrement Q (k + 1) f) := by
    calc
      _ = ∑' k, (Real.sqrt 3)⁻¹ ^ (k + 1) *
          (c ^ 2 * energy Q (cubeIncrement Q (k + 1) f)) := by
            apply tsum_congr
            intro k
            rw [hinc (k + 1), henergy]
      _ = _ := by rw [← tsum_mul_left]; congr 1; funext k; ring
  rw [hseries]
  ring

private theorem vectorWeakHaarEnergy_smul_local (Q : TriadicCube 2) (c : ℝ)
    (F : Vec 2 → Vec 2) :
    vectorWeakHaarEnergy Q (fun x i => c * F x i) =
      c ^ 2 * vectorWeakHaarEnergy Q F := by
  unfold vectorWeakHaarEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact dualEnergy_smul_local Q c (fun x => F x i)

/-- The doubled block state representing a homogeneous compatible field. -/
noncomputable def compatiblePairState {Q : TriadicCube 2} {a : CoeffField 2}
    (u : AHarmonicFunction a (openCubeSet Q))
    (v : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) : BlockState 2 :=
  blockResponsePairHalfState a u v

/-- First component of the homogeneous compatible field. -/
def compatiblePairFirst {Q : TriadicCube 2} {a : CoeffField 2}
    (u : AHarmonicFunction a (openCubeSet Q))
    (v : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) : Vec 2 → Vec 2 :=
  fun x => (compatiblePairState u v).potential x

/-- Second component of the coefficient image of the homogeneous compatible
field, written in its equal almost-everywhere harmonic-gradient form. -/
def compatiblePairSecondImage {Q : TriadicCube 2} {a : CoeffField 2}
    (u : AHarmonicFunction a (openCubeSet Q))
    (v : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) : Vec 2 → Vec 2 :=
  fun x => (1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x)

/-- The block energy of a homogeneous compatible field is the mean of its two
primal and adjoint harmonic energies. -/
theorem compatiblePairState_energy (Q : TriadicCube 2) {a : CoeffField 2}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction a (openCubeSet Q))
    (v : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) :
    blockPairingAverage (openCubeSet Q) a (compatiblePairState u v)
        (compatiblePairState u v) =
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a u) / 2 +
        volumeAverage (openCubeSet Q)
          (scalarVariationEnergyIntegrand (adjointCoeffField a) v) / 2 := by
  letI compatibleCoercivityFiniteMeasure : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have h := blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
    a (measurableSet_openCubeSet Q) hEll u v
  calc
    blockPairingAverage (openCubeSet Q) a (compatiblePairState u v)
        (compatiblePairState u v) = 2 * blockEnergyAverage (openCubeSet Q) a
          (compatiblePairState u v) := by
            rw [blockEnergyAverage_eq_half_blockPairingAverage_self]
            ring
    _ = _ := by
      change 2 * blockEnergyAverage (openCubeSet Q) a
        (blockResponsePairHalfState a u v) = _
      rw [h]
      ring

/-- The quarter-order weak energy of the two complementary half-pair
components is exactly one half of the sum of the two scalar weak energies. -/
private theorem compatiblePair_weakEnergy_parallelogram (Q : TriadicCube 2)
    {a : CoeffField 2} (u : AHarmonicFunction a (openCubeSet Q))
    (v : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) :
    vectorWeakHaarEnergy Q (compatiblePairFirst u v) +
      vectorWeakHaarEnergy Q (compatiblePairSecondImage u v) =
      (vectorWeakHaarEnergy Q (fun x i => u.toH1.grad x i) +
        vectorWeakHaarEnergy Q (fun x i => v.toH1.grad x i)) / 2 := by
  have hpara (F G : Vec 2 → Vec 2)
      (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
      (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
      vectorWeakHaarEnergy Q (fun x i => F x i + G x i) +
        vectorWeakHaarEnergy Q (fun x i => F x i - G x i) =
          2 * vectorWeakHaarEnergy Q F + 2 * vectorWeakHaarEnergy Q G := by
    unfold vectorWeakHaarEnergy
    have hcoord (i : Fin 2) :
        dualEnergy Q (Real.sqrt 3) (fun x => F x i + G x i) +
          dualEnergy Q (Real.sqrt 3) (fun x => F x i - G x i) =
            2 * dualEnergy Q (Real.sqrt 3) (fun x => F x i) +
              2 * dualEnergy Q (Real.sqrt 3) (fun x => G x i) := by
      have hq : 1 < Real.sqrt 3 := by
        have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
        nlinarith [Real.sqrt_nonneg (3 : ℝ)]
      have hplus := summable_weighted_projections Q hq ((hF i).add (hG i))
      have hminus := summable_weighted_projections Q hq ((hF i).sub (hG i))
      have hfi := summable_weighted_projections Q hq (hF i)
      have hgi := summable_weighted_projections Q hq (hG i)
      have hplusFormula : dualEnergy Q (Real.sqrt 3)
          (fun x => F x i + G x i) = (1 - (Real.sqrt 3)⁻¹) *
            ∑' k, (Real.sqrt 3)⁻¹ ^ k *
              energy Q (cubeProjection Q k (fun x => F x i + G x i)) := by
        have h := dualEnergy_eq_weighted_projections Q hq ((hF i).add (hG i)) hplus
        change dualEnergy Q (Real.sqrt 3)
          ((fun x => F x i) + (fun x => G x i)) = _ at h
        exact h
      have hminusFormula : dualEnergy Q (Real.sqrt 3)
          (fun x => F x i - G x i) = (1 - (Real.sqrt 3)⁻¹) *
            ∑' k, (Real.sqrt 3)⁻¹ ^ k *
              energy Q (cubeProjection Q k (fun x => F x i - G x i)) := by
        have h := dualEnergy_eq_weighted_projections Q hq ((hF i).sub (hG i)) hminus
        change dualEnergy Q (Real.sqrt 3)
          ((fun x => F x i) - (fun x => G x i)) = _ at h
        exact h
      have hfiFormula := dualEnergy_eq_weighted_projections Q hq (hF i) hfi
      have hgiFormula := dualEnergy_eq_weighted_projections Q hq (hG i) hgi
      rw [hplusFormula, hminusFormula, hfiFormula, hgiFormula]
      have htsum : ∀ k,
          energy Q (cubeProjection Q k (fun x => F x i + G x i)) +
            energy Q (cubeProjection Q k (fun x => F x i - G x i)) =
              2 * energy Q (cubeProjection Q k (fun x => F x i)) +
                2 * energy Q (cubeProjection Q k (fun x => G x i)) := by
        intro k
        have hpadd : cubeProjection Q k (fun x => F x i + G x i) =
            fun x => cubeProjection Q k (fun x => F x i) x + cubeProjection Q k (fun x => G x i) x :=
          by simpa using projection_add Q k (hF i) (hG i)
        have hpsub : cubeProjection Q k (fun x => F x i - G x i) =
            fun x => cubeProjection Q k (fun x => F x i) x - cubeProjection Q k (fun x => G x i) x := by
          have hneg : cubeProjection Q k (fun x => -G x i) =
              fun x => -cubeProjection Q k (fun x => G x i) x := by
            simpa only [neg_one_mul] using projection_smul Q k (fun x => G x i) (-1)
          calc
            cubeProjection Q k (fun x => F x i - G x i) =
                cubeProjection Q k (fun x => F x i + -G x i) := by
              congr 1
            _ = fun x => cubeProjection Q k (fun x => F x i) x +
                cubeProjection Q k (fun x => -G x i) x :=
              projection_add Q k (hF i) (hG i).neg
            _ = _ := by rw [hneg]; funext x; ring
        rw [hpadd, hpsub]
        exact energy_parallelogram Q (projection_memLp Q k (fun x => F x i) 2)
          (projection_memLp Q k (fun x => G x i) 2)
      have hplusSeq : Summable (fun k => (Real.sqrt 3)⁻¹ ^ k *
          energy Q (cubeProjection Q k (fun x => F x i + G x i))) := by
        change Summable (fun k => (Real.sqrt 3)⁻¹ ^ k *
          energy Q (cubeProjection Q k ((fun x => F x i) + (fun x => G x i))))
        exact hplus
      have hminusSeq : Summable (fun k => (Real.sqrt 3)⁻¹ ^ k *
          energy Q (cubeProjection Q k (fun x => F x i - G x i))) := by
        change Summable (fun k => (Real.sqrt 3)⁻¹ ^ k *
          energy Q (cubeProjection Q k ((fun x => F x i) - (fun x => G x i))))
        exact hminus
      have htsums :
          (∑' k, (Real.sqrt 3)⁻¹ ^ k *
              energy Q (cubeProjection Q k (fun x => F x i + G x i))) +
            (∑' k, (Real.sqrt 3)⁻¹ ^ k *
              energy Q (cubeProjection Q k (fun x => F x i - G x i))) =
          (∑' k, (Real.sqrt 3)⁻¹ ^ k *
              (2 * energy Q (cubeProjection Q k (fun x => F x i)) +
                2 * energy Q (cubeProjection Q k (fun x => G x i))) ) := by
        calc
          _ = ∑' k, ((Real.sqrt 3)⁻¹ ^ k *
              energy Q (cubeProjection Q k (fun x => F x i + G x i)) +
            (Real.sqrt 3)⁻¹ ^ k *
              energy Q (cubeProjection Q k (fun x => F x i - G x i))) :=
                (hplusSeq.tsum_add hminusSeq).symm
          _ = ∑' k, (Real.sqrt 3)⁻¹ ^ k *
              (energy Q (cubeProjection Q k (fun x => F x i + G x i)) +
                energy Q (cubeProjection Q k (fun x => F x i - G x i))) := by
                  apply tsum_congr
                  intro k
                  ring
          _ = _ := by
                apply tsum_congr
                intro k
                rw [htsum k]
      have hweight : 0 ≤ 1 - (Real.sqrt 3)⁻¹ := by
        have hs : (Real.sqrt 3)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).2 hq
        linarith
      have hdecomp :
          (∑' k, (Real.sqrt 3)⁻¹ ^ k *
              (2 * energy Q (cubeProjection Q k (fun x => F x i)) +
                2 * energy Q (cubeProjection Q k (fun x => G x i)))) =
          2 * (∑' k, (Real.sqrt 3)⁻¹ ^ k *
              energy Q (cubeProjection Q k (fun x => F x i))) +
            2 * (∑' k, (Real.sqrt 3)⁻¹ ^ k *
              energy Q (cubeProjection Q k (fun x => G x i))) := by
        calc
          _ = ∑' k, (2 * ((Real.sqrt 3)⁻¹ ^ k *
                energy Q (cubeProjection Q k (fun x => F x i))) +
              2 * ((Real.sqrt 3)⁻¹ ^ k *
                energy Q (cubeProjection Q k (fun x => G x i)))) := by
                  apply tsum_congr
                  intro k
                  ring
          _ = _ := by
            calc
              _ = (∑' k, 2 * ((Real.sqrt 3)⁻¹ ^ k *
                    energy Q (cubeProjection Q k (fun x => F x i)))) +
                  ∑' k, 2 * ((Real.sqrt 3)⁻¹ ^ k *
                    energy Q (cubeProjection Q k (fun x => G x i))) :=
                      (hfi.mul_left 2).tsum_add (hgi.mul_left 2)
              _ = _ := by rw [tsum_mul_left, tsum_mul_left]
      calc
        (1 - (Real.sqrt 3)⁻¹) *
              (∑' k, (Real.sqrt 3)⁻¹ ^ k * energy Q (cubeProjection Q k (fun x => F x i + G x i))) +
            (1 - (Real.sqrt 3)⁻¹) *
              (∑' k, (Real.sqrt 3)⁻¹ ^ k * energy Q (cubeProjection Q k (fun x => F x i - G x i))) =
            (1 - (Real.sqrt 3)⁻¹) *
              ((∑' k, (Real.sqrt 3)⁻¹ ^ k * energy Q (cubeProjection Q k (fun x => F x i + G x i))) +
                ∑' k, (Real.sqrt 3)⁻¹ ^ k * energy Q (cubeProjection Q k (fun x => F x i - G x i))) := by ring
        _ = (1 - (Real.sqrt 3)⁻¹) *
              (∑' k, (Real.sqrt 3)⁻¹ ^ k *
                (2 * energy Q (cubeProjection Q k (fun x => F x i)) +
                  2 * energy Q (cubeProjection Q k (fun x => G x i)))) := by rw [htsums]
        _ = _ := by
          rw [hdecomp]
          ring
    calc
      _ = ∑ i, (dualEnergy Q (Real.sqrt 3) (fun x => F x i + G x i) +
          dualEnergy Q (Real.sqrt 3) (fun x => F x i - G x i)) := by rw [Finset.sum_add_distrib]
      _ = ∑ i, (2 * dualEnergy Q (Real.sqrt 3) (fun x => F x i) +
          2 * dualEnergy Q (Real.sqrt 3) (fun x => G x i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hcoord i
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hpara' := hpara
      (fun x i => (1 / 2 : ℝ) * u.toH1.grad x i)
      (fun x i => (1 / 2 : ℝ) * v.toH1.grad x i)
      (fun i => (u.toH1.grad_memL2_normalizedCubeMeasure i).const_smul (1 / 2 : ℝ))
      (fun i => (v.toH1.grad_memL2_normalizedCubeMeasure i).const_smul (1 / 2 : ℝ))
  have huScale := vectorWeakHaarEnergy_smul_local Q (1 / 2 : ℝ)
    (fun x i => u.toH1.grad x i)
  have hvScale := vectorWeakHaarEnergy_smul_local Q (1 / 2 : ℝ)
    (fun x i => v.toH1.grad x i)
  have hfirst : compatiblePairFirst u v =
      fun x => (1 / 2 : ℝ) • u.toH1.grad x + (1 / 2 : ℝ) • v.toH1.grad x := by
    funext x
    ext i
    change ((1 / 2 : ℝ) • (u.toH1.grad x + v.toH1.grad x)) i = _
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  have hsecond : compatiblePairSecondImage u v =
      fun x => (1 / 2 : ℝ) • u.toH1.grad x - (1 / 2 : ℝ) • v.toH1.grad x := by
    funext x
    ext i
    change ((1 / 2 : ℝ) • (u.toH1.grad x - v.toH1.grad x)) i = _
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hfirst, hsecond]
  rw [huScale, hvScale] at hpara'
  norm_num at hpara'
  have hcoordinate :
      vectorWeakHaarEnergy Q
          (fun x i => (1 / 2 : ℝ) * u.toH1.grad x i +
            (1 / 2 : ℝ) * v.toH1.grad x i) +
        vectorWeakHaarEnergy Q
          (fun x i => (1 / 2 : ℝ) * u.toH1.grad x i -
            (1 / 2 : ℝ) * v.toH1.grad x i) =
      (vectorWeakHaarEnergy Q u.toH1.grad +
        vectorWeakHaarEnergy Q v.toH1.grad) / 2 := by
    nlinarith [hpara']
  change vectorWeakHaarEnergy Q
      (fun x i => (1 / 2 : ℝ) * u.toH1.grad x i +
        (1 / 2 : ℝ) * v.toH1.grad x i) +
    vectorWeakHaarEnergy Q
      (fun x i => (1 / 2 : ℝ) * u.toH1.grad x i -
        (1 / 2 : ℝ) * v.toH1.grad x i) =
    (vectorWeakHaarEnergy Q (fun x i => u.toH1.grad x i) +
      vectorWeakHaarEnergy Q (fun x i => v.toH1.grad x i)) / 2
  exact hcoordinate

/-- Paired coercivity for the compatible field and its coefficient-image
component, with the complete inverse-history constant and source energy. -/
theorem paired_compatible_coercivity
    (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction a (openCubeSet Q))
    (v : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) :
    vectorWeakHaarEnergy Q (compatiblePairFirst u v) +
      vectorWeakHaarEnergy Q (compatiblePairSecondImage u v) ≤
      compatibleInverseHistory Q a *
        blockPairingAverage (openCubeSet Q) a (compatiblePairState u v)
          (compatiblePairState u v) := by
  have hu0 := lemmaV_harmonic_vectorWeakHaarEnergy_le Q hEll u
  have hv0 := lemmaV_adjoint_vectorWeakHaarEnergy_le Q hEll v
  have hu : vectorWeakHaarEnergy Q u.toH1.grad ≤ compatibleInverseHistory Q a *
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a u) := by
    simpa [compatibleInverseHistory, volumeAverage, integralAverage,
      cubeAverage_eq_integralAverage_openCubeSet] using hu0
  have hv : vectorWeakHaarEnergy Q v.toH1.grad ≤ compatibleInverseHistory Q a *
      volumeAverage (openCubeSet Q)
        (scalarVariationEnergyIntegrand (adjointCoeffField a) v) := by
    simpa [compatibleInverseHistory, volumeAverage, integralAverage,
      cubeAverage_eq_integralAverage_openCubeSet] using hv0
  rw [compatiblePair_weakEnergy_parallelogram]
  rw [compatiblePairState_energy Q hEll u v]
  unfold compatibleInverseHistory
  unfold compatibleInverseHistory at hu hv
  nlinarith [hu, hv]

/-- The coefficient dual reflection of an arbitrary finite-energy field remains
in the block `L²` carrier. -/
theorem compatibleReflectState_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (W : BlockState d) (hW : MemBlockL2 U W.eval) :
    MemBlockL2 U (pairedReflectState a W).eval := by
  have hp : MemVectorL2 U W.potential := by
    simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 hW
  have hq : MemVectorL2 U W.flux := by
    simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hW
  have hk := memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hp
  have hdiff : MemVectorL2 U
      (fun x => W.flux x - matVecMul (skewPart (a x)) (W.potential x)) := hq.sub hk
  have hlower := memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hdiff
  have hSymm := memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hp
  have hSkew := memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hlower
  have hUpperSum : MemVectorL2 U
      (fun x => matVecMul (symmPart (a x)) (W.potential x) +
        matVecMul (skewPart (a x))
          (matVecMul ((symmPart (a x))⁻¹)
            (W.flux x - matVecMul (skewPart (a x)) (W.potential x)))) := hSymm.add hSkew
  have hLowerEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) =
        (fun x => matVecMul ((symmPart (a x))⁻¹)
          (W.flux x - matVecMul (skewPart (a x)) (W.potential x))) := by
    funext x
    change (blockMatVecMul (blockMatrixOfCoeff (a x))
      (W.potential x, W.flux x)).2 = _
    rw [blockMatVecMul_blockMatrixOfCoeff_snd]
  have hUpperEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).1) =
        (fun x => matVecMul (symmPart (a x)) (W.potential x) +
          matVecMul (skewPart (a x))
            (matVecMul ((symmPart (a x))⁻¹)
              (W.flux x - matVecMul (skewPart (a x)) (W.potential x)))) := by
    funext x
    change (blockMatVecMul (blockMatrixOfCoeff (a x))
      (W.potential x, W.flux x)).1 = _
    rw [blockMatVecMul_blockMatrixOfCoeff_fst]
  have hLower : MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) := by
    rw [hLowerEq]
    exact hlower
  have hUpper : MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).1) := by
    rw [hUpperEq]
    exact hUpperSum
  change MemBlockL2 U
    (fun x => ((blockMatVecMul (blockCoeffField a x) (W.eval x)).2,
      (blockMatVecMul (blockCoeffField a x) (W.eval x)).1))
  exact memBlockL2_blockField hLower hUpper

/-- A compatible field is controlled by the lower-right coarse energy block.
This is the source's local div-curl estimate and imposes no Euler equation on
the field being estimated. -/
theorem compatible_meanGradient_bound_of_minimizerFamily
    {d : ℕ} [NeZero d] {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ}
    (hConv : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (F : LinearMuMinimizerFamily U a)
    (W : BlockState d) (hWpot : IsBlockPotentialOn U W)
    (hWsol : IsBlockSolenoidalOn U W)
    (hWmem : MemBlockL2 U W.eval) :
    vecNormSq (pairedPotentialMean U W) ≤
      Book.Ch02.matrixNorm (coarseBlockMatrix U a).lowerRight *
        blockPairingAverage U a W W := by
  let Data := exists_energyMap_coarseData hConv hEll hvol
  obtain ⟨_sigma, hCoarse, _hInv, _hStar, _hKappa, _hSigma, hDpos, _hdet⟩ := Data
  let D : Mat d := (coarseBlockMatrix U a).lowerRight
  have hD : D.PosDef := by
    dsimp [D]
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hDinv : D⁻¹.PosDef := hD.inv
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  let p : Vec d := pairedPotentialMean U W
  let e : Vec d := matVecMul D⁻¹ p
  let S : BlockState d := F.field (0, e)
  let C : BlockState d := { potential := fun _ => 0, flux := fun _ => e }
  let Adm := F.admissible (0, e)
  let Corr := Adm.toCorrectionFieldDataOfAdmissible
  have hSmem : MemBlockL2 U S.eval := by
    simpa [S] using Adm.memBlockL2_eval
  have hJmem : MemBlockL2 U (pairedReflectState a W).eval :=
    compatibleReflectState_memBlockL2 hEll W hWmem
  have hSJ : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a S (pairedReflectState a W)) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hJmem hEll
  have hSS : MeasureTheory.IntegrableOn (blockPairingIntegrand a S S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hSmem hEll
  have hJJ : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a (pairedReflectState a W) (pairedReflectState a W)) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hJmem hJmem hEll
  have hmeanS : blockPairingAverage U a S S = vecDot e (matVecMul D e) := by
    have hreal := F.realizes (0, e)
    have hmat := F.mu_eq_half_blockVecDot_coarseBlockMatrix (0, e)
    rw [hreal, blockEnergyAverage_eq_half_blockPairingAverage_self] at hmat
    have hdiag : blockPairingAverage U a S S =
        blockVecDot (0, e) (blockMatVecMul (coarseBlockMatrix U a) (0, e)) := by
      dsimp [S]
      nlinarith [hmat]
    simpa [D, blockVecDot, blockMatVecMul, matVecMul_zero, vecDot_zero_left] using hdiag
  have hcross : blockPairingAverage U a S (pairedReflectState a W) = vecDot e p := by
    let T : BlockState d := { potential := Corr.potential, flux := Corr.flux }
    have hsplit : S = T + C := by
      apply BlockState.ext
      · funext x
        change S.potential x = T.potential x + C.potential x
        simp [S, T, C, Corr, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible]
      · funext x
        change S.flux x = T.flux x + C.flux x
        simp [S, T, C, Corr, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible]
        
    have hInt1 : MeasureTheory.IntegrableOn
        (fun x => vecDot (T.potential x) (W.flux x)) U :=
      integrableOn_vecDot_of_memVectorL2 Corr.potential_memL2
        (memVectorL2_snd_of_memBlockL2 hWmem)
    have hInt2 : MeasureTheory.IntegrableOn
        (fun x => vecDot (T.flux x) (W.potential x)) U :=
      integrableOn_vecDot_of_memVectorL2 Corr.flux_memL2
        (memVectorL2_fst_of_memBlockL2 hWmem)
    have hInt3 : MeasureTheory.IntegrableOn
        (fun x => vecDot e (W.potential x)) U :=
      CorrectionFieldData.integrableOn_vecDot_const_left_of_memVectorL2 e
        (memVectorL2_fst_of_memBlockL2 hWmem)
    have hzero1 : ∫ x in U, vecDot (T.potential x) (W.flux x)
        ∂MeasureTheory.volume = 0 := by
      rcases Corr.isPotentialZeroTrace with ⟨φ, hφ⟩
      have h := hWsol φ
      simpa [hφ, vecDot_comm] using h
    have hzero2 : ∫ x in U, vecDot (T.flux x) (W.potential x)
        ∂MeasureTheory.volume = 0 := by
      rcases hWpot with ⟨φ, hφ⟩
      have h := Corr.isSolenoidalZeroNormalTrace φ
      simpa [hφ] using h
    have hzeroAvg1 : volumeAverage U
        (fun x => vecDot (T.potential x) (W.flux x)) = 0 :=
      volumeAverage_eq_zero_of_integral_eq_zero hzero1
    have hzeroAvg2 : volumeAverage U
        (fun x => vecDot (T.flux x) (W.potential x)) = 0 :=
      volumeAverage_eq_zero_of_integral_eq_zero hzero2
    have hcoord : ∀ i, MeasureTheory.IntegrableOn (fun x => W.potential x i) U := by
      intro i
      exact CorrectionFieldData.integrableOn_coord_of_memVectorL2
        (memVectorL2_fst_of_memBlockL2 hWmem) i
    have hconst : volumeAverage U (fun x => vecDot e (W.potential x)) = vecDot e p := by
      exact volumeAverage_vecDot_left e W.potential hcoord
    have hpoint :
        (fun x => vecDot (S.potential x) (W.flux x) +
          vecDot (S.flux x) (W.potential x)) =
        (fun x => vecDot (T.potential x) (W.flux x) +
          vecDot (T.flux x) (W.potential x) + vecDot e (W.potential x)) := by
      funext x
      rw [hsplit]
      change vecDot (T.potential x + C.potential x) (W.flux x) +
          vecDot (T.flux x + C.flux x) (W.potential x) = _
      simp only [C]
      rw [vecDot_add_left, vecDot_add_left]
      simp only [vecDot_zero_left]
      ring
    have hcrossRaw : blockPairingAverage U a S (pairedReflectState a W) =
        volumeAverage U (fun x => vecDot (S.potential x) (W.flux x) +
          vecDot (S.flux x) (W.potential x)) := by
      unfold blockPairingAverage volumeAverage
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem
        (measurableSet_of_isEllipticFieldOn hEll)] with x hx
      change blockVecDot (S.eval x)
        (blockMatVecMul (blockCoeffField a x)
          ((pairedReflectState a W).eval x)) = _
      rw [pairedReflectState_action hEll W hx]
      simp [BlockState.eval, blockVecDot]
    calc
      blockPairingAverage U a S (pairedReflectState a W) =
          volumeAverage U (fun x => vecDot (S.potential x) (W.flux x) +
            vecDot (S.flux x) (W.potential x)) := by
        exact hcrossRaw
      _ = volumeAverage U
          (fun x => vecDot (T.potential x) (W.flux x) +
            vecDot (T.flux x) (W.potential x) + vecDot e (W.potential x)) := by
        rw [← hpoint]
      _ = volumeAverage U
          ((fun x => vecDot (T.potential x) (W.flux x) +
            vecDot (T.flux x) (W.potential x)) +
            (fun x => vecDot e (W.potential x))) := by
        rfl
      _ = _ := by
        have hPointAdd :
            (fun x => vecDot (T.potential x) (W.flux x) +
              vecDot (T.flux x) (W.potential x)) =
            (fun x => vecDot (T.potential x) (W.flux x)) +
              (fun x => vecDot (T.flux x) (W.potential x)) := by
          funext x
          rfl
        rw [hPointAdd]
        rw [volumeAverage_add (hInt1.add hInt2) hInt3]
        have hAdd := volumeAverage_add (U := U)
          (f := fun x => vecDot (T.potential x) (W.flux x))
          (g := fun x => vecDot (T.flux x) (W.potential x)) hInt1 hInt2
        rw [hAdd, hzeroAvg1, hzeroAvg2, hconst]
        ring
  have hReflectEnergy := pairedReflect_pairingAverage_isometry hEll W W
  have hCS := blockPairingAverage_sq_le_product hEll
    (measurableSet_of_isEllipticFieldOn hEll) S (pairedReflectState a W)
    hSS hSJ hJJ
  have hSmeanInv : blockPairingAverage U a S S = vecDot p e := by
    rw [hmeanS]
    dsimp [e]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hDdet]
    have h : matVecMul (1 : Mat d) p = p := by
      funext i
      simp [matVecMul, Matrix.one_apply]
    rw [h]
    exact vecDot_comm _ _
  have hqnonneg : 0 ≤ vecDot p e := by
    by_cases hp0 : p = 0
    · simp [p, hp0, e, matVecMul_zero, vecDot_zero_left]
    · have hpos := hDinv.dotProduct_mulVec_pos hp0
      have hpos' : 0 < vecDot p (matVecMul D⁻¹ p) := by
        simpa [dotProduct, Matrix.mulVec, matVecMul, vecDot] using hpos
      simpa [e] using le_of_lt hpos'
  have hEblock : 0 ≤ blockEnergyAverage U a W := by
    unfold blockEnergyAverage
    apply volumeAverage_nonneg_of_nonneg_on
      (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    unfold blockEnergyDensity
    have hpoint : 0 ≤ blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField a x) (W.eval x)) := by
      simpa [blockCoeffField] using
        blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (W.eval x)
    exact mul_nonneg (by norm_num) hpoint
  have hWnonneg : 0 ≤ blockPairingAverage U a W W := by
    have hhalf := blockEnergyAverage_eq_half_blockPairingAverage_self U a W
    nlinarith
  have hCauchy : (vecDot p e) ^ 2 ≤
      vecDot p e * blockPairingAverage U a W W := by
    rw [hcross, hSmeanInv, hReflectEnergy] at hCS
    simpa [vecDot_comm] using hCS
  have hdual : vecDot p e ≤ blockPairingAverage U a W W := by
    by_cases hzero : vecDot p e = 0
    · rw [hzero]
      exact hWnonneg
    · have hpos : 0 < vecDot p e := lt_of_le_of_ne hqnonneg (Ne.symm hzero)
      nlinarith [hCauchy]
  have hDleft : ∀ ξ : Vec d, matVecMul D (matVecMul D⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hDdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hnorm := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    hD.posSemidef hDleft p
  calc
    vecNormSq (pairedPotentialMean U W) = vecNormSq p := by rfl
    _ ≤ Book.Ch02.matrixNorm D * vecDot p e := by simpa [D, e] using hnorm
    _ ≤ Book.Ch02.matrixNorm D * blockPairingAverage U a W W :=
      mul_le_mul_of_nonneg_left hdual (Book.Ch02.matrixNorm_nonneg D)

/-- Every triadic open square has its actual affine minimizers, transported
from the origin square by the source translation. -/
private theorem compatible_isElliptic_translateCoeffField
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

private theorem compatible_linearMuMinimizerFamily_exists
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Nonempty (LinearMuMinimizerFamily (openCubeSet Q) a) := by
  let U : Set (Vec 2) := openCubeSet Q
  let z : Vec 2 := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  let U0 : Set (Vec 2) := openCubeSet (originCube 2 Q.scale)
  let a0 : CoeffField 2 := translateCoeffField z a
  have hTranslate : U = translateSet z U0 :=
    openCubeSet_eq_translateSet_originCube_of_triadicCube Q
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_openCubeSet_lt_top Q⟩
  let : IsFiniteMeasure (volumeMeasureOn U) := by infer_instance
  have hEll0 : IsEllipticFieldOn lam Lam U0 a0 := by
    have hEllTarget : IsEllipticFieldOn lam Lam (translateSet z U0) a := by
      simpa [U, hTranslate] using hEll
    exact compatible_isElliptic_translateCoeffField z hEllTarget
  let : Fact (MeasureTheory.volume U0 < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := 2) Q.scale⟩
  let : IsFiniteMeasure (volumeMeasureOn U0) := by infer_instance
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
      have hAdmissible := isBlockMuAdmissible_translateSet (F0.admissible P) z
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
  exact ⟨by simpa [U] using F⟩

/-- Local mean-gradient bound on every source cell, with the actual coarse
inverse block and no harmonicity assumption on the field. -/
theorem compatible_meanGradient_bound_openCubeSet
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2)
    (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    (hWsol : IsBlockSolenoidalOn (openCubeSet Q) W)
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval) :
    vecNormSq (pairedPotentialMean (openCubeSet Q) W) ≤
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet Q) a) *
        blockPairingAverage (openCubeSet Q) a W W := by
  let U : Set (Vec 2) := openCubeSet Q
  let : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_openCubeSet_lt_top Q⟩
  let : IsFiniteMeasure (volumeMeasureOn U) := by infer_instance
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hConv : IsOpenBoundedConvexDomain U :=
    isOpenBoundedConvexDomain_openCubeSet Q
  obtain ⟨F⟩ := compatible_linearMuMinimizerFamily_exists hEll
  have h := compatible_meanGradient_bound_of_minimizerFamily hConv hvol hEll F W
    hWpot hWsol hWmem
  obtain ⟨_sigma, hCoarse, _, _, _, _, _, _⟩ :=
    exists_energyMap_coarseData hConv hEll hvol
  simpa [U, coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse] using h

theorem compatible_blockPairingAverage_nonneg
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (W : BlockState 2) :
    0 ≤ blockPairingAverage (openCubeSet Q) a W W := by
  have hEnergy : 0 ≤ blockEnergyAverage (openCubeSet Q) a W := by
    unfold blockEnergyAverage
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_openCubeSet Q)
    intro x hx
    unfold blockEnergyDensity
    have hpoint : 0 ≤ blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField a x) (W.eval x)) := by
      simpa [blockCoeffField] using
        blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (W.eval x)
    exact mul_nonneg (by norm_num) hpoint
  have hhalf := blockEnergyAverage_eq_half_blockPairingAverage_self
    (openCubeSet Q) a W
  nlinarith

/-- The level-k projection energy of an arbitrary compatible field is bounded
by the actual depth-k inverse maximum times its full doubled energy. -/
theorem compatible_projectionEnergy_bound
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2)
    (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    (hWsol : IsBlockSolenoidalOn (openCubeSet Q) W)
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval) (k : ℕ) :
    (∑ i, energy Q (cubeProjection Q k (fun x => W.potential x i))) ≤
      lemmaVInverseDepthMax Q a k *
        cubeAverage Q (blockPairingIntegrand a W W) := by
  change IsPotentialOn (openCubeSet Q) W.potential at hWpot
  obtain ⟨v, hv⟩ := hWpot
  let : Fact (MeasureTheory.volume (openCubeSet Q) < ⊤) :=
    ⟨volume_openCubeSet_lt_top Q⟩
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by infer_instance
  have hIntOpen : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a W W) (openCubeSet Q) :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hWmem hEll
  have hInt : MeasureTheory.IntegrableOn
      (blockPairingIntegrand a W W) (cubeSet Q) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hIntOpen
  rw [← hv, lemmaV_projectionEnergy_eq_meanGradient Q k v]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    Q k (blockPairingIntegrand a W W) hInt]
  unfold descendantsAverage
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q k) :
      vecNormSq (fun i => cubeAverage R (fun x => v.grad x i)) ≤
        lemmaVInverseDepthMax Q a k * cubeAverage R (blockPairingIntegrand a W W) := by
    let V : Set (Vec 2) := openCubeSet R
    have hsub : V ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR : IsEllipticFieldOn lam Lam V a :=
      hEll.mono (measurableSet_openCubeSet R) hsub
    let : Fact (MeasureTheory.volume V < ⊤) := ⟨volume_openCubeSet_lt_top R⟩
    let : IsFiniteMeasure (volumeMeasureOn V) := by infer_instance
    have hpotmem : MemVectorL2 V W.potential := by
      exact (memVectorL2_fst_of_memBlockL2 hWmem).mono_measure
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsub)
    have hfluxmem : MemVectorL2 V W.flux := by
      exact (memVectorL2_snd_of_memBlockL2 hWmem).mono_measure
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsub)
    have hWmemR : MemBlockL2 V W.eval := by
      exact memBlockL2_blockField hpotmem hfluxmem
    have hWpotR : IsBlockPotentialOn V W := by
      change IsPotentialOn V W.potential
      have hgradmem : MemVectorL2 V v.grad := by
        simpa only [hv] using hpotmem
      simpa only [hv] using v.isPotentialOn.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub hgradmem
    have hWsolR : IsBlockSolenoidalOn V W := by
      change IsSolenoidalOn V W.flux
      exact hWsol.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub hfluxmem
    have hmean : pairedPotentialMean V W =
        fun i => cubeAverage R (fun x => v.grad x i) := by
      funext i
      simp [pairedPotentialMean, volumeAverageVec, V, hv,
        cubeAverage_eq_integralAverage_openCubeSet, volumeAverage, integralAverage,
        volume_openCubeSet_toReal]
    have hpair : blockPairingAverage V a W W =
        cubeAverage R (blockPairingIntegrand a W W) := by
      rw [blockPairingAverage, cubeAverage_eq_integralAverage_openCubeSet]
      rfl
    have hlocal := compatible_meanGradient_bound_openCubeSet hEllR W hWpotR hWsolR hWmemR
    rw [hmean, hpair] at hlocal
    have hsup : Book.Ch02.matrixNorm (sigmaStarInvCoarse V a) ≤
        lemmaVInverseDepthMax Q a k := by
      unfold lemmaVInverseDepthMax Book.Ch02.finsetSupReal
      exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R, hR, rfl⟩
    have henergy : 0 ≤ cubeAverage R (blockPairingIntegrand a W W) := by
      rw [← hpair]
      exact compatible_blockPairingAverage_nonneg hEllR W
    have hlocal' : vecNormSq (fun i => cubeAverage R (fun x => v.grad x i)) ≤
        Book.Ch02.matrixNorm (sigmaStarInvCoarse V a) *
          cubeAverage R (blockPairingIntegrand a W W) := by
      simpa using hlocal
    calc
      _ ≤ Book.Ch02.matrixNorm (sigmaStarInvCoarse V a) *
          cubeAverage R (blockPairingIntegrand a W W) := hlocal'
      _ ≤ lemmaVInverseDepthMax Q a k *
          cubeAverage R (blockPairingIntegrand a W W) :=
        mul_le_mul_of_nonneg_right hsup henergy
  calc
    ((descendantsAtDepth Q k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q k,
          vecNormSq (fun i => cubeAverage R (fun x => v.grad x i)) ≤
      ((descendantsAtDepth Q k).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q k,
          lemmaVInverseDepthMax Q a k * cubeAverage R (blockPairingIntegrand a W W) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpoint) (by positivity)
    _ = lemmaVInverseDepthMax Q a k *
        descendantsAverage Q k (fun R => cubeAverage R (blockPairingIntegrand a W W)) := by
      unfold descendantsAverage
      rw [← Finset.mul_sum]
      ring_nf

/-- Complete-history coercivity for every finite-energy compatible field on a
triadic square. -/
theorem compatible_coercivity
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2)
    (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    (hWsol : IsBlockSolenoidalOn (openCubeSet Q) W)
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval) :
    vectorWeakHaarEnergy Q (fun x i => W.potential x i) ≤
      compatibleInverseHistory Q a * blockPairingAverage (openCubeSet Q) a W W := by
  change IsPotentialOn (openCubeSet Q) W.potential at hWpot
  obtain ⟨v, hv⟩ := hWpot
  have hWpot' : IsBlockPotentialOn (openCubeSet Q) W := ⟨v, hv⟩
  have hq : 1 < Real.sqrt 3 := by
    have hs : (Real.sqrt 3) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hw : 0 ≤ (Real.sqrt 3)⁻¹ := inv_nonneg.mpr (by positivity)
  have hw1 : 0 ≤ 1 - (Real.sqrt 3)⁻¹ := by
    have hlt : (Real.sqrt 3)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).2 hq
    linarith
  have hsCoord (i : Fin 2) : Summable (fun k => (Real.sqrt 3)⁻¹ ^ k *
      energy Q (cubeProjection Q k (fun x => v.grad x i))) :=
    summable_weighted_projections Q hq (v.grad_memL2_normalizedCubeMeasure i)
  have hsSum : Summable (fun k => ∑ i, (Real.sqrt 3)⁻¹ ^ k *
      energy Q (cubeProjection Q k (fun x => v.grad x i))) :=
    summable_sum fun i _ => hsCoord i
  have hEq : vectorWeakHaarEnergy Q (fun x i => W.potential x i) =
      (1 - (Real.sqrt 3)⁻¹) * ∑' k, (Real.sqrt 3)⁻¹ ^ k *
        (∑ i, energy Q (cubeProjection Q k (fun x => v.grad x i))) := by
    simp_rw [vectorWeakHaarEnergy, ← hv,
      dualEnergy_eq Q hq (v.grad_memL2_normalizedCubeMeasure _)]
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ => hsCoord i)]
    congr 1
    exact tsum_congr fun k => (Finset.mul_sum _ _ _).symm
  rw [hEq]
  have hE : 0 ≤ cubeAverage Q (blockPairingIntegrand a W W) := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    simpa [blockPairingAverage, volumeAverage, integralAverage] using
      compatible_blockPairingAverage_nonneg hEll W
  have hsHist := lemmaVInverseHistory_summable Q hEll hq
  have hleft : Summable (fun k => (Real.sqrt 3)⁻¹ ^ k *
      (∑ i, energy Q (cubeProjection Q k (fun x => v.grad x i)))) := by
    simpa only [Finset.mul_sum] using hsSum
  calc
    (1 - (Real.sqrt 3)⁻¹) * ∑' k, (Real.sqrt 3)⁻¹ ^ k *
        (∑ i, energy Q (cubeProjection Q k (fun x => v.grad x i))) ≤
      (1 - (Real.sqrt 3)⁻¹) * ∑' k,
        ((Real.sqrt 3)⁻¹ ^ k * lemmaVInverseDepthMax Q a k) *
          cubeAverage Q (blockPairingIntegrand a W W) := by
      apply mul_le_mul_of_nonneg_left _ hw1
      apply hleft.tsum_le_tsum _ (hsHist.mul_right _)
      intro k
      simpa only [← hv, mul_assoc] using
        mul_le_mul_of_nonneg_left
          (compatible_projectionEnergy_bound hEll W hWpot' hWsol hWmem k)
          (pow_nonneg hw k)
    _ = compatibleInverseHistory Q a * blockPairingAverage (openCubeSet Q) a W W := by
      have hAvg : cubeAverage Q (blockPairingIntegrand a W W) =
          blockPairingAverage (openCubeSet Q) a W W := by
        rw [cubeAverage_eq_integralAverage_openCubeSet]
        rfl
      rw [hAvg]
      unfold compatibleInverseHistory lemmaVInverseHistory
      rw [tsum_mul_right]
      ring

end
end Variational
