module

public import ASDExplicitGamma.Scalar.DefectResolventCarriers
public import ASDExplicitGamma.Triadic.HaarParseval
public import ASDExplicitGamma.Triadic.VectorHaar
public import ASDExplicitGamma.Variational.LemmaVHaar
public import Homogenization.Sobolev.Foundations.H10Graph

/-! A Hilbert carrier for the actual zero-trace potentials, with the weak
quarter-Haar energy as its norm. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators RealInnerProductSpace

noncomputable section

def weakHaarRho : ℝ := (Real.sqrt 3)⁻¹

private theorem weakHaarRho_nonneg : 0 ≤ weakHaarRho := by
  unfold weakHaarRho
  positivity

private theorem sqrt_weighted_projection_pairing_bound
    (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) (k : ℕ) :
    |weakHaarRho ^ k * pairing Q (cubeProjection Q k f) (cubeProjection Q k g)| ≤
      Real.sqrt (weakHaarRho ^ k * energy Q (cubeProjection Q k f)) *
        Real.sqrt (weakHaarRho ^ k * energy Q (cubeProjection Q k g)) := by
  let q := Real.sqrt 3
  have hq : 1 < q := by
    dsimp [q]
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hfk : MemLp (cubeProjection Q k f) 2 (normalizedCubeMeasure Q) :=
    projection_memLp Q k f 2
  have hgk : MemLp (cubeProjection Q k g) 2 (normalizedCubeMeasure Q) :=
    projection_memLp Q k g 2
  have hpair := abs_pairing_le Q hfk hgk
  have hrho : 0 ≤ weakHaarRho := weakHaarRho_nonneg
  have hweight : 0 ≤ weakHaarRho ^ k := pow_nonneg hrho _
  have hleft :
      |weakHaarRho ^ k * pairing Q (cubeProjection Q k f)
          (cubeProjection Q k g)| =
        weakHaarRho ^ k *
          |pairing Q (cubeProjection Q k f) (cubeProjection Q k g)| := by
    rw [abs_mul, abs_of_nonneg hweight]
  rw [hleft]
  have hnormf : l2Norm Q (cubeProjection Q k f) ^ 2 =
      energy Q (cubeProjection Q k f) := by
    rw [l2Norm, Real.sq_sqrt (energy_nonneg Q _)]
  have hnormg : l2Norm Q (cubeProjection Q k g) ^ 2 =
      energy Q (cubeProjection Q k g) := by
    rw [l2Norm, Real.sq_sqrt (energy_nonneg Q _)]
  have henergyf : 0 ≤ energy Q (cubeProjection Q k f) := energy_nonneg Q _
  have henergyg : 0 ≤ energy Q (cubeProjection Q k g) := energy_nonneg Q _
  have hnormf_nonneg : 0 ≤ l2Norm Q (cubeProjection Q k f) := by
    unfold l2Norm
    exact Real.sqrt_nonneg _
  have hnormg_nonneg : 0 ≤ l2Norm Q (cubeProjection Q k g) := by
    unfold l2Norm
    exact Real.sqrt_nonneg _
  calc
    weakHaarRho ^ k *
        |pairing Q (cubeProjection Q k f) (cubeProjection Q k g)| ≤
      weakHaarRho ^ k *
        (l2Norm Q (cubeProjection Q k f) * l2Norm Q (cubeProjection Q k g)) :=
          mul_le_mul_of_nonneg_left hpair hweight
    _ = Real.sqrt (weakHaarRho ^ k * energy Q (cubeProjection Q k f)) *
        Real.sqrt (weakHaarRho ^ k * energy Q (cubeProjection Q k g)) := by
      have hsqrtprod : Real.sqrt (weakHaarRho ^ k) *
          Real.sqrt (weakHaarRho ^ k) = weakHaarRho ^ k := by
        calc
          Real.sqrt (weakHaarRho ^ k) * Real.sqrt (weakHaarRho ^ k) =
              Real.sqrt (weakHaarRho ^ k) ^ 2 := by ring
          _ = weakHaarRho ^ k := Real.sq_sqrt hweight
      rw [Real.sqrt_mul hweight, Real.sqrt_mul hweight,
        ← hnormf, ← hnormg, Real.sqrt_sq_eq_abs,
        abs_of_nonneg hnormf_nonneg,
        Real.sqrt_sq_eq_abs,
        abs_of_nonneg hnormg_nonneg]
      calc
        weakHaarRho ^ k *
            (l2Norm Q (cubeProjection Q k f) * l2Norm Q (cubeProjection Q k g)) =
          (Real.sqrt (weakHaarRho ^ k) * Real.sqrt (weakHaarRho ^ k)) *
            (l2Norm Q (cubeProjection Q k f) * l2Norm Q (cubeProjection Q k g)) := by
              rw [hsqrtprod]
        _ = Real.sqrt (weakHaarRho ^ k) * l2Norm Q (cubeProjection Q k f) *
            (Real.sqrt (weakHaarRho ^ k) * l2Norm Q (cubeProjection Q k g)) := by ring

private theorem weakScalarPairing_summable
    (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    Summable (fun k => |weakHaarRho ^ k *
      pairing Q (cubeProjection Q k f) (cubeProjection Q k g)|) := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  let A : ℕ → ℝ := fun k => weakHaarRho ^ k *
    energy Q (cubeProjection Q k f)
  let B : ℕ → ℝ := fun k => weakHaarRho ^ k *
    energy Q (cubeProjection Q k g)
  have hA : Summable A := by
    simpa [A, weakHaarRho] using summable_weighted_projections Q hq hf
  have hB : Summable B := by
    simpa [B, weakHaarRho] using summable_weighted_projections Q hq hg
  have hAnonneg (k : ℕ) : 0 ≤ A k := by
    dsimp [A]
    exact mul_nonneg (pow_nonneg weakHaarRho_nonneg _) (energy_nonneg Q _)
  have hBnonneg (k : ℕ) : 0 ≤ B k := by
    dsimp [B]
    exact mul_nonneg (pow_nonneg weakHaarRho_nonneg _) (energy_nonneg Q _)
  apply summable_of_sum_le (fun k => abs_nonneg _)
  intro s
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun k => Real.sqrt (A k)) (fun k => Real.sqrt (B k))
  have hsumA : (∑ k ∈ s, (Real.sqrt (A k)) ^ 2) = ∑ k ∈ s, A k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact Real.sq_sqrt (hAnonneg k)
  have hsumB : (∑ k ∈ s, (Real.sqrt (B k)) ^ 2) = ∑ k ∈ s, B k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact Real.sq_sqrt (hBnonneg k)
  calc
    ∑ k ∈ s, |weakHaarRho ^ k *
        pairing Q (cubeProjection Q k f) (cubeProjection Q k g)| ≤
      ∑ k ∈ s, Real.sqrt (A k) * Real.sqrt (B k) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa [A, B] using sqrt_weighted_projection_pairing_bound Q hf hg k
    _ ≤ Real.sqrt (∑ k ∈ s, A k) * Real.sqrt (∑ k ∈ s, B k) := by
      simpa only [hsumA, hsumB] using hcs
    _ ≤ Real.sqrt (∑' k, A k) * Real.sqrt (∑' k, B k) := by
      apply mul_le_mul
      · exact Real.sqrt_le_sqrt (hA.sum_le_tsum s (fun k hk => hAnonneg k))
      · exact Real.sqrt_le_sqrt (hB.sum_le_tsum s (fun k hk => hBnonneg k))
      · exact Real.sqrt_nonneg _
      · exact Real.sqrt_nonneg _

/-- The scalar polarized weak-Haar form. -/
noncomputable def weakScalarPairing (Q : TriadicCube 2)
    (f g : Vec 2 → ℝ) : ℝ :=
  (1 - weakHaarRho) *
    ∑' k, weakHaarRho ^ k *
      pairing Q (cubeProjection Q k f) (cubeProjection Q k g)

private theorem normalized_ae_to_cube (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (h : f =ᵐ[normalizedCubeMeasure Q] g) : f =ᵐ[cubeMeasure Q] g := by
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  have h' : f =ᵐ[ENNReal.ofReal ((cubeVolume Q)⁻¹) • cubeMeasure Q] g := by
    simpa [normalizedCubeMeasure] using h
  exact (Measure.ae_ennreal_smul_measure_iff hc).1 h'

private theorem weakScalarPairing_congr_ae (Q : TriadicCube 2)
    {f f' g g' : Vec 2 → ℝ}
    (hf : f =ᵐ[normalizedCubeMeasure Q] f')
    (hg : g =ᵐ[normalizedCubeMeasure Q] g') :
    weakScalarPairing Q f g = weakScalarPairing Q f' g' := by
  have hfp (k : ℕ) : cubeProjection Q k f = cubeProjection Q k f' :=
    ASDExplicitGamma.Variational.lemmaV_cubeProjection_congr_ae Q k
      (normalized_ae_to_cube Q hf)
  have hgp (k : ℕ) : cubeProjection Q k g = cubeProjection Q k g' :=
    ASDExplicitGamma.Variational.lemmaV_cubeProjection_congr_ae Q k
      (normalized_ae_to_cube Q hg)
  unfold weakScalarPairing
  congr 1
  apply tsum_congr
  intro k
  rw [hfp k, hgp k]

private theorem weakScalarPairing_self (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    weakScalarPairing Q f f = dualEnergy Q (Real.sqrt 3) f := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hs := summable_weighted_projections Q hq hf
  rw [weakScalarPairing, dualEnergy_eq_weighted_projections Q hq hf hs]
  rfl

private theorem weakScalarPairing_symm (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    weakScalarPairing Q f g = weakScalarPairing Q g f := by
  have hfg := weakScalarPairing_summable Q hf hg
  have hgf := weakScalarPairing_summable Q hg hf
  simp only [weakScalarPairing]
  congr 1
  apply tsum_congr
  intro k
  rw [pairing_comm]

private theorem weakScalarPairing_add_left (Q : TriadicCube 2)
    {f g h : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    weakScalarPairing Q (fun x => f x + g x) h =
      weakScalarPairing Q f h + weakScalarPairing Q g h := by
  have hfh := weakScalarPairing_summable Q hf hh
  have hgh := weakScalarPairing_summable Q hg hh
  have hfgh := weakScalarPairing_summable Q (hf.add hg) hh
  have hfh' : Summable (fun k => weakHaarRho ^ k *
      pairing Q (cubeProjection Q k f) (cubeProjection Q k h)) := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using hfh
  have hgh' : Summable (fun k => weakHaarRho ^ k *
      pairing Q (cubeProjection Q k g) (cubeProjection Q k h)) := by
    apply Summable.of_norm
    simpa [Real.norm_eq_abs] using hgh
  simp only [weakScalarPairing]
  rw [← mul_add, ← hfh'.tsum_add hgh']
  congr 1
  apply tsum_congr
  intro k
  rw [projection_add Q k hf hg]
  have hp : pairing Q (fun x => cubeProjection Q k f x + cubeProjection Q k g x)
      (cubeProjection Q k h) =
      pairing Q (cubeProjection Q k f) (cubeProjection Q k h) +
        pairing Q (cubeProjection Q k g) (cubeProjection Q k h) := by
    unfold pairing
    rw [cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure,
      cubeAverage_eq_integral_normalizedCubeMeasure]
    calc
      (∫ x, (cubeProjection Q k f x + cubeProjection Q k g x) *
          cubeProjection Q k h x ∂normalizedCubeMeasure Q) =
        ∫ x, cubeProjection Q k f x * cubeProjection Q k h x +
          cubeProjection Q k g x * cubeProjection Q k h x
          ∂normalizedCubeMeasure Q := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = _ := integral_add
        ((projection_memLp Q k f 2).integrable_mul (projection_memLp Q k h 2))
        ((projection_memLp Q k g 2).integrable_mul (projection_memLp Q k h 2))
  rw [hp]
  ring

private theorem weakScalarPairing_smul_left (Q : TriadicCube 2)
    {f h : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    weakScalarPairing Q (fun x => c * f x) h =
      c * weakScalarPairing Q f h := by
  have hfh := weakScalarPairing_summable Q hf hh
  have hcfh := weakScalarPairing_summable Q (hf.const_mul c) hh
  simp only [weakScalarPairing]
  have hp (k : ℕ) : pairing Q (fun x => c * cubeProjection Q k f x)
      (cubeProjection Q k h) = c *
        pairing Q (cubeProjection Q k f) (cubeProjection Q k h) := by
    unfold pairing
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_eq_integral_normalizedCubeMeasure]
    calc
      (∫ x, (c * cubeProjection Q k f x) * cubeProjection Q k h x
          ∂normalizedCubeMeasure Q) =
        ∫ x, c * (cubeProjection Q k f x * cubeProjection Q k h x)
          ∂normalizedCubeMeasure Q := by
            apply integral_congr_ae
            filter_upwards [] with x
            ring
      _ = c * ∫ x, cubeProjection Q k f x * cubeProjection Q k h x
          ∂normalizedCubeMeasure Q := by rw [integral_const_mul]
  have hsum : (∑' k, weakHaarRho ^ k *
      pairing Q (cubeProjection Q k (fun x => c * f x))
        (cubeProjection Q k h)) =
      c * (∑' k, weakHaarRho ^ k *
        pairing Q (cubeProjection Q k f) (cubeProjection Q k h)) := by
    calc
      _ = ∑' k, c * (weakHaarRho ^ k *
          pairing Q (cubeProjection Q k f) (cubeProjection Q k h)) := by
        apply tsum_congr
        intro k
        rw [projection_smul, hp]
        ring
      _ = _ := tsum_mul_left
  rw [hsum]
  ring

/-- Weak-Haar pairing of vector fields, with the actual source quarter-discount. -/
noncomputable def weakVectorPairing (Q : TriadicCube 2)
    (F G : Vec 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, weakScalarPairing Q (fun x => F x i) (fun x => G x i)

private theorem weakVectorPairing_congr_ae (Q : TriadicCube 2)
    {F F' G G' : Vec 2 → Fin 2 → ℝ}
    (hF : F =ᵐ[normalizedCubeMeasure Q] F')
    (hG : G =ᵐ[normalizedCubeMeasure Q] G') :
    weakVectorPairing Q F G = weakVectorPairing Q F' G' := by
  unfold weakVectorPairing
  apply Finset.sum_congr rfl
  intro i hi
  apply weakScalarPairing_congr_ae Q
  · filter_upwards [hF] with x hx
    exact congrFun hx i
  · filter_upwards [hG] with x hx
    exact congrFun hx i

private theorem weakVectorPairing_self (Q : TriadicCube 2)
    {F : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    weakVectorPairing Q F F = vectorWeakHaarEnergy Q F := by
  unfold weakVectorPairing vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact weakScalarPairing_self Q (hF i)

private theorem weakVectorPairing_symm (Q : TriadicCube 2)
    {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    weakVectorPairing Q F G = weakVectorPairing Q G F := by
  unfold weakVectorPairing
  apply Finset.sum_congr rfl
  intro i hi
  exact weakScalarPairing_symm Q (hF i) (hG i)

private theorem weakVectorPairing_add_left (Q : TriadicCube 2)
    {F G H : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    weakVectorPairing Q (fun x i => F x i + G x i) H =
      weakVectorPairing Q F H + weakVectorPairing Q G H := by
  unfold weakVectorPairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact weakScalarPairing_add_left Q (hF i) (hG i) (hH i)

private theorem weakVectorPairing_smul_left (Q : TriadicCube 2)
    {F H : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    weakVectorPairing Q (fun x i => c * F x i) H =
      c * weakVectorPairing Q F H := by
  unfold weakVectorPairing
  calc
    ∑ i : Fin 2, weakScalarPairing Q (fun x => c * F x i)
        (fun x => H x i) =
      ∑ i : Fin 2, c * weakScalarPairing Q (fun x => F x i)
        (fun x => H x i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact weakScalarPairing_smul_left Q (hF i) (hH i) c
    _ = c * ∑ i : Fin 2, weakScalarPairing Q (fun x => F x i)
        (fun x => H x i) := by rw [Finset.mul_sum]

def graphPotentialField (Q : TriadicCube 2)
    (z : Homogenization.H10GraphClosedSpace (openCubeSet Q)) : Vec 2 → Vec 2 :=
  hilbertVectorL2ToVectorL2 (U := openCubeSet Q) z.val.2

private theorem graphPotentialField_add (Q : TriadicCube 2)
    (x y : Homogenization.H10GraphClosedSpace (openCubeSet Q)) :
    graphPotentialField Q (x + y) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun p => graphPotentialField Q x p + graphPotentialField Q y p := by
  change (hilbertVectorL2ToVectorL2 (U := openCubeSet Q)
      (x.val.2 + y.val.2)) =ᵐ[volumeMeasureOn (openCubeSet Q)] _
  rw [map_add]
  change (↑(hilbertVectorL2ToVectorL2 (U := openCubeSet Q) x.val.2 +
      hilbertVectorL2ToVectorL2 (U := openCubeSet Q) y.val.2) : Vec 2 → Vec 2) =ᵐ[volumeMeasureOn (openCubeSet Q)]
    (↑(hilbertVectorL2ToVectorL2 (U := openCubeSet Q) x.val.2) +
      ↑(hilbertVectorL2ToVectorL2 (U := openCubeSet Q) y.val.2))
  exact MeasureTheory.Lp.coeFn_add _ _

private theorem graphPotentialField_smul (Q : TriadicCube 2)
    (c : ℝ) (x : Homogenization.H10GraphClosedSpace (openCubeSet Q)) :
    graphPotentialField Q (c • x) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun p => c • graphPotentialField Q x p := by
  change (hilbertVectorL2ToVectorL2 (U := openCubeSet Q)
      (c • x.val.2)) =ᵐ[volumeMeasureOn (openCubeSet Q)] _
  rw [map_smul]
  change (↑(c • hilbertVectorL2ToVectorL2 (U := openCubeSet Q) x.val.2) :
      Vec 2 → Vec 2) =ᵐ[volumeMeasureOn (openCubeSet Q)]
    (c • ↑(hilbertVectorL2ToVectorL2 (U := openCubeSet Q) x.val.2))
  exact MeasureTheory.Lp.coeFn_smul c _

private theorem graphPotentialField_memLp (Q : TriadicCube 2)
    (z : Homogenization.H10GraphClosedSpace (openCubeSet Q)) :
    ∀ i : Fin 2, MemLp (fun x => graphPotentialField Q z x i) 2
      (normalizedCubeMeasure Q) := by
  have hvec : MemVectorL2 (openCubeSet Q) (graphPotentialField Q z) :=
    MeasureTheory.Lp.memLp _
  intro i
  exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hvec i)

private theorem raw_ae_to_normalized (Q : TriadicCube 2)
    {F G : Vec 2 → Vec 2}
    (h : F =ᵐ[volumeMeasureOn (openCubeSet Q)] G) :
    F =ᵐ[normalizedCubeMeasure Q] G := by
  have hmeasure : cubeMeasure Q = volumeMeasureOn (openCubeSet Q) := by
    rw [cubeMeasure, volumeMeasureOn]
    exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q
  have hcube : F =ᵐ[cubeMeasure Q] G := by
    rw [hmeasure]
    exact h
  rw [normalizedCubeMeasure]
  exact Measure.ae_smul_measure hcube (ENNReal.ofReal ((cubeVolume Q)⁻¹))

/-- The zero-trace H10 graph, endowed with the actual order-1/4 weak-Haar
inner product of its gradient coordinate. -/
def defectWeakPotential (Q : TriadicCube 2) :=
  ULift (Homogenization.H10GraphClosedSpace (openCubeSet Q))

instance instAddCommGroupDefectWeakPotential (Q : TriadicCube 2) :
    AddCommGroup (defectWeakPotential Q) :=
  inferInstanceAs (AddCommGroup (ULift
    (Homogenization.H10GraphClosedSpace (openCubeSet Q))))

instance instModuleDefectWeakPotential (Q : TriadicCube 2) :
    Module ℝ (defectWeakPotential Q) :=
  inferInstanceAs (Module ℝ (ULift
    (Homogenization.H10GraphClosedSpace (openCubeSet Q))))

def defectWeakPotentialInner (Q : TriadicCube 2)
    (x y : defectWeakPotential Q) : ℝ :=
  weakVectorPairing Q (graphPotentialField Q x.down)
    (graphPotentialField Q y.down)

theorem defectWeakPotential_inner_symm (Q : TriadicCube 2)
    (x y : defectWeakPotential Q) :
    defectWeakPotentialInner Q x y = defectWeakPotentialInner Q y x := by
  simp only [defectWeakPotentialInner]
  exact weakVectorPairing_symm Q
    (graphPotentialField_memLp Q x.down) (graphPotentialField_memLp Q y.down)

theorem defectWeakPotential_inner_nonneg (Q : TriadicCube 2)
    (x : defectWeakPotential Q) : 0 ≤ defectWeakPotentialInner Q x x := by
  rw [defectWeakPotentialInner]
  rw [weakVectorPairing_self Q (graphPotentialField_memLp Q x.down)]
  exact vectorWeakHaarEnergy_nonneg Q _

theorem defectWeakPotential_inner_add_left (Q : TriadicCube 2)
    (x y z : defectWeakPotential Q) :
    defectWeakPotentialInner Q (x + y) z =
      defectWeakPotentialInner Q x z + defectWeakPotentialInner Q y z := by
  have hdown : (x + y).down = x.down + y.down := rfl
  simp only [defectWeakPotentialInner]
  rw [hdown]
  calc
    weakVectorPairing Q (graphPotentialField Q (x.down + y.down))
        (graphPotentialField Q z.down) =
      weakVectorPairing Q
        (fun p => graphPotentialField Q x.down p + graphPotentialField Q y.down p)
        (graphPotentialField Q z.down) := by
          apply weakVectorPairing_congr_ae Q
          · exact raw_ae_to_normalized Q
              (graphPotentialField_add Q x.down y.down)
          · exact Filter.EventuallyEq.rfl
    _ = weakVectorPairing Q (graphPotentialField Q x.down)
          (graphPotentialField Q z.down) +
        weakVectorPairing Q (graphPotentialField Q y.down)
          (graphPotentialField Q z.down) :=
      weakVectorPairing_add_left Q
        (graphPotentialField_memLp Q x.down)
        (graphPotentialField_memLp Q y.down)
        (graphPotentialField_memLp Q z.down)

theorem defectWeakPotential_inner_smul_left (Q : TriadicCube 2)
    (x y : defectWeakPotential Q) (c : ℝ) :
    defectWeakPotentialInner Q (c • x) y =
      c * defectWeakPotentialInner Q x y := by
  have hdown : (c • x).down = c • x.down := rfl
  simp only [defectWeakPotentialInner]
  rw [hdown]
  calc
    weakVectorPairing Q (graphPotentialField Q (c • x.down))
        (graphPotentialField Q y.down) =
      weakVectorPairing Q
        (fun p => c • graphPotentialField Q x.down p)
        (graphPotentialField Q y.down) := by
          apply weakVectorPairing_congr_ae Q
          · exact raw_ae_to_normalized Q (graphPotentialField_smul Q c x.down)
          · exact Filter.EventuallyEq.rfl
    _ = c * weakVectorPairing Q (graphPotentialField Q x.down)
          (graphPotentialField Q y.down) := by
      change weakVectorPairing Q
          (fun p i => c * graphPotentialField Q x.down p i)
          (graphPotentialField Q y.down) = _
      exact weakVectorPairing_smul_left Q
        (graphPotentialField_memLp Q x.down)
        (graphPotentialField_memLp Q y.down) c

private theorem dualEnergy_zero_implies_energy_zero (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hdual : dualEnergy Q (Real.sqrt 3) f = 0) : energy Q f = 0 := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hprimal : primalEnergy Q (Real.sqrt 3)⁻¹ f = 0 := by
    simpa [dualEnergy] using hdual
  let A : ℕ → ℝ := fun k => (Real.sqrt 3)⁻¹ ^ (k + 1) *
    energy Q (cubeIncrement Q (k + 1) f)
  have hAs : Summable A := by
    simpa [A] using summable_dual_increments Q hq hf
  have hAnonneg (k : ℕ) : 0 ≤ A k := by
    dsimp [A]
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
      (energy_nonneg Q _)
  have hseries_nonneg : 0 ≤ ∑' k, A k := tsum_nonneg hAnonneg
  have hroot_nonneg : 0 ≤ energy Q (cubeIncrement Q 0 f) := energy_nonneg Q _
  have hroot : energy Q (cubeIncrement Q 0 f) = 0 := by
    change energy Q (cubeIncrement Q 0 f) + ∑' k, A k = 0 at hprimal
    linarith
  have htail : (∑' k, A k) = 0 := by
    change energy Q (cubeIncrement Q 0 f) + ∑' k, A k = 0 at hprimal
    linarith
  have hincrement (k : ℕ) : energy Q (cubeIncrement Q (k + 1) f) = 0 := by
    have hterm : A k ≤ ∑' n, A n := by
      calc
        A k = ∑ n ∈ ({k} : Finset ℕ), A n := by simp
        _ ≤ ∑' n, A n :=
          hAs.sum_le_tsum {k} (by intro n hn; exact hAnonneg n)
    have hAk_nonneg : 0 ≤ A k := hAnonneg k
    have hAk : A k = 0 := by linarith [hterm]
    have hweight : 0 < (Real.sqrt 3)⁻¹ ^ (k + 1) := by
      positivity
    dsimp [A] at hAk
    rcases mul_eq_zero.mp hAk with hw | he
    · exact (ne_of_gt hweight hw).elim
    · exact he
  have hincrementAll (k : ℕ) : energy Q (cubeIncrement Q k f) = 0 := by
    cases k with
    | zero => exact hroot
    | succ k => simpa using hincrement k
  calc
    energy Q f = ∑' k, energy Q (cubeIncrement Q k f) :=
      (tsum_cubeIncrement_energy Q hf).symm
    _ = ∑' k, 0 := tsum_congr hincrementAll
    _ = 0 := tsum_zero

private theorem energy_zero_ae' (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (henergy : energy Q f = 0) :
    f =ᵐ[normalizedCubeMeasure Q] 0 := by
  have hsquare : Integrable (fun x => f x ^ 2) (normalizedCubeMeasure Q) := by
    have hmul : Integrable (f * f) (normalizedCubeMeasure Q) := hf.integrable_mul hf
    have hfun : (fun x => f x ^ 2) = f * f := by
      funext x
      simp [pow_two, Pi.mul_apply]
    rw [hfun]
    exact hmul
  have hsquare_zero : (∫ x, f x ^ 2 ∂normalizedCubeMeasure Q) = 0 := by
    simpa [energy_eq_integral_sq] using henergy
  have hae_square :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x)) hsquare).mp hsquare_zero
  filter_upwards [hae_square] with x hx
  have hx' : f x ^ 2 = 0 := by simpa using hx
  nlinarith [hx']

private theorem rawCubeMeasure_eq_smul_normalized (Q : TriadicCube 2) :
    volumeMeasureOn (openCubeSet Q) =
      ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
  rw [volumeMeasureOn, ← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  rw [normalizedCubeMeasure, cubeMeasure, smul_smul]
  have hcoeff : ENNReal.ofReal (cubeVolume Q) *
      ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (cubeVolume_pos Q).le]
    rw [mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)), ENNReal.ofReal_one]
  rw [hcoeff, one_smul]

theorem defectWeakPotential_inner_definite (Q : TriadicCube 2)
    (x : defectWeakPotential Q)
    (hx : defectWeakPotentialInner Q x x = 0) : x = 0 := by
  let z := x.down
  let F := graphPotentialField Q z
  have hF : ∀ i : Fin 2, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) :=
    graphPotentialField_memLp Q z
  have hweak : vectorWeakHaarEnergy Q F = 0 := by
    simp only [defectWeakPotentialInner] at hx
    rw [weakVectorPairing_self Q hF] at hx
    exact hx
  have hcoordinate (i : Fin 2) : dualEnergy Q (Real.sqrt 3) (fun x => F x i) = 0 := by
    have hle : dualEnergy Q (Real.sqrt 3) (fun x => F x i) ≤
        ∑ j : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => F x j) := by
      simpa using (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin 2 => dualEnergy Q (Real.sqrt 3) (fun x => F x j))
        (fun j hj => dualEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) _)
        (Finset.mem_univ i))
    have hnonneg : 0 ≤ dualEnergy Q (Real.sqrt 3) (fun x => F x i) :=
      dualEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) _
    unfold vectorWeakHaarEnergy at hweak
    linarith
  have hcoordinateEnergy (i : Fin 2) : energy Q (fun x => F x i) = 0 :=
    dualEnergy_zero_implies_energy_zero Q (hF i) (hcoordinate i)
  have hcoordinateAE (i : Fin 2) :
      (fun x => F x i) =ᵐ[normalizedCubeMeasure Q] 0 :=
    energy_zero_ae' Q (hF i) (hcoordinateEnergy i)
  have hcoordinateRaw (i : Fin 2) :
      (fun x => F x i) =ᵐ[volumeMeasureOn (openCubeSet Q)] 0 := by
    rw [rawCubeMeasure_eq_smul_normalized Q]
    exact Measure.ae_smul_measure (hcoordinateAE i) (ENNReal.ofReal (cubeVolume Q))
  have hFraw : F =ᵐ[volumeMeasureOn (openCubeSet Q)] 0 := by
    filter_upwards [hcoordinateRaw 0, hcoordinateRaw 1] with y hy0 hy1
    ext i
    fin_cases i
    · exact hy0
    · exact hy1
  have hzGrad : z.val.2 = 0 := by
    have htoVec : hilbertVectorL2ToVectorL2
        (U := openCubeSet Q) z.val.2 = 0 := by
      apply MeasureTheory.Lp.ext
      filter_upwards [hFraw,
        MeasureTheory.Lp.coeFn_zero (E := Vec 2) (p := (2 : ENNReal))
          (μ := volumeMeasureOn (openCubeSet Q))] with y hy hzero
      have hFzero : (hilbertVectorL2ToVectorL2
          (U := openCubeSet Q) z.val.2) y = 0 := by
        simpa [F, graphPotentialField] using hy
      rw [hzero]
      exact hFzero
    have hback := congrArg (vectorL2ToHilbertVectorL2 (U := openCubeSet Q)) htoVec
    rw [vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2] at hback
    exact hback
  have hzmem : ((z.val.1, z.val.2) : ScalarL2 (openCubeSet Q) ×
      HilbertVectorL2 (openCubeSet Q)) ∈ h10GraphClosedSubmodule (openCubeSet Q) := z.property
  obtain ⟨C, hC, hPoincare⟩ := h10GraphClosedSubmodule_norm_value_le_of_isOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q) hzmem
  have hzNorm : ‖z.val.1‖ = 0 := by
    apply le_antisymm
    · simpa [hzGrad] using hPoincare
    · exact norm_nonneg _
  have hzVal : z.val.1 = 0 := norm_eq_zero.mp hzNorm
  have hz : z = 0 := by
    apply Subtype.ext
    change (z.val.1, z.val.2) = (0, 0)
    exact Prod.ext hzVal hzGrad
  apply ULift.ext
  exact hz

@[instance_reducible]
def defectWeakPotentialInnerCore (Q : TriadicCube 2) :
    InnerProductSpace.Core ℝ (defectWeakPotential Q) where
  inner := defectWeakPotentialInner Q
  conj_inner_symm := by
    intro x y
    change defectWeakPotentialInner Q y x = defectWeakPotentialInner Q x y
    exact (defectWeakPotential_inner_symm Q x y).symm
  re_inner_nonneg := by
    intro x
    change 0 ≤ defectWeakPotentialInner Q x x
    exact defectWeakPotential_inner_nonneg Q x
  add_left := defectWeakPotential_inner_add_left Q
  smul_left := defectWeakPotential_inner_smul_left Q
  definite := defectWeakPotential_inner_definite Q

instance instNormedAddCommGroupDefectWeakPotential (Q : TriadicCube 2) :
    NormedAddCommGroup (defectWeakPotential Q) :=
  (defectWeakPotentialInnerCore Q).toNormedAddCommGroup

instance instInnerProductSpaceDefectWeakPotential (Q : TriadicCube 2) :
    InnerProductSpace ℝ (defectWeakPotential Q) := by
  letI : InnerProductSpace.Core ℝ (defectWeakPotential Q) :=
    defectWeakPotentialInnerCore Q
  exact InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ
    (defectWeakPotential Q))

/-- Insert an actual global zero-trace potential into the weak-Haar graph
carrier. The graph pair retains both the scalar value and its genuine weak
gradient. -/
noncomputable def defectWeakPotentialOfH10 (Q : TriadicCube 2)
    (r : H10Function (openCubeSet Q)) : defectWeakPotential Q :=
  ULift.up ⟨(r.toH1Function.toScalarL2,
      r.toH1Function.gradToHilbertVectorL2),
    Submodule.le_topologicalClosure _ (h10_pair_mem_h10GraphSubmodule r)⟩

/-- The gradient represented by the graph carrier of an H10 potential is its
actual pointwise weak gradient, up to the volume-null identification. -/
theorem graphPotentialField_ofH10 (Q : TriadicCube 2)
    (r : H10Function (openCubeSet Q)) :
    graphPotentialField Q (defectWeakPotentialOfH10 Q r).down =ᵐ[
      volumeMeasureOn (openCubeSet Q)] r.toH1Function.grad := by
  change hilbertVectorL2ToVectorL2 (U := openCubeSet Q)
      r.toH1Function.gradToHilbertVectorL2 =ᵐ[
        volumeMeasureOn (openCubeSet Q)] r.toH1Function.grad
  filter_upwards [coeFn_hilbertVectorL2ToVectorL2
      (U := openCubeSet Q) r.toH1Function.gradToHilbertVectorL2,
    r.toH1Function.coeFn_gradToHilbertVectorL2] with x htransport hgrad
  rw [htransport, hgrad]
  rfl

/-- The same graph-gradient identification on the normalized cube measure
used by the weak-Haar pairing. -/
theorem graphPotentialField_ofH10_normalized (Q : TriadicCube 2)
    (r : H10Function (openCubeSet Q)) :
    graphPotentialField Q (defectWeakPotentialOfH10 Q r).down =ᵐ[
      normalizedCubeMeasure Q] r.toH1Function.grad :=
  raw_ae_to_normalized Q (graphPotentialField_ofH10 Q r)

/-- Recover the genuine H10 representative of a closed-graph weak potential.
The representative theorem for the closed H10 graph proves that every
carrier element is an actual potential, rather than an abstract completion
point. -/
noncomputable def defectWeakPotentialRepresentative (Q : TriadicCube 2)
    (x : defectWeakPotential Q) : H10Function (openCubeSet Q) :=
  Classical.choose (Homogenization.exists_h10Function_of_mem_h10GraphClosedSubmodule
    (U := openCubeSet Q) (isOpenBoundedConvexDomain_openCubeSet Q)
    (z := x.down.val) x.down.property)

/-- The scalar L2 value of the recovered potential is the value component of
the original closed-graph point. -/
theorem defectWeakPotentialRepresentative_value (Q : TriadicCube 2)
    (x : defectWeakPotential Q) :
    (defectWeakPotentialRepresentative Q x).toH1Function.toScalarL2 =
      x.down.val.1 :=
  (Classical.choose_spec (Homogenization.exists_h10Function_of_mem_h10GraphClosedSubmodule
    (U := openCubeSet Q) (isOpenBoundedConvexDomain_openCubeSet Q)
    (z := x.down.val) x.down.property)).1

/-- The weak gradient of the recovered potential is the gradient component
of the original closed-graph point. -/
theorem defectWeakPotentialRepresentative_gradient (Q : TriadicCube 2)
    (x : defectWeakPotential Q) :
    (defectWeakPotentialRepresentative Q x).toH1Function.gradToHilbertVectorL2 =
      x.down.val.2 :=
  (Classical.choose_spec (Homogenization.exists_h10Function_of_mem_h10GraphClosedSubmodule
    (U := openCubeSet Q) (isOpenBoundedConvexDomain_openCubeSet Q)
    (z := x.down.val) x.down.property)).2

/-- The graph-gradient field agrees almost everywhere with the recovered
H10 gradient. -/
theorem graphPotentialField_ofRepresentative (Q : TriadicCube 2)
    (x : defectWeakPotential Q) :
    graphPotentialField Q x.down =ᵐ[volumeMeasureOn (openCubeSet Q)]
      (defectWeakPotentialRepresentative Q x).toH1Function.grad := by
  have hgrad := defectWeakPotentialRepresentative_gradient Q x
  have hfield : hilbertVectorL2ToVectorL2 (U := openCubeSet Q) x.down.val.2 =
      hilbertVectorL2ToVectorL2 (U := openCubeSet Q)
        (defectWeakPotentialRepresentative Q x).toH1Function.gradToHilbertVectorL2 :=
    congrArg (hilbertVectorL2ToVectorL2 (U := openCubeSet Q)) hgrad.symm
  change hilbertVectorL2ToVectorL2 (U := openCubeSet Q) x.down.val.2 =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
    (defectWeakPotentialRepresentative Q x).toH1Function.grad
  have hfieldAE := MeasureTheory.Lp.ext_iff.mp hfield
  filter_upwards [hfieldAE,
    coeFn_hilbertVectorL2ToVectorL2 (U := openCubeSet Q)
      (f := (defectWeakPotentialRepresentative Q x).toH1Function.gradToHilbertVectorL2),
    (defectWeakPotentialRepresentative Q x).toH1Function.coeFn_gradToHilbertVectorL2]
      with y hy htransport hgradField
  rw [hy, htransport, hgradField]
  rfl

end
end ASDExplicitGamma.Scalar
