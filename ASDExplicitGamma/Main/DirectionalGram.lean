module

public import ASDExplicitGamma.Triadic.SensitivityWeakEnergy
public import ASDExplicitGamma.Triadic.TriadicProjection
public import ASDExplicitGamma.Triadic.VectorHaar
public import ASDExplicitGamma.Variational.LemmaVHaar
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Polarization of the actual order-`1/4` weak-Haar energy. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

private theorem main_weak_hair_pairing_summable
    (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    Summable (fun j : ℕ => (Real.sqrt 3)⁻¹ ^ j *
      pairing Q (cubeProjection Q j f) (cubeProjection Q j g)) := by
  have hq : 1 < Real.sqrt 3 := by
    simpa using (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) < 3))
  let w : ℝ := (Real.sqrt 3)⁻¹
  have hw : 0 ≤ w := by
    dsimp [w]
    positivity
  have hsF := summable_weighted_projections Q hq hf
  have hsG := summable_weighted_projections Q hq hg
  refine (hsF.add hsG).div_const 2 |>.of_norm_bounded ?_
  intro j
  let fₙ := cubeProjection Q j f
  let gₙ := cubeProjection Q j g
  let a := w ^ j * energy Q fₙ
  let b := w ^ j * energy Q gₙ
  have ha : 0 ≤ a := mul_nonneg (pow_nonneg hw j) (energy_nonneg Q fₙ)
  have hb : 0 ≤ b := mul_nonneg (pow_nonneg hw j) (energy_nonneg Q gₙ)
  let x := l2Norm Q fₙ
  let y := l2Norm Q gₙ
  have hx2 : x ^ 2 = energy Q fₙ := by
    dsimp [x, l2Norm]
    exact Real.sq_sqrt (energy_nonneg Q fₙ)
  have hy2 : y ^ 2 = energy Q gₙ := by
    dsimp [y, l2Norm]
    exact Real.sq_sqrt (energy_nonneg Q gₙ)
  have hxy : x * y ≤ (energy Q fₙ + energy Q gₙ) / 2 := by
    rw [← hx2, ← hy2]
    nlinarith [sq_nonneg (x - y)]
  have hpair := abs_pairing_le Q
    (projection_memLp Q j f 2) (projection_memLp Q j g 2)
  have hwj : 0 ≤ w ^ j := pow_nonneg hw j
  have hbound : ‖w ^ j * pairing Q fₙ gₙ‖ ≤ (a + b) / 2 := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hwj]
    calc
      w ^ j * |pairing Q fₙ gₙ| ≤ w ^ j * (x * y) :=
        mul_le_mul_of_nonneg_left hpair hwj
      _ ≤ w ^ j * ((energy Q fₙ + energy Q gₙ) / 2) :=
        mul_le_mul_of_nonneg_left hxy hwj
      _ = (a + b) / 2 := by
        dsimp [a, b]
        ring
  simpa [a, b, fₙ, gₙ, w, add_div] using hbound

/-- The polarized weak-Haar pairing whose diagonal is the actual weak energy. -/
noncomputable def mainWeakHaarPairing
    (Q : TriadicCube 2) (f g : Vec 2 → ℝ) : ℝ :=
  (1 - (Real.sqrt 3)⁻¹) *
    ∑' j : ℕ, (Real.sqrt 3)⁻¹ ^ j *
      pairing Q (cubeProjection Q j f) (cubeProjection Q j g)

theorem main_weak_hair_pairing_self_eq_dualEnergy
    (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    mainWeakHaarPairing Q f f = dualEnergy Q (Real.sqrt 3) f := by
  unfold mainWeakHaarPairing
  rw [dualEnergy_eq Q (by
    simpa using (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) < 3))) hf]
  congr 1

theorem main_weak_hair_pairing_comm
    (Q : TriadicCube 2) (f g : Vec 2 → ℝ) :
    mainWeakHaarPairing Q f g = mainWeakHaarPairing Q g f := by
  unfold mainWeakHaarPairing
  congr 1
  apply tsum_congr
  intro j
  rw [pairing_comm]

/-- The polarized weak-Haar pairing depends only on the fields on the cube. -/
theorem main_weak_hair_pairing_congr_ae
    (Q : TriadicCube 2) {f f' g g' : Vec 2 → ℝ}
    (hff : f =ᵐ[volume.restrict (cubeSet Q)] f')
    (hgg : g =ᵐ[volume.restrict (cubeSet Q)] g') :
    mainWeakHaarPairing Q f g = mainWeakHaarPairing Q f' g' := by
  have hf (j : ℕ) := lemmaV_cubeProjection_congr_ae Q j hff
  have hg (j : ℕ) := lemmaV_cubeProjection_congr_ae Q j hgg
  unfold mainWeakHaarPairing
  congr 1
  apply tsum_congr
  intro j
  rw [hf j, hg j]

private theorem main_pairing_add_left
    (Q : TriadicCube 2) {f g h : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    pairing Q (fun x => f x + g x) h = pairing Q f h + pairing Q g h := by
  simp only [pairing, cubeAverage_eq_integral_normalizedCubeMeasure, add_mul]
  exact integral_add (hf.integrable_mul hh) (hg.integrable_mul hh)

private theorem main_pairing_smul_left
    (Q : TriadicCube 2) {f h : Vec 2 → ℝ} (c : ℝ) :
    pairing Q (fun x => c * f x) h = c * pairing Q f h := by
  simp only [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  have hfun : (fun x => c * f x * h x) = fun x => c * (f x * h x) := by
    funext x
    ring
  rw [hfun, integral_const_mul]

theorem main_weak_hair_pairing_add_left
    (Q : TriadicCube 2) {f g h : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) :
    mainWeakHaarPairing Q (fun x => f x + g x) h =
      mainWeakHaarPairing Q f h + mainWeakHaarPairing Q g h := by
  have hsF := main_weak_hair_pairing_summable Q hf hh
  have hsG := main_weak_hair_pairing_summable Q hg hh
  have hterm (j : ℕ) :
      (Real.sqrt 3)⁻¹ ^ j *
          pairing Q (cubeProjection Q j (fun x => f x + g x))
            (cubeProjection Q j h) =
        (Real.sqrt 3)⁻¹ ^ j *
            pairing Q (cubeProjection Q j f) (cubeProjection Q j h) +
          (Real.sqrt 3)⁻¹ ^ j *
            pairing Q (cubeProjection Q j g) (cubeProjection Q j h) := by
    rw [projection_add Q j hf hg]
    rw [main_pairing_add_left Q
      (projection_memLp Q j f 2) (projection_memLp Q j g 2)
      (projection_memLp Q j h 2)]
    ring
  unfold mainWeakHaarPairing
  rw [show (fun j : ℕ => (Real.sqrt 3)⁻¹ ^ j *
      pairing Q (cubeProjection Q j (fun x => f x + g x))
        (cubeProjection Q j h)) = fun j =>
      (Real.sqrt 3)⁻¹ ^ j * pairing Q (cubeProjection Q j f)
          (cubeProjection Q j h) +
        (Real.sqrt 3)⁻¹ ^ j * pairing Q (cubeProjection Q j g)
          (cubeProjection Q j h) from funext hterm]
  rw [hsF.tsum_add hsG]
  ring

theorem main_weak_hair_pairing_smul_left
    (Q : TriadicCube 2) {f h : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hh : MemLp h 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    mainWeakHaarPairing Q (fun x => c * f x) h =
      c * mainWeakHaarPairing Q f h := by
  have hsF := main_weak_hair_pairing_summable Q hf hh
  have hterm (j : ℕ) :
      (Real.sqrt 3)⁻¹ ^ j *
          pairing Q (cubeProjection Q j (fun x => c * f x))
            (cubeProjection Q j h) =
        c * ((Real.sqrt 3)⁻¹ ^ j *
          pairing Q (cubeProjection Q j f) (cubeProjection Q j h)) := by
    rw [projection_smul]
    rw [main_pairing_smul_left Q c]
    ring
  unfold mainWeakHaarPairing
  rw [show (fun j : ℕ => (Real.sqrt 3)⁻¹ ^ j *
      pairing Q (cubeProjection Q j (fun x => c * f x))
        (cubeProjection Q j h)) = fun j => c *
      ((Real.sqrt 3)⁻¹ ^ j * pairing Q (cubeProjection Q j f)
        (cubeProjection Q j h)) from funext hterm]
  rw [hsF.tsum_mul_left c]
  ring

/-- The vector-valued pairing, summed over the physical coordinates. -/
noncomputable def mainVectorWeakHaarPairing
    (Q : TriadicCube 2) (F G : Vec 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, mainWeakHaarPairing Q (fun x => F x i) (fun x => G x i)

theorem main_vector_weak_hair_pairing_self_eq_energy
    (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    mainVectorWeakHaarPairing Q F F = vectorWeakHaarEnergy Q F := by
  unfold mainVectorWeakHaarPairing vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  exact main_weak_hair_pairing_self_eq_dualEnergy Q (hF i)

theorem main_vector_weak_hair_energy_congr_ae
    (Q : TriadicCube 2) {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hFG : F =ᵐ[volume.restrict (cubeSet Q)] G) :
    vectorWeakHaarEnergy Q F = vectorWeakHaarEnergy Q G := by
  unfold vectorWeakHaarEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply lemmaV_dualEnergy_congr_ae Q
    (by simpa using (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) < 3))) (hF i) (hG i)
  filter_upwards [hFG] with x hx
  exact congrFun hx i

theorem main_vector_weak_hair_pairing_comm
    (Q : TriadicCube 2) (F G : Vec 2 → Fin 2 → ℝ) :
    mainVectorWeakHaarPairing Q F G = mainVectorWeakHaarPairing Q G F := by
  unfold mainVectorWeakHaarPairing
  apply Finset.sum_congr rfl
  intro i hi
  exact main_weak_hair_pairing_comm Q (fun x => F x i) (fun x => G x i)

/-- The vector-valued pairing is invariant under changes on a cell-null set. -/
theorem main_vector_weak_hair_pairing_congr_ae
    (Q : TriadicCube 2) {F F' G G' : Vec 2 → Fin 2 → ℝ}
    (hFF : F =ᵐ[volume.restrict (cubeSet Q)] F')
    (hGG : G =ᵐ[volume.restrict (cubeSet Q)] G') :
    mainVectorWeakHaarPairing Q F G = mainVectorWeakHaarPairing Q F' G' := by
  unfold mainVectorWeakHaarPairing
  apply Finset.sum_congr rfl
  intro i hi
  exact main_weak_hair_pairing_congr_ae Q
    (hFF.mono fun x hx => congrFun hx i)
    (hGG.mono fun x hx => congrFun hx i)

theorem main_vector_weak_hair_pairing_add_left
    (Q : TriadicCube 2) {F G H : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    mainVectorWeakHaarPairing Q (fun x i => F x i + G x i) H =
      mainVectorWeakHaarPairing Q F H + mainVectorWeakHaarPairing Q G H := by
  unfold mainVectorWeakHaarPairing
  change (∑ i : Fin 2, mainWeakHaarPairing Q
      (fun x => F x i + G x i) (fun x => H x i)) = _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact main_weak_hair_pairing_add_left Q (hF i) (hG i) (hH i)

theorem main_vector_weak_hair_pairing_smul_left
    (Q : TriadicCube 2) {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    mainVectorWeakHaarPairing Q (fun x i => c * F x i) G =
      c * mainVectorWeakHaarPairing Q F G := by
  unfold mainVectorWeakHaarPairing
  change (∑ i : Fin 2, mainWeakHaarPairing Q
      (fun x => c * F x i) (fun x => G x i)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact main_weak_hair_pairing_smul_left Q (hF i) (hG i) c

/-- Right additivity for the vector-valued pairing. -/
theorem main_vector_weak_hair_pairing_add_right
    (Q : TriadicCube 2) {F G H : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hH : ∀ i, MemLp (fun x => H x i) 2 (normalizedCubeMeasure Q)) :
    mainVectorWeakHaarPairing Q F (fun x i => G x i + H x i) =
      mainVectorWeakHaarPairing Q F G + mainVectorWeakHaarPairing Q F H := by
  rw [main_vector_weak_hair_pairing_comm,
    main_vector_weak_hair_pairing_add_left Q hG hH hF,
    main_vector_weak_hair_pairing_comm Q G F,
    main_vector_weak_hair_pairing_comm Q H F]

/-- Right homogeneity for the vector-valued pairing. -/
theorem main_vector_weak_hair_pairing_smul_right
    (Q : TriadicCube 2) {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) (c : ℝ) :
    mainVectorWeakHaarPairing Q F (fun x i => c * G x i) =
      c * mainVectorWeakHaarPairing Q F G := by
  rw [main_vector_weak_hair_pairing_comm,
    main_vector_weak_hair_pairing_smul_left Q hG hF c,
    main_vector_weak_hair_pairing_comm Q G F]

/-- The quadratic form of a weak-Haar Gram matrix is exactly the weak-Haar
energy of the corresponding linear combination of its fields. -/
theorem main_vector_weak_hair_gram_quadratic_eq_energy
    (Q : TriadicCube 2) (F : Fin 2 → Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i k, MemLp (fun x => F i x k) 2 (normalizedCubeMeasure Q))
    (c : Fin 2 → ℝ) :
    dotProduct (star c) (Matrix.mulVec
        (fun i j => mainVectorWeakHaarPairing Q (F i) (F j)) c) =
      vectorWeakHaarEnergy Q (fun x k =>
        c 0 * F 0 x k + c 1 * F 1 x k) := by
  classical
  let F0 : Vec 2 → Fin 2 → ℝ := F 0
  let F1 : Vec 2 → Fin 2 → ℝ := F 1
  let G : Vec 2 → Fin 2 → ℝ := fun x k => c 0 * F0 x k + c 1 * F1 x k
  have hF0 (k : Fin 2) : MemLp (fun x => F0 x k) 2 (normalizedCubeMeasure Q) :=
    hF 0 k
  have hF1 (k : Fin 2) : MemLp (fun x => F1 x k) 2 (normalizedCubeMeasure Q) :=
    hF 1 k
  have hG (k : Fin 2) : MemLp (fun x => G x k) 2 (normalizedCubeMeasure Q) := by
    exact (hF0 k).const_mul (c 0) |>.add ((hF1 k).const_mul (c 1))
  have hG0 (k : Fin 2) :
      MemLp (fun x => c 0 * F0 x k) 2 (normalizedCubeMeasure Q) :=
    (hF0 k).const_mul (c 0)
  have hG1 (k : Fin 2) :
      MemLp (fun x => c 1 * F1 x k) 2 (normalizedCubeMeasure Q) :=
    (hF1 k).const_mul (c 1)
  have hExpand0 :
      mainVectorWeakHaarPairing Q F0 G =
        c 0 * mainVectorWeakHaarPairing Q F0 F0 +
          c 1 * mainVectorWeakHaarPairing Q F0 F1 := by
    change mainVectorWeakHaarPairing Q F0
        (fun x k => c 0 * F0 x k + c 1 * F1 x k) = _
    rw [main_vector_weak_hair_pairing_add_right Q hF0 hG0 hG1]
    rw [main_vector_weak_hair_pairing_smul_right Q hF0 hF0 (c 0),
      main_vector_weak_hair_pairing_smul_right Q hF0 hF1 (c 1)]
  have hExpand1 :
      mainVectorWeakHaarPairing Q F1 G =
        c 0 * mainVectorWeakHaarPairing Q F1 F0 +
          c 1 * mainVectorWeakHaarPairing Q F1 F1 := by
    change mainVectorWeakHaarPairing Q F1
        (fun x k => c 0 * F0 x k + c 1 * F1 x k) = _
    rw [main_vector_weak_hair_pairing_add_right Q hF1 hG0 hG1]
    rw [main_vector_weak_hair_pairing_smul_right Q hF1 hF0 (c 0),
      main_vector_weak_hair_pairing_smul_right Q hF1 hF1 (c 1)]
  have hPair :
      mainVectorWeakHaarPairing Q G G =
        c 0 * (c 0 * mainVectorWeakHaarPairing Q F0 F0 +
          c 1 * mainVectorWeakHaarPairing Q F0 F1) +
        c 1 * (c 0 * mainVectorWeakHaarPairing Q F1 F0 +
          c 1 * mainVectorWeakHaarPairing Q F1 F1) := by
    change mainVectorWeakHaarPairing Q
        (fun x k => c 0 * F0 x k + c 1 * F1 x k)
        (fun x k => c 0 * F0 x k + c 1 * F1 x k) = _
    rw [main_vector_weak_hair_pairing_add_left Q hG0 hG1 hG]
    rw [main_vector_weak_hair_pairing_smul_left Q hF0 hG (c 0),
      main_vector_weak_hair_pairing_smul_left Q hF1 hG (c 1),
      hExpand0, hExpand1]
  have hDot :
      dotProduct (star c) (Matrix.mulVec
          (fun i j => mainVectorWeakHaarPairing Q (F i) (F j)) c) =
        c 0 * (c 0 * mainVectorWeakHaarPairing Q F0 F0 +
          c 1 * mainVectorWeakHaarPairing Q F0 F1) +
        c 1 * (c 0 * mainVectorWeakHaarPairing Q F1 F0 +
          c 1 * mainVectorWeakHaarPairing Q F1 F1) := by
    simp [dotProduct, Matrix.mulVec, F0, F1, Fin.sum_univ_two,
      mul_add, mul_left_comm, mul_comm]
  calc
    dotProduct (star c) (Matrix.mulVec
        (fun i j => mainVectorWeakHaarPairing Q (F i) (F j)) c) =
        mainVectorWeakHaarPairing Q G G := hDot.trans hPair.symm
    _ = vectorWeakHaarEnergy Q G :=
      main_vector_weak_hair_pairing_self_eq_energy Q G hG
    _ = vectorWeakHaarEnergy Q (fun x k => c 0 * F 0 x k + c 1 * F 1 x k) := by
      rfl

/-- A finite Gram matrix of actual vector weak-Haar pairings is positive
semidefinite. The proof is the energy of the corresponding linear
combination, so no matrix-positivity hypothesis is introduced. -/
theorem main_vector_weak_hair_gram_matrix_posSemidef
    (Q : TriadicCube 2) (F : Fin 2 → Vec 2 → Fin 2 → ℝ)
    (hF : ∀ i k, MemLp (fun x => F i x k) 2 (normalizedCubeMeasure Q)) :
    Matrix.PosSemidef
      (fun i j => mainVectorWeakHaarPairing Q (F i) (F j)) := by
  classical
  let N : Matrix (Fin 2) (Fin 2) ℝ :=
    fun i j => mainVectorWeakHaarPairing Q (F i) (F j)
  change N.PosSemidef
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa [N] using main_vector_weak_hair_pairing_comm Q (F j) (F i)
  · intro c
    let F0 : Vec 2 → Fin 2 → ℝ := F 0
    let F1 : Vec 2 → Fin 2 → ℝ := F 1
    let G : Vec 2 → Fin 2 → ℝ := fun x k => c 0 * F0 x k + c 1 * F1 x k
    have hF0 (k : Fin 2) : MemLp (fun x => F0 x k) 2 (normalizedCubeMeasure Q) :=
      hF 0 k
    have hF1 (k : Fin 2) : MemLp (fun x => F1 x k) 2 (normalizedCubeMeasure Q) :=
      hF 1 k
    have hG (k : Fin 2) : MemLp (fun x => G x k) 2 (normalizedCubeMeasure Q) := by
      exact (hF0 k).const_mul (c 0) |>.add ((hF1 k).const_mul (c 1))
    have hG0 (k : Fin 2) :
        MemLp (fun x => c 0 * F0 x k) 2 (normalizedCubeMeasure Q) :=
      (hF0 k).const_mul (c 0)
    have hG1 (k : Fin 2) :
        MemLp (fun x => c 1 * F1 x k) 2 (normalizedCubeMeasure Q) :=
      (hF1 k).const_mul (c 1)
    have hExpand0 :
        mainVectorWeakHaarPairing Q F0 G =
          c 0 * mainVectorWeakHaarPairing Q F0 F0 +
            c 1 * mainVectorWeakHaarPairing Q F0 F1 := by
      change mainVectorWeakHaarPairing Q F0
          (fun x k => c 0 * F0 x k + c 1 * F1 x k) = _
      rw [main_vector_weak_hair_pairing_add_right Q hF0 hG0 hG1]
      rw [main_vector_weak_hair_pairing_smul_right Q hF0 hF0 (c 0),
        main_vector_weak_hair_pairing_smul_right Q hF0 hF1 (c 1)]
    have hExpand1 :
        mainVectorWeakHaarPairing Q F1 G =
          c 0 * mainVectorWeakHaarPairing Q F1 F0 +
            c 1 * mainVectorWeakHaarPairing Q F1 F1 := by
      change mainVectorWeakHaarPairing Q F1
          (fun x k => c 0 * F0 x k + c 1 * F1 x k) = _
      rw [main_vector_weak_hair_pairing_add_right Q hF1 hG0 hG1]
      rw [main_vector_weak_hair_pairing_smul_right Q hF1 hF0 (c 0),
        main_vector_weak_hair_pairing_smul_right Q hF1 hF1 (c 1)]
    have hPair :
        mainVectorWeakHaarPairing Q G G =
          c 0 * (c 0 * mainVectorWeakHaarPairing Q F0 F0 +
            c 1 * mainVectorWeakHaarPairing Q F0 F1) +
          c 1 * (c 0 * mainVectorWeakHaarPairing Q F1 F0 +
            c 1 * mainVectorWeakHaarPairing Q F1 F1) := by
      change mainVectorWeakHaarPairing Q
          (fun x k => c 0 * F0 x k + c 1 * F1 x k)
          (fun x k => c 0 * F0 x k + c 1 * F1 x k) = _
      rw [main_vector_weak_hair_pairing_add_left Q hG0 hG1 hG]
      rw [main_vector_weak_hair_pairing_smul_left Q hF0 hG (c 0),
        main_vector_weak_hair_pairing_smul_left Q hF1 hG (c 1),
        hExpand0, hExpand1]
    have hDot :
        dotProduct (star c) (Matrix.mulVec N c) =
          c 0 * (c 0 * mainVectorWeakHaarPairing Q F0 F0 +
            c 1 * mainVectorWeakHaarPairing Q F0 F1) +
          c 1 * (c 0 * mainVectorWeakHaarPairing Q F1 F0 +
            c 1 * mainVectorWeakHaarPairing Q F1 F1) := by
      simp [dotProduct, Matrix.mulVec, N, F0, F1, Fin.sum_univ_two,
        mul_add, mul_left_comm, mul_comm]
    calc
      0 ≤ vectorWeakHaarEnergy Q G :=
        vectorWeakHaarEnergy_nonneg Q G
      _ = mainVectorWeakHaarPairing Q G G :=
        (main_vector_weak_hair_pairing_self_eq_energy Q G hG).symm
      _ = dotProduct (star c) (Matrix.mulVec N c) :=
        hPair.trans hDot.symm

end ASDExplicitGamma.Main
