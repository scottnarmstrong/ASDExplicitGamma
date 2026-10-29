module

public import ASDExplicitGamma.Scalar.T4v2Cell
public import ASDExplicitGamma.Scalar.T4v2Mode
public import ASDExplicitGamma.Scalar.RefBudget2
public import ASDExplicitGamma.Scalar.PairFinalId

/-! T4 v2, part one: the pathwise identity `forcedLamR = σ⁻² · fwStar` on the mode set `S n`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Native MeasureTheory
open Algsuperdiff.Section3
open scoped InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

open scoped Classical in
/-- The set of white-basis modes occurring among the first `n` enumerated shell directions. -/
def t4v2S (n : ℕ) : Finset whiteBasisIndex :=
  (Finset.range n).biUnion (fun j => match eOpt j with | some l => {l} | none => ∅)

theorem t4v2_zero_energy (Q : TriadicCube 2) (F : Vec 2 → Vec 2)
    (h : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), F x = 0) :
    lemmaVTiledWeakEnergy Q 134 F = 0 := by
  have := t4v2_tiled_scale Q 0 (F := F) (G := fun _ : Vec 2 => (0 : Vec 2)) (by
    filter_upwards [h] with x hx
    simp [hx])
  simpa using this

namespace Cfg''

variable (C : Cfg'')

theorem t4v2_Hs (j : ℕ) :
    C.Hs j = match eOpt j with
      | some l => q3H3RangeValue C.a C.b C.c C.d C.β C.L
          (q3H3RangeFactor C.a C.b C.c C.d C.β C.L (whiteBasis l))
      | none => 0 := by
  unfold Hs q3H3Directions
  rw [enumerated_eq]
  cases eOpt j with
  | some l => rfl
  | none => simp

theorem t4v2_none_energy (hQ : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) (hj : C.Fl (C.Hs j) = 0) :
    lemmaVTiledWeakEnergy C.Q 134
        (rep'' C.nQ (potMap C.Q ((C.forcedR old j).ofLp.2 : HilbertVectorL2
          (openCubeSet C.Q)))).toH1Function.grad +
      lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.forcedR old j).ofLp.1).1 = 0 := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  have hf : C.forcedR old j = 0 := by
    rw [C.forcedR_eq hQ, hj]
    simp
  have hx : (C.forcedR old j).ofLp.2 = 0 := by rw [hf]; rfl
  have hy : (C.forcedR old j).ofLp.1 = 0 := by rw [hf]; rfl
  have hz0 : ∀ᵐ x ∂volumeMeasureOn (openCubeSet C.Q),
      hilbertVectorL2ToVectorL2 (0 : HilbertVectorL2 (openCubeSet C.Q)) x = 0 := by
    rw [map_zero]
    filter_upwards [Lp.coeFn_zero (E := Vec 2) 2 (volumeMeasureOn (openCubeSet C.Q))] with x h0
    simpa using h0
  have e1 : lemmaVTiledWeakEnergy C.Q 134
      (rep'' C.nQ (potMap C.Q ((C.forcedR old j).ofLp.2 : HilbertVectorL2
        (openCubeSet C.Q)))).toH1Function.grad = 0 := by
    apply t4v2_zero_energy
    have h1 := C.t4v2_pot_plain ((C.forcedR old j).ofLp.2)
    have h2 : ∀ᵐ x ∂volumeMeasureOn (openCubeSet C.Q), hilbertVectorL2ToVectorL2
        (((C.forcedR old j).ofLp.2 : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)) x = 0 := by
      rw [hx]
      simpa using hz0
    filter_upwards [h1, h2] with x a b
    rw [a]
    exact b
  have e2 : lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.forcedR old j).ofLp.1).1 = 0 := by
    apply t4v2_zero_energy
    change ∀ᵐ x ∂volumeMeasureOn (openCubeSet C.Q), (hilbertVectorL2ToVectorL2
      (C.forcedR old j).ofLp.1 : Vec 2 → Vec 2) x = 0
    rw [hy]
    exact hz0
  rw [e1, e2]; ring

end Cfg''

theorem t4v2_FwStar_sum {ι : Type*} (S : Finset ι) (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (depth : ℕ) (u : ι → H10Function (openCubeSet Q))
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2) (ω : Cutoff.CutoffSample 2) :
    fwStar S M m Q depth u Z ω = ∑ l ∈ S, fwStar {l} M m Q depth u Z ω := by
  simp [fwStar]

theorem t4v2_pathwise_gen {a b c d : ℝ} (hab : a < b) (hcd : c < d) (M : ABKModel 2) (h : ℝ)
    (m : ℤ) (e : Vec 2) (nQ : ℤ) (hk : nQ = m + 1 + 128)
    (hQcl : closure (openCubeSet (originCube 2 nQ)) ⊆ closedRectangle a b c d)
    (hQ : openCubeSet (originCube 2 nQ) ⊆ openRectangle a b c d)
    (ell : ℤ) (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell))
    (n : ℕ) (ω : Cutoff.CutoffSample 2) :
    (Cfg''.ofModel nQ hab hcd hQcl M h m e).forcedLamR n
        (olderField (closedRectangle a b c d) m ω) =
      (((Cfg''.ofModel nQ hab hcd hQcl M h m e).σ ^ 2)⁻¹) *
        fwStar (t4v2S n) M m (originCube 2 (m + 1 + 128)) 134
          (lambda8Q3ParentModePotential M h e (m + 1))
          (oldMaxFam M m (originCube 2 (m + 1 + 128))
            (lambda8Q3ParentModePotential M h e (m + 1))) ω := by
  subst hk
  classical
  set C := Cfg''.ofModel (m + 1 + 128) hab hcd hQcl M h m e with hC
  set Q' := originCube 2 (m + 1 + 128) with hQ'
  set u := lambda8Q3ParentModePotential M h e (m + 1) with hu
  set old := olderField (closedRectangle a b c d) m ω with hold
  -- per-mode term
  let T : ℕ → ℝ := fun j => lemmaVTiledWeakEnergy C.Q 134
        (rep'' C.nQ (potMap C.Q ((C.forcedR old j).ofLp.2 : HilbertVectorL2
          (openCubeSet C.Q)))).toH1Function.grad +
      lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.forcedR old j).ofLp.1).1
  have hsum : C.forcedLamR n old = ∑ j ∈ Finset.range n, T j := by
    unfold Cfg''.forcedLamR
    rw [← Finset.sum_add_distrib]
    exact Fin.sum_univ_eq_sum_range T n
  have hrest : C.Rest old = oldCutoffSkewCoefficient m Q' ω :=
    rest_old_eq M (closedRectangle a b c d) ell m hK C.Q C.hQcl ω
  have key : ∀ j ∈ Finset.range n, T j = (C.σ ^ 2)⁻¹ *
      ∑ l ∈ (match eOpt j with | some l => ({l} : Finset whiteBasisIndex) | none => ∅),
        fwStar {l} M m Q' 134 u (oldMaxFam M m Q' u) ω := by
    intro j _
    cases hj : eOpt j with
    | none =>
      have hH : C.Hs j = 0 := by rw [C.t4v2_Hs j, hj]
      have hF : C.Fl (C.Hs j) = 0 := by rw [hH, map_zero]
      have := C.t4v2_none_energy hQ old j hF
      change T j = (C.σ ^ 2)⁻¹ * ∑ l ∈ (∅ : Finset whiteBasisIndex),
        fwStar {l} M m Q' 134 u (oldMaxFam M m Q' u) ω
      rw [Finset.sum_empty, mul_zero]
      exact this
    | some l =>
      have hH : C.Hs j = q3H3RangeValue a b c d C.β C.L
          (q3H3RangeFactor a b c d C.β C.L (whiteBasis l)) := by
        rw [C.t4v2_Hs j, hj]
        rfl
      have hF : C.Fl (C.Hs j) = -(fwLoad C.Q (u l)) := by
        apply Subtype.ext
        have hcar := t4v2_mode_carrier Q' hab hcd hQ C.β C.L e l
        rw [hH]
        exact hcar
      have hmode := C.t4v2_mode_energy hQ old j (oldCutoffSkewCoefficient m Q' ω) hrest (u l) hF
        (oldMaxFam M m Q' u ω l) (oldMaxFam_spec M m Q' u ω l)
      have hcell := t4v2_cell_average M.nu (Annealed.sigmaBar M m : ℝ) Q'
        (oldCutoffSkewCoefficient m Q' ω) (oldMaxFam M m Q' u ω l)
        (fun x => (u l).toH1Function.grad x)
      have hFw : fwStar {l} M m Q' 134 u (oldMaxFam M m Q' u) ω =
          lemmaVTiledWeakEnergy Q' 134 (fun x j => (oldMaxFam M m Q' u ω l x).1 j -
              (u l).toH1Function.grad x j) +
            lemmaVTiledWeakEnergy Q' 134 (fun x => (scalarCoefficientFlux
              (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
                (oldCutoffSkewCoefficient m Q' ω)) (oldMaxFam M m Q' u ω l) x).2) := by
        unfold fwStar
        rw [Finset.sum_singleton]
        exact hcell
      change T j = (C.σ ^ 2)⁻¹ * ∑ l' ∈ ({l} : Finset whiteBasisIndex),
        fwStar {l'} M m Q' 134 u (oldMaxFam M m Q' u) ω
      rw [Finset.sum_singleton, hFw]
      exact hmode
  rw [hsum, Finset.sum_congr rfl key, ← Finset.mul_sum, t4v2_FwStar_sum]
  congr 1
  unfold t4v2S
  rw [Finset.sum_biUnion]
  intro j1 hj1 j2 hj2 hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro l hl1 hl2
  cases h1 : eOpt j1 with
  | none => simp [h1] at hl1
  | some l1 =>
    cases h2 : eOpt j2 with
    | none => simp [h2] at hl2
    | some l2 =>
      simp only [h1, Finset.mem_singleton] at hl1
      simp only [h2, Finset.mem_singleton] at hl2
      subst hl1
      subst hl2
      exact hne (eOpt_inj j1 j2 l h1 h2)

end

end ASDExplicitGamma.Scalar
