module

public import ASDExplicitGamma.Variational.LemmaVSobolev

/-! Weak column-divergence fields for the source localized shear. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section

/-- Column divergence of H r, where H=eta J. The sign is fixed by skew symmetry. -/
def localizedColumnProductDivergence {U : Set (Vec 2)} (η r : H1Function U) : Vec 2 → Vec 2 :=
  fun x => r.toFun x • lemmaVPlanarWeakColumnDivergence η x -
    η.toFun x • matVecMul responsePlanarJ (r.grad x)

 theorem localizedColumnProductDivergence_memL2 {U : Set (Vec 2)} (η r : H1Function U)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U)) :
    MemVectorL2 U (localizedColumnProductDivergence η r) := by
  have hb : MemVectorL2 U (fun x => r.toFun x • lemmaVPlanarWeakColumnDivergence η x) := by
    apply MemLp.of_eval
    intro i
    fin_cases i
    · simpa [lemmaVPlanarWeakColumnDivergence, matVecMul, responsePlanarJ, Fin.sum_univ_two] using
        r.memL2.fun_mul (hDη 1)
    · simpa [lemmaVPlanarWeakColumnDivergence, matVecMul, responsePlanarJ, Fin.sum_univ_two,
        Pi.neg_apply, volumeMeasureOn] using! (r.memL2.fun_mul (hDη 0)).neg
  exact hb.sub (lemmaVPlanar_skewGradient_memL2 r hη)

/-- Actual weak cancellation against every H1 test; no boundary condition on the test. -/
theorem localizedColumnProductDivergence_solenoidal {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeMeasureOn U)] (hU : IsOpenBoundedConvexDomain U)
    (η r : H1Function U) (hr : MemH10 U r.toFun)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U)) :
    IsSolenoidalZeroNormalTraceOn U (localizedColumnProductDivergence η r) := by
  obtain ⟨r0,hr0⟩ := hr
  have hg := lemmaV_H1_grad_eq_ae hU.isOpen hr0
  have hs := isSolenoidalZeroNormalTraceOn_smul
    (lemmaVPlanar_lift_cancellation hU r0 η hη hDη) (-1)
  intro w
  rw [← hs w]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  congr 1
  ext i
  simp only [localizedColumnProductDivergence, Pi.smul_apply, neg_one_smul,
    Pi.sub_apply, hr0, ← hx]
  ring

/-- The localized row differs from the global skew action by exactly the column divergence. -/
theorem localizedColumnProductDivergence_row_identity {U : Set (Vec 2)}
    (I : H1Function U →ₗ[ℝ] H1Function U) (η v : H1Function U) :
    (fun x => η.toFun x • matVecMul responsePlanarJ (v.grad x) +
      localizedColumnProductDivergence η (v-I v) x) = lemmaVPlanarRowField I η v := by
  funext x i
  fin_cases i <;>
    simp [localizedColumnProductDivergence, lemmaVPlanarRowField, lemmaVPlanarWeakColumnDivergence,
      H1Function.sub_grad, matVecMul, responsePlanarJ, Fin.sum_univ_two] <;> ring

end
end ASDExplicitGamma.Variational
