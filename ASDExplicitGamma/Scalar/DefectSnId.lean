module

public import ASDExplicitGamma.Scalar.DefectCfgId
public import ASDExplicitGamma.Scalar.DefectHMeas

/-! The Wick partial sum `s_n = S(z_n, z_n)` is the pair of the flux and potential slot sources
of the truncated Wick fields `F_n`, `G_n`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped InnerProductSpace BigOperators

noncomputable section

theorem psdDefectSource_coe_apply {Q : TriadicCube 2} {m n : ℕ}
    (B : Fin n → Fin n → TiledHaarField Q m) (x : Fin n → ℝ) (p : Vec 2) :
    (psdDefectSource B x).1 p = ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) • (B ij.1 ij.2).1 p := by
  unfold psdDefectSource
  rw [Fintype.sum_prod_type]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]

theorem psdDefectSource_neg {Q : TriadicCube 2} {m n : ℕ}
    (B : Fin n → Fin n → TiledHaarField Q m) (x : Fin n → ℝ) :
    psdDefectSource (fun i j => -B i j) x = -psdDefectSource B x := by
  unfold psdDefectSource
  simp [Finset.sum_neg_distrib]

theorem tiledPositiveEnergy_neg' (Q : TriadicCube 2) (m : ℕ) (a : TiledHaarField Q m) :
    tiledPositiveEnergy Q m (-a) = tiledPositiveEnergy Q m a := by
  unfold tiledPositiveEnergy
  exact tiled_positive_neg Q m a.1

theorem toLp_sum_prod {n : ℕ} {Y X : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (a : Fin n → Fin n → Y) (b : Fin n → Fin n → X) :
    ∑ i : Fin n, ∑ j : Fin n, (WithLp.toLp 2 (a i j, b i j) : WithLp 2 (Y × X)) =
      WithLp.toLp 2 (∑ ij : Fin n × Fin n, a ij.1 ij.2, ∑ ij : Fin n × Fin n, b ij.1 ij.2) := by
  refine WithLp.ofLp_injective 2 ?_
  rw [← Fintype.sum_prod_type' (f := fun i j => (WithLp.toLp 2 (a i j, b i j) : WithLp 2 (Y × X)))]
  ext <;> simp [WithLp.ofLp_sum, Prod.fst_sum, Prod.snd_sum]

namespace Cfg''

variable (C : Cfg'')

end Cfg''

end

end ASDExplicitGamma.Scalar
