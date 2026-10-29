module

public import ASDExplicitGamma.Main.Q3RowCovariance
public import ASDExplicitGamma.Variational.LemmaVH2BandDirections

/-! Identifying the actual weak Sobolev jets used in the covariance row products. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational

/-- The genuine W^{2,∞} witness has the actual convolution jets in every source
coordinate; no smoothness or derivative identity is a premise. -/
theorem mainQ3DirectionW2_jet (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) (o : Q3SpatialJet) (x : Vec 2) :
    q3DirectionJet (mainQ3DirectionW2 Q b L u) o x =
      q3Convolution b L (mainQ3JetIndex o) u x := by
  cases o with
  | value => rfl
  | first i =>
    change (fderiv ℝ (q3Convolution b L h3Zero u) x) (basisVec i) = _
    rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
    congr 1
    fin_cases i <;> rfl
  | second i j =>
    change (fderiv ℝ (q3Convolution b L (h3Next h3Zero i (by decide)) u) x) (basisVec j) = _
    have ha : (h3Next h3Zero i (by decide)).1.1.val+
        (h3Next h3Zero i (by decide)).1.2.val ≤ 2 := by
      fin_cases i <;> norm_num [h3Next, h3Zero]
    rw [q3Convolution_fderiv_basis b L _ ha]
    congr 1
    fin_cases i <;> fin_cases j <;> rfl

/-- Actual weak q3 jets inherit the exact covariance Gram rows. -/
theorem mainQ3DirectionW2_jet_covariance {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (o p : Q3SpatialJet) (x : Vec 2) :
    HasSum (fun j => q3DirectionJet (mainQ3DirectionW2 Q b L (e j)) o x*
      q3DirectionJet (mainQ3DirectionW2 Q b L (e j)) p x)
      (q3ScaledJetCovariance (b^2) L.1 o p x x) := by
  simp_rw [mainQ3DirectionW2_jet]
  exact main_q3_jet_covariance e b L o p x

end ASDExplicitGamma.Main
