module

public import ASDExplicitGamma.Numerics.Model.Q3Modes
public import Mathlib.Algebra.BigOperators.Ring.List

/-! A finite algebraic identity exposing the small positive covariance-difference charge. -/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model

noncomputable def listSum {α : Type*} (xs : List α) (f : α → ℝ) : ℝ := (xs.map f).sum

theorem list_sum_nil {α : Type*} (f : α → ℝ) : listSum [] f = 0 := rfl
theorem list_sum_cons {α : Type*} (x : α) (xs : List α) (f : α → ℝ) :
    listSum (x::xs) f = f x+listSum xs f := rfl

theorem list_sum_congr {α : Type*} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x = g x) : listSum xs f = listSum xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [list_sum_cons,list_sum_cons,h x (by simp),ih (by intro y hy; exact h y (by simp [hy]))]

theorem list_sum_add {α : Type*} (xs : List α) (f g : α → ℝ) :
    listSum xs (fun x => f x+g x) = listSum xs f+listSum xs g := by
  simp only [listSum,List.sum_map_add]
theorem list_sum_sub {α : Type*} (xs : List α) (f g : α → ℝ) :
    listSum xs (fun x => f x-g x) = listSum xs f-listSum xs g := by
  induction xs with
  | nil => simp only [list_sum_nil,sub_self]
  | cons x xs ih => simp only [list_sum_cons,ih]; ring
theorem list_sum_mul_left {α : Type*} (xs : List α) (f : α → ℝ) (a : ℝ) :
    listSum xs (fun x => a*f x) = a*listSum xs f := List.sum_map_mul_left _ _ _
theorem list_sum_mul_right {α : Type*} (xs : List α) (f : α → ℝ) (a : ℝ) :
    listSum xs (fun x => f x*a) = listSum xs f*a := List.sum_map_mul_right _ _ _

theorem list_sum_zero {α : Type*} (xs : List α) : listSum xs (fun _ => (0 : ℝ)) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [list_sum_cons,zero_add] using ih

theorem list_sum_le {α : Type*} (xs : List α) (f g : α → ℝ)
    (h : ∀ x ∈ xs, f x ≤ g x) : listSum xs f ≤ listSum xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [list_sum_cons,list_sum_cons]
    exact add_le_add (h x (by simp)) (ih (by intro y hy; exact h y (by simp [hy])))

theorem list_sum_nonneg {α : Type*} (xs : List α) (f : α → ℝ)
    (h : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ listSum xs f := by
  have hh := list_sum_le xs (fun _ => (0 : ℝ)) f h
  rwa [list_sum_zero] at hh

theorem list_sum_append {α : Type*} (xs ys : List α) (f : α → ℝ) :
    listSum (xs++ys) f = listSum xs f+listSum ys f := by
  simp only [listSum,List.map_append,List.sum_append]

theorem list_sum_flatMap {α β : Type*} (xs : List α) (f : α → List β) (g : β → ℝ) :
    listSum (xs.flatMap f) g = listSum xs (fun x => listSum (f x) g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,list_sum_append,list_sum_cons,ih]

theorem list_sum_comm {α β : Type*} (xs : List α) (ys : List β) (f : α → β → ℝ) :
    listSum xs (fun x => listSum ys (f x)) = listSum ys (fun y => listSum xs (fun x => f x y)) := by
  induction xs with
  | nil => simp only [list_sum_nil,list_sum_zero]
  | cons x xs ih => simp only [list_sum_cons,list_sum_add,ih]

theorem list_sum_range (N : ℕ) (f : ℕ → ℝ) : listSum (List.range N) f = ∑ n ∈ Finset.range N, f n := by
  induction N with
  | zero => rfl
  | succ N ih => simp only [List.range_succ,list_sum_append,list_sum_cons,list_sum_nil,
      add_zero,ih,Finset.sum_range_succ]

noncomputable def modeWeight (m n : ℕ) : ℝ :=
  ((m+1 : ℕ) : ℝ)^2/(((m+1 : ℕ) : ℝ)^2+((n+1 : ℕ) : ℝ)^2)

theorem mode_weight_symmetry (m n : ℕ) : modeWeight m n+modeWeight n m = 1 := by
  have hd : (0 : ℝ) < ((m+1 : ℕ) : ℝ)^2+((n+1 : ℕ) : ℝ)^2 := by positivity
  unfold modeWeight
  rw [add_comm (((n+1 : ℕ) : ℝ)^2),← add_div]
  exact div_self hd.ne'

theorem weighted_square_identity (xs : List ℕ) (f : ℕ → ℝ) :
    2*listSum xs (fun m => listSum xs (fun n => modeWeight m n*f m*f n)) = (listSum xs f)^2 := by
  let W := listSum xs (fun m => listSum xs (fun n => modeWeight m n*f m*f n))
  have hswap : W = listSum xs (fun m => listSum xs (fun n => modeWeight n m*f m*f n)) := by
    dsimp [W]
    rw [list_sum_comm]
    apply list_sum_congr
    intro m _
    apply list_sum_congr
    intro n _
    ring
  calc
    2*W = W+W := by ring
    _ = W+listSum xs (fun m => listSum xs (fun n => modeWeight n m*f m*f n)) := congrArg (fun z => W+z) hswap
    _ = listSum xs (fun m => listSum xs (fun n => (modeWeight m n+modeWeight n m)*f m*f n)) := by
      simp only [W,add_mul,list_sum_add]
    _ = listSum xs (fun m => listSum xs (fun n => f m*f n)) := by
      apply list_sum_congr
      intro m _
      apply list_sum_congr
      intro n _
      rw [mode_weight_symmetry,one_mul]
    _ = (listSum xs f)^2 := by
      simp only [list_sum_mul_left,list_sum_mul_right]
      ring

/-- Pair symmetry is algebraic; it does not enumerate any mode pairs in the kernel. -/
theorem projection_difference_identity (j N : ℕ) :
    q3Projection j N = (listSum (List.range N) (q3ModeSine j))^2-
      2*listSum (List.range N) (fun m => listSum (List.range N)
        (fun n => modeWeight m n*q3ModeDifference j m*q3ModeSine j n)) := by
  have h := weighted_square_identity (List.range N) (q3ModeSine j)
  have he : listSum (List.range N) (fun m => listSum (List.range N)
      (fun n => modeWeight m n*q3ModeDifference j m*q3ModeSine j n)) =
      listSum (List.range N) (fun m => listSum (List.range N)
        (fun n => modeWeight m n*q3ModeSine j m*q3ModeSine j n))-
      listSum (List.range N) (fun m => listSum (List.range N)
        (fun n => modeWeight m n*q3ModeCosine j m*q3ModeSine j n)) := by
    simp only [q3ModeDifference,mul_sub,sub_mul,list_sum_sub]
  rw [he]
  change 2*(∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
    modeWeight m n*q3ModeCosine j m*q3ModeSine j n) = _
  rw [← list_sum_range]
  have hh : (fun m => ∑ n ∈ Finset.range N, modeWeight m n*q3ModeCosine j m*q3ModeSine j n) =
      (fun m => listSum (List.range N) (fun n => modeWeight m n*q3ModeCosine j m*q3ModeSine j n)) := by
    funext m
    exact (list_sum_range N _).symm
  rw [hh]
  linarith only [h]

end ASDExplicitGamma.Numerics.Model
