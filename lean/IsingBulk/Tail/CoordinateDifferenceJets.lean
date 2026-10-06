import IsingBulk.Analysis.JetsMultiindex
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Tactic

/-! Exact real coordinate jets of the polynomial pair-selection numerators. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets

theorem cutoffJet_linear_pow {N : ℕ} (L : (Fin N → ℝ) →L[ℝ] ℝ)
    (m : ℕ) (l : List (Fin N)) (u : Fin N → ℝ) :
    cutoffJet l (fun x => (L x)^m) u =
      ((m.descFactorial l.length : ℝ)*(l.map (fun i => L (Pi.single i 1))).prod)*
        (L u)^(m-l.length) := by
  induction l generalizing u with
  | nil => simp [cutoffJet]
  | cons i l ih =>
    have he : cutoffJet l (fun x => (L x)^m) =
        fun x => ((m.descFactorial l.length : ℝ)*(l.map (fun i => L (Pi.single i 1))).prod)*
          (L x)^(m-l.length) := funext ih
    rw [cutoffJet,he]
    dsimp only
    have hd := ((L.hasFDerivAt (x := u)).pow (m-l.length)).const_mul
      ((m.descFactorial l.length : ℝ)*(l.map (fun i => L (Pi.single i 1))).prod)
    rw [hd.fderiv]
    simp only [smul_apply,smul_eq_mul,nsmul_eq_mul,List.length_cons,
      List.map_cons,List.prod_cons,Nat.descFactorial_succ,Nat.cast_mul]
    have hn : m-(l.length+1)=(m-l.length)-1 := by omega
    rw [hn]
    ring

def coordinateDifference {N : ℕ} (p q : Fin N) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) p-
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) q

theorem cutoffJet_coordinate_difference_pow {N : ℕ} (p q : Fin N)
    (m : ℕ) (l : List (Fin N)) (u : Fin N → ℝ) :
    cutoffJet l (fun x => (x p-x q)^m) u =
      ((m.descFactorial l.length : ℝ)*
        (l.map (fun i => (if i=p then (1:ℝ) else 0)-(if i=q then (1:ℝ) else 0))).prod)*
          (u p-u q)^(m-l.length) := by
  simpa [coordinateDifference,Pi.single_apply,eq_comm] using
    cutoffJet_linear_pow (coordinateDifference p q) m l u

theorem coordinate_difference_jet_norm {N : ℕ} (p q : Fin N)
    (m : ℕ) (l : List (Fin N)) (u : Fin N → ℝ) :
    ‖cutoffJet l (fun x => (x p-x q)^m) u‖ ≤
      (m.descFactorial l.length : ℝ)*‖u p-u q‖^(m-l.length) := by
  let slope := fun i : Fin N => (if i=p then (1:ℝ) else 0)-(if i=q then (1:ℝ) else 0)
  have hs : ∀ i, ‖slope i‖ ≤ 1 := by
    intro i
    dsimp [slope]
    split_ifs <;> norm_num
  have hp : ‖(l.map slope).prod‖ ≤ 1 := by
    induction l with
    | nil => simp
    | cons i l ih =>
      rw [List.map_cons,List.prod_cons,norm_mul]
      calc
        _ ≤ 1*1 := mul_le_mul (hs i) ih (norm_nonneg _) (by norm_num)
        _ = 1 := by ring
  rw [cutoffJet_coordinate_difference_pow,norm_mul,norm_mul,norm_pow]
  have hc : ‖(m.descFactorial l.length : ℝ)‖=(m.descFactorial l.length : ℝ) := by simp
  rw [hc]
  change (m.descFactorial l.length : ℝ)*‖(l.map slope).prod‖*‖u p-u q‖^(m-l.length) ≤ _
  have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (m.descFactorial l.length) : (0:ℝ)≤_)
  have h2 := mul_le_mul_of_nonneg_right h (pow_nonneg (norm_nonneg (u p-u q)) (m-l.length))
  simpa only [mul_one] using h2

theorem coordinate_difference_jet_vanishes {N : ℕ} (p q : Fin N)
    (m : ℕ) (l : List (Fin N)) (u : Fin N → ℝ) (hm : m < l.length) :
    cutoffJet l (fun x => (x p-x q)^m) u=0 := by
  rw [cutoffJet_coordinate_difference_pow,Nat.descFactorial_eq_zero_iff_lt.mpr hm]
  simp

end
end IsingBulk.Tail
