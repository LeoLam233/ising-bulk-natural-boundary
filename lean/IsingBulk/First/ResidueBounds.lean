import IsingBulk.First.ResidueAlgebra

/-! All pole exclusions used on the actual closed polydisk are derived here. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

theorem one_sub_mul_ne_zero_of_norm_lt_one {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    1-a*b ≠ 0 := by
  intro h
  have he : a*b = 1 := (sub_eq_zero.mp h).symm
  have hlt : ‖a*b‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg a, norm_nonneg b]
  simp [he] at hlt

theorem coordinateProduct_norm_lt_one {N : ℕ} (hN : 0 < N) {x : Fin N → ℂ}
    (hx : ∀ i, ‖x i‖ < 1) : ‖coordinateProduct x‖ < 1 := by
  cases N with
  | zero => omega
  | succ n =>
    rw [coordinateProduct, Fin.prod_univ_succ, norm_mul]
    have ht : ‖∏ i : Fin n, x i.succ‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => (hx i.succ).le)
    have hh := hx 0
    nlinarith [norm_nonneg (x 0), norm_nonneg (∏ i : Fin n, x i.succ)]

theorem one_sub_coordinateProduct_ne_zero {N : ℕ} (hN : 0 < N) {x : Fin N → ℂ}
    (hx : ∀ i, ‖x i‖ < 1) : 1-coordinateProduct x ≠ 0 := by
  intro h
  have he : coordinateProduct x = 1 := (sub_eq_zero.mp h).symm
  have hlt := coordinateProduct_norm_lt_one hN hx
  simp [he] at hlt

theorem exterior_root_ne_on_disk {r : ℝ} {x z : ℂ} (hr : r < 1)
    (hx : ‖x‖ ≤ r) (hz : ‖z‖ < r) (hz0 : z ≠ 0) : x-z⁻¹ ≠ 0 := by
  intro he
  have hxz : x = z⁻¹ := sub_eq_zero.mp he
  have hmul : x*z = 1 := by rw [hxz, inv_mul_cancel₀ hz0]
  have hlt : ‖x*z‖ < 1 := by
    rw [norm_mul]
    have hx1 := hx.trans_lt hr
    have hz1 := hz.trans hr
    nlinarith [norm_nonneg x, norm_nonneg z]
  simp [hmul] at hlt

end
end IsingBulk.First
