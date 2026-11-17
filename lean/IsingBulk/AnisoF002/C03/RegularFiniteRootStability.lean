import IsingBulk.AnisoF002.C03.RegularQuadraticStability
import IsingBulk.AnisoF002.RegularTail.SinePair

/-!
# Finite physical-root product and Schur stability

These estimates keep every factor. The unmatched Schur entries grow by
only O(h/d), while the canceled matched pairs and one-body factors have
fixed relative costs. This is the complete finite algebra needed on the
protected mixed parameter disk.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped Topology BigOperators

theorem root_pair_product_change {r s R S : ℂ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1)
    (hR : ‖R - r‖ ≤ h) (hS : ‖S - s‖ ≤ h) : ‖R * S - r * s‖ ≤ 3 * h := by
  have hSn : ‖S‖ ≤ 1 + h := by
    have ht := norm_le_norm_sub_add S s
    linarith
  have he : R * S - r * s = (R - r) * S + r * (S - s) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have h1 := mul_le_mul hR hSn (norm_nonneg S) hh
  have h2 := mul_le_mul hr hS (norm_nonneg _) zero_le_one
  nlinarith

theorem root_pair_gap_half {r s R S : ℂ} {h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1)
    (hR : ‖R - r‖ ≤ h) (hS : ‖S - s‖ ≤ h)
    (hsmall : 6 * h ≤ ‖1 - r * s‖) :
    ‖1 - r * s‖ / 2 ≤ ‖1 - R * S‖ := by
  have hp := root_pair_product_change hh hh1 hr hs hR hS
  have ht := norm_le_norm_sub_add (1 - r * s) (1 - R * S)
  rw [show (1 - r * s) - (1 - R * S) = R * S - r * s by ring] at ht
  linarith

theorem schur_perturbed_norm_le {r s R S : ℂ} {h d : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) (hd : 0 < d)
    (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) (hR : ‖R - r‖ ≤ h) (hS : ‖S - s‖ ≤ h)
    (hgap : d ≤ ‖1 - r * s‖) (hsmall : 6 * h ≤ d) (hK : ‖schur r s‖ ≤ 1) :
    ‖schur R S‖ ≤ 1 + 10 * h / d := by
  have hold : 0 < ‖1 - r * s‖ := hd.trans_le hgap
  have hhalf := root_pair_gap_half hh hh1 hr hs hR hS (hsmall.trans hgap)
  have hnew : 0 < ‖1 - R * S‖ := (half_pos hold).trans_le hhalf
  have hnum : ‖r - s‖ ≤ ‖1 - r * s‖ := by
    rw [schur, norm_div] at hK
    exact (div_le_one hold).mp hK
  have hnnew : ‖R - S‖ ≤ ‖r - s‖ + 2 * h := by
    have he : R - S = (r - s) + ((R - r) - (S - s)) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_sub_le _ _).trans (by linarith)))
  have hp := root_pair_product_change hh hh1 hr hs hR hS
  have ht := norm_le_norm_sub_add (1 - r * s) (1 - R * S)
  rw [show (1 - r * s) - (1 - R * S) = R * S - r * s by ring] at ht
  have hsum : ‖R - S‖ ≤ ‖1 - R * S‖ + 5 * h := by linarith
  have hratio : 5 * h / ‖1 - R * S‖ ≤ 10 * h / d := by
    have hdnew : d / 2 ≤ ‖1 - R * S‖ := (div_le_div_of_nonneg_right hgap (by norm_num)).trans hhalf
    apply (div_le_div_of_nonneg_left (by positivity) (half_pos hd) hdnew).trans_eq
    ring
  rw [schur, norm_div]
  apply (div_le_div_of_nonneg_right hsum hnew.le).trans
  rw [add_div, div_self hnew.ne']
  exact add_le_add le_rfl hratio

theorem canceledPair_relative_bound {B r s R S y v : ℂ}
    (hR : ‖R‖ ≤ 2 * ‖r‖) (hS : ‖S‖ ≤ 2 * ‖s‖)
    (hd : ‖1 - r * s‖ / 2 ≤ ‖1 - R * S‖)
    (hold : 1 - r * s ≠ 0) (hy : y ≠ 0) (hv : v ≠ 0) :
    ‖canceledPair B R S y v‖ ≤ 16 * ‖canceledPair B r s y v‖ := by
  have hgap : 0 < ‖1 - r * s‖ := norm_pos_iff.mpr hold
  have hnew : 0 < ‖1 - R * S‖ := (half_pos hgap).trans_le hd
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  simp only [canceledPair, norm_div, norm_mul, norm_neg, norm_pow]
  have hnum : ‖B‖ * ‖y - v‖ ^ 2 * ‖R‖ * ‖S‖ ≤
      4 * (‖B‖ * ‖y - v‖ ^ 2 * ‖r‖ * ‖s‖) := by
    calc
      _ ≤ ‖B‖ * ‖y - v‖ ^ 2 * (2 * ‖r‖) * (2 * ‖s‖) := by gcongr
      _ = _ := by ring
  have hden : (‖y‖ * ‖v‖ * ‖1 - r * s‖ ^ 2) / 4 ≤
      ‖y‖ * ‖v‖ * ‖1 - R * S‖ ^ 2 := by
    have hsquare := (sq_le_sq₀ (half_pos hgap).le hnew.le).mpr hd
    have hh := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hyn.le hvn.le)
    convert hh using 1
    ring
  have hpos : 0 < (‖y‖ * ‖v‖ * ‖1 - r * s‖ ^ 2) / 4 := by positivity
  apply (div_le_div₀ (by positivity) hnum hpos hden).trans_eq
  field_simp
  ring

theorem oneBody_relative_bound {r R : ℂ}
    (hR : ‖R‖ ≤ 2 * ‖r‖) (hd : ‖1 - r ^ 2‖ / 2 ≤ ‖1 - R ^ 2‖)
    (hold : 1 - r ^ 2 ≠ 0) :
    ‖2 * R / (1 - R ^ 2)‖ ≤ 4 * ‖2 * r / (1 - r ^ 2)‖ := by
  have hgap : 0 < ‖1 - r ^ 2‖ := norm_pos_iff.mpr hold
  simp only [norm_div, norm_mul, Complex.norm_two]
  have hn : 2 * ‖R‖ ≤ 4 * ‖r‖ := by linarith
  apply (div_le_div₀ (by positivity) hn (half_pos hgap) hd).trans_eq
  field_simp

theorem list_prod_perturbation {α : Type*} (r R : α → ℂ) {h : ℝ} (hh : 0 ≤ h)
    (hr : ∀ a, ‖r a‖ ≤ 1) (hR : ∀ a, ‖R a - r a‖ ≤ h) (xs : List α) :
    ‖(xs.map R).prod - (xs.map r).prod‖ ≤ xs.length * h * (1 + h) ^ xs.length := by
  have hpbound (ys : List α) : ‖(ys.map r).prod‖ ≤ 1 := by
    induction ys with
    | nil => simp
    | cons b ys ih =>
        simp only [List.map_cons, List.prod_cons, norm_mul]
        simpa only [mul_one] using mul_le_mul (hr b) ih (norm_nonneg _) zero_le_one
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have hRa : ‖R a‖ ≤ 1 + h := by
        have ht := norm_le_norm_sub_add (R a) (r a)
        linarith [hr a, hR a]
      have hprod : ‖(xs.map r).prod‖ ≤ 1 := hpbound xs
      have he : R a * (xs.map R).prod - r a * (xs.map r).prod =
          R a * ((xs.map R).prod - (xs.map r).prod) + (R a - r a) * (xs.map r).prod := by ring
      simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [he]
      apply (norm_add_le _ _).trans
      rw [norm_mul, norm_mul]
      have h1 := mul_le_mul hRa ih (norm_nonneg _) (by positivity : 0 ≤ 1 + h)
      have h2 := mul_le_mul (hR a) hprod (norm_nonneg _) hh
      have hpow : 1 ≤ (1 + h) ^ (xs.length + 1) := one_le_pow₀ (by linarith)
      rw [pow_succ] at hpow ⊢
      nlinarith

theorem finite_prod_perturbation {N : ℕ} (r R : Fin N → ℂ) {h : ℝ} (hh : 0 ≤ h)
    (hr : ∀ i, ‖r i‖ ≤ 1) (hR : ∀ i, ‖R i - r i‖ ≤ h) :
    ‖(∏ i, R i) - (∏ i, r i)‖ ≤ N * h * (1 + h) ^ N := by
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_def, id_eq, List.length_ofFn] using
    list_prod_perturbation r R hh hr hR (List.ofFn id)

theorem one_add_pow_le_exp_one {h : ℝ} (hh : 0 ≤ h) (N : ℕ) (hNh : (N : ℝ) * h ≤ 1) :
    (1 + h) ^ N ≤ Real.exp 1 := by
  have hex : 1 + h ≤ Real.exp h := by simpa only [add_comm] using Real.add_one_le_exp h
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + h) hex N
  rw [← Real.exp_nat_mul] at hp
  exact hp.trans (Real.exp_le_exp.mpr hNh)

end
end IsingBulk.AnisoF002.RegularTail.C03
