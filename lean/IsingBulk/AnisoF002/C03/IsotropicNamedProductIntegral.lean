import IsingBulk.AnisoF002.C03.IsotropicAnchorPhysicalPeriodization
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product integration after eliminating the actual named anchor

The ordered physical weight is kept as a function of all labelled
angles. A measure-preserving constrained permutation eliminates its
named coordinate, and every other coordinate is integrated with the
literal independent Lebesgue measure. No symmetry of the weight is
assumed, and no square-root particle factor is introduced.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory

theorem namedAnchorAngles_continuous {n : ℕ} (i : Fin (n + 1)) (μ : ℝ) :
    Continuous (namedAnchorAngles i μ) :=
  continuous_pi fun k => (continuous_apply (Equiv.swap i (Fin.last n) k)).comp
    (centeredConstraintAngles_continuous μ)

theorem namedAnchorAngles_product_erase {n : ℕ} (i : Fin (n + 1)) (μ : ℝ)
    (f : ℝ → ℝ) (x : Fin n → ℝ) :
    (∏ k ∈ Finset.univ.erase i, f (namedAnchorAngles i μ x k)) = ∏ j, f (μ + x j) := by
  let G : Fin (n + 1) → ℝ := fun k => if k = i then 1 else f (namedAnchorAngles i μ x k)
  have hG : G i = 1 := by simp only [G, ite_eq_left rfl]
  calc
    _ = ∏ k ∈ Finset.univ.erase i, G k := by
      apply Finset.prod_congr rfl
      intro k hk
      simp only [G, ite_eq_right (Finset.ne_of_mem_erase hk)]
    _ = ∏ k, G k := Finset.prod_erase _ hG
    _ = ∏ k, G (Equiv.swap i (Fin.last n) k) := (Equiv.prod_comp _ G).symm
    _ = (∏ j : Fin n, f (μ + x j)) * 1 := by
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _
        have hne : Equiv.swap i (Fin.last n) j.castSucc ≠ i := by
          intro he
          have hj := (Equiv.swap i (Fin.last n)).injective
            (he.trans (Equiv.swap_apply_right i (Fin.last n)).symm)
          exact (Fin.castSucc_ne_last j) hj
        simp only [G, ite_eq_right hne, namedAnchorAngles_independent]
      · simp only [Equiv.swap_apply_right, hG]
    _ = _ := mul_one _

theorem named_rectangular_weight_zero_off_box {n : ℕ} (i : Fin (n + 1)) {L U μ : ℝ}
    {F : (Fin (n + 1) → ℝ) → ℂ}
    (hsupp : Function.support F ⊆ Icc (fun _ => L) (fun _ => U))
    {x : Fin n → ℝ} (hx : x ∉ Icc (fun _ => L - μ) (fun _ => U - μ)) :
    F (namedAnchorAngles i μ x) = 0 := by
  by_contra hn
  have hh := hsupp hn
  apply hx
  constructor
  · intro j
    have hj := hh.1 (Equiv.swap i (Fin.last n) j.castSucc)
    rw [namedAnchorAngles_independent] at hj
    linarith only [hj]
  · intro j
    have hj := hh.2 (Equiv.swap i (Fin.last n) j.castSucc)
    rw [namedAnchorAngles_independent] at hj
    linarith only [hj]

theorem translated_box_product_integral (n : ℕ) (L U μ : ℝ) (hLU : L ≤ U) (f : ℝ → ℝ) :
    (∫ x in Icc (fun _ : Fin n => L - μ) (fun _ => U - μ), ∏ j, f (μ + x j)) =
      (∫ t in Icc L U, f t) ^ n := by
  change (∫ x : Fin n → ℝ, ∏ j, f (μ + x j)
    ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict _) = _
  rw [← Set.pi_univ_Icc, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_pow (ι := Fin n) (fun t : ℝ => f (μ + t))]
  simp only [Fintype.card_fin]
  congr 1
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith only [hLU] : L - μ ≤ U - μ),
    intervalIntegral.integral_comp_add_left]
  simp only [add_sub_cancel]
  rw [intervalIntegral.integral_of_le hLU, integral_Icc_eq_integral_Ioc]

theorem named_anchor_product_integral_bound {n : ℕ} (i : Fin (n + 1)) (μ L U E A H : ℝ)
    (hLU : L ≤ U) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (F : (Fin (n + 1) → ℝ) → ℂ) (hF : Continuous F)
    (hsupp : Function.support F ⊆ Icc (fun _ => L) (fun _ => U))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (hH : (∫ t in Icc L U, f t) ≤ H)
    (hbound : ∀ θ ∈ Icc (fun _ => L) (fun _ => U),
      ‖F θ‖ ≤ E * A * ∏ k ∈ Finset.univ.erase i, f (θ k)) :
    Integrable (fun x : Fin n → ℝ => F (centeredConstraintAngles μ x)) ∧
      Integrable (fun x : Fin n → ℝ => F (namedAnchorAngles i μ x)) ∧
      ‖∫ x : Fin n → ℝ, F (centeredConstraintAngles μ x)‖ ≤ E * A * H ^ n := by
  let K := Icc (fun _ : Fin n => L - μ) (fun _ => U - μ)
  have hK : IsCompact K := isCompact_Icc
  have hc := hF.comp (centeredConstraintAngles_continuous μ)
  have hn := hF.comp (namedAnchorAngles_continuous i μ)
  have hcsupp : Function.support (fun x => F (centeredConstraintAngles μ x)) ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (centered_rectangular_weight_zero_off_box hsupp hxK)
  have hnsupp : Function.support (fun x => F (namedAnchorAngles i μ x)) ⊆ K := by
    intro x hx
    by_contra hxK
    exact hx (named_rectangular_weight_zero_off_box i hsupp hxK)
  have hcI := (integrableOn_iff_integrable_of_support_subset (μ := volume) hcsupp).mp
    (hc.continuousOn.integrableOn_compact (μ := volume) hK)
  have hnI := (integrableOn_iff_integrable_of_support_subset (μ := volume) hnsupp).mp
    (hn.continuousOn.integrableOn_compact (μ := volume) hK)
  refine ⟨hcI, hnI, ?_⟩
  rw [← namedAnchorAngles_integral i μ F,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => named_rectangular_weight_zero_off_box i hsupp hx)]
  have hpcont : Continuous (fun x : Fin n → ℝ => ∏ j, f (μ + x j)) :=
    continuous_finsetProd _ (fun j _ => hf.comp (continuous_const.add (continuous_apply j)))
  have hpI := hpcont.continuousOn.integrableOn_compact (μ := volume) hK
  calc
    _ ≤ ∫ x in K, ‖F (namedAnchorAngles i μ x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in K, E * A * ∏ j, f (μ + x j) := by
      apply integral_mono_ae (hnI.integrableOn.norm) (hpI.const_mul (E * A))
      filter_upwards [ae_restrict_mem hK.measurableSet] with x _
      by_cases hx : F (namedAnchorAngles i μ x) = 0
      · rw [hx, norm_zero]
        exact mul_nonneg (mul_nonneg hE hA) (Finset.prod_nonneg (fun j _ => hf0 (μ + x j)))
      · have hh := hbound _ (hsupp hx)
        rwa [namedAnchorAngles_product_erase] at hh
    _ = E * A * (∫ t in Icc L U, f t) ^ n := by
      rw [integral_const_mul, translated_box_product_integral n L U μ hLU f]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (integral_nonneg hf0) hH n) (mul_nonneg hE hA)

end IsingBulk.AnisoF002.Isotropic
