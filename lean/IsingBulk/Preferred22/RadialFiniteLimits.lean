import IsingBulk.Preferred22.RadialLogImprovement
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The integrable inverse-square-root step in the last section of the
frozen manuscript. No value or analytic continuation at the boundary is
assumed. The finite limits are obtained from the actual radial fundamental
theorem of calculus and the continuity of an integrable primitive. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators Interval
set_option backward.isDefEq.respectTransparency false

/-- An integrable majorant for the next complex derivative gives a finite
radial limit of the preceding derivative. -/
theorem preferred_radial_limit_of_integrable_bound {R : ℂ → ℂ} {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) {a : ℝ} (ha : 0 < a) (j : ℕ)
    (hR : ∀ t : ℝ, 0 < t → t ≤ a → AnalyticAt ℂ R ((1+(t:ℂ))*ζ))
    {b : ℝ → ℝ} (hb : IntervalIntegrable b volume 0 a)
    (hnext : ∀ t : ℝ, 0 < t → t ≤ a →
      ‖iteratedDeriv (j+1) R ((1+(t:ℂ))*ζ)‖ ≤ b t) :
    ∃ L : ℂ, Tendsto (fun t : ℝ => iteratedDeriv j R ((1+(t:ℂ))*ζ))
      (𝓝[>] 0) (𝓝 L) := by
  let g : ℝ → ℂ := fun t => iteratedDeriv j R ((1+(t:ℂ))*ζ)
  let g' : ℝ → ℂ := fun t => ζ * iteratedDeriv (j+1) R ((1+(t:ℂ))*ζ)
  have hpath : Continuous (fun t : ℝ => (1+(t:ℂ))*ζ) := by fun_prop
  have hgd (t : ℝ) (ht : 0 < t) (hta : t ≤ a) : HasDerivAt g (g' t) t := by
    have hd := (IsingBulk.First.analyticAt_iteratedDeriv (hR t ht hta) j).differentiableAt.hasDerivAt
    have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (t:ℂ) := by
      simpa using ((hasDerivAt_id (t:ℂ)).const_add 1).mul_const ζ
    convert! (hd.comp (t:ℂ) hp).comp_ofReal using 1
    simp only [g',iteratedDeriv_succ,mul_comm]
  have hgc : ContinuousOn g' (Ioc 0 a) := by
    intro t ht
    have hc := (IsingBulk.First.analyticAt_iteratedDeriv (hR t ht.1 ht.2) (j+1)).continuousAt
    exact (continuousAt_const.mul
      (hc.comp (f := fun t : ℝ => (1+(t:ℂ))*ζ) (x := t) hpath.continuousAt)).continuousWithinAt
  have hgi : IntervalIntegrable g' volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le] at hb ⊢
    apply hb.mono' (hgc.aestronglyMeasurable measurableSet_Ioc)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [g',norm_mul,hζ,one_mul] using hnext t ht.1 ht.2
  have hprim : Tendsto (fun t : ℝ => ∫ x in t..a, g' x)
      (𝓝[>] 0) (𝓝 (∫ x in (0:ℝ)..a, g' x)) := by
    have hc := intervalIntegral.continuousOn_primitive_interval_left
      ((intervalIntegrable_iff').mp hgi)
    have hle : 𝓝[>] (0:ℝ) ≤ 𝓝[Set.uIcc 0 a] 0 := by
      refine le_inf nhdsWithin_le_nhds (le_principal_iff.mpr ?_)
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
      rw [uIcc_of_le ha.le]
      exact ⟨ht.le,hta.le⟩
    exact (hc 0 left_mem_uIcc).mono_left hle
  refine ⟨g a - ∫ x in (0:ℝ)..a, g' x,?_⟩
  apply (tendsto_const_nhds.sub hprim).congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
  have hi : IntervalIntegrable g' volume t a :=
    hgi.mono_set (by
      rw [uIcc_of_le hta.le,uIcc_of_le ha.le]
      exact Icc_subset_Icc ht.le le_rfl)
  have heq : (∫ x in t..a, g' x) = g a - g t :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => by
      rw [uIcc_of_le hta.le] at hx
      exact hgd x (ht.trans_le hx.1) hx.2) hi
  rw [heq]
  dsimp only [g]
  abel

/-- A finite square-root-scaled limit provides the actual inverse square
root bound on a positive radial interval. -/
theorem preferred_inverse_sqrt_bound_of_limit {f : ℝ → ℂ} {L : ℂ}
    (hlim : Tendsto (fun t : ℝ => Real.sqrt t • f t) (𝓝[>] 0) (𝓝 L)) :
    ∃ C a : ℝ, 0 < C ∧ 0 < a ∧ ∀ t : ℝ, 0 < t → t ≤ a →
      ‖f t‖ ≤ C / Real.sqrt t := by
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖Real.sqrt t • f t‖ < ‖L‖+1 :=
    hlim.norm.eventually (eventually_lt_nhds (lt_add_one ‖L‖))
  obtain ⟨a,ha,hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨‖L‖+1,a,by positivity,ha,?_⟩
  intro t ht hta
  have hh : ‖Real.sqrt t • f t‖ ≤ ‖L‖+1 := (show
    ‖Real.sqrt t • f t‖ < ‖L‖+1 from hbound ⟨ht,hta⟩).le
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg t)] at hh
  exact (le_div_iff₀ (Real.sqrt_pos.2 ht)).2 (by simpa only [mul_comm] using hh)

/-- The inverse square root is locally integrable at zero. The proof uses
the exact exponent -1/2, not a positive lower cutoff. -/
theorem preferred_intervalIntegrable_inverse_sqrt (C a : ℝ) (ha : 0 ≤ a) :
    IntervalIntegrable (fun t : ℝ => C / Real.sqrt t) volume 0 a := by
  have hi : IntervalIntegrable (fun t : ℝ => C * t ^ (-(1/2:ℝ))) volume 0 a :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1:ℝ) < -(1/2:ℝ))).const_mul C
  apply hi.congr
  intro t ht
  rw [uIoc_of_le ha] at ht
  dsimp only
  rw [Real.rpow_neg ht.1.le,← Real.sqrt_eq_rpow,div_eq_mul_inv]

/-- Every lower complex derivative has a finite radial limit when the top
derivative has the manuscript's square-root-scaled finite limit. -/
theorem preferred_lower_radial_limits_of_sqrt_limit {R : ℂ → ℂ} {ζ : ℂ}
    (hζ : ‖ζ‖ = 1)
    (hR : ∀ t : ℝ, 0 < t → AnalyticAt ℂ R ((1+(t:ℂ))*ζ))
    (k : ℕ) {L : ℂ}
    (hlim : Tendsto (fun t : ℝ => Real.sqrt t •
      iteratedDeriv k R ((1+(t:ℂ))*ζ)) (𝓝[>] 0) (𝓝 L)) :
    ∀ j : ℕ, j < k → ∃ Lj : ℂ,
      Tendsto (fun t : ℝ => iteratedDeriv j R ((1+(t:ℂ))*ζ)) (𝓝[>] 0) (𝓝 Lj) := by
  induction k generalizing L with
  | zero => intro j hj; omega
  | succ k ih =>
    obtain ⟨C,a,_hC,ha,hbound⟩ := preferred_inverse_sqrt_bound_of_limit hlim
    obtain ⟨Lk,hLk⟩ := preferred_radial_limit_of_integrable_bound hζ ha k
      (fun t ht _ => hR t ht) (preferred_intervalIntegrable_inverse_sqrt C a ha.le) hbound
    intro j hj
    by_cases heq : j = k
    · subst j
      exact ⟨Lk,hLk⟩
    · have hs : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
        simpa using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
      have hk : Tendsto (fun t : ℝ => Real.sqrt t •
          iteratedDeriv k R ((1+(t:ℂ))*ζ)) (𝓝[>] 0) (𝓝 0) := by
        simpa using hs.smul hLk
      exact ih hk j (by omega)

/-- The finite lower limits imply the explicitly stated uniform lower
derivative bounds on a sufficiently short radial interval. -/
theorem preferred_lower_radial_bounds_of_sqrt_limit {R : ℂ → ℂ} {ζ : ℂ}
    (hζ : ‖ζ‖ = 1)
    (hR : ∀ t : ℝ, 0 < t → AnalyticAt ℂ R ((1+(t:ℂ))*ζ))
    (k : ℕ) {L : ℂ}
    (hlim : Tendsto (fun t : ℝ => Real.sqrt t •
      iteratedDeriv k R ((1+(t:ℂ))*ζ)) (𝓝[>] 0) (𝓝 L)) :
    ∀ j : ℕ, j < k → ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ t : ℝ, 0 < t → t ≤ a → ‖iteratedDeriv j R ((1+(t:ℂ))*ζ)‖ ≤ C := by
  intro j hj
  obtain ⟨Lj,hLj⟩ := preferred_lower_radial_limits_of_sqrt_limit hζ hR k hlim j hj
  have hev : ∀ᶠ (t : ℝ) in 𝓝[>] (0:ℝ), ‖iteratedDeriv j R ((1+(t:ℂ))*ζ)‖ < ‖Lj‖+1 :=
    hLj.norm.eventually (eventually_lt_nhds (lt_add_one ‖Lj‖))
  obtain ⟨a,ha,hbound⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  refine ⟨‖Lj‖+1,a,by positivity,ha,?_⟩
  intro t ht hta
  exact (show ‖iteratedDeriv j R ((1+(t:ℂ))*ζ)‖ < ‖Lj‖+1 from hbound ⟨ht,hta⟩).le

end
end IsingBulk.Preferred22
