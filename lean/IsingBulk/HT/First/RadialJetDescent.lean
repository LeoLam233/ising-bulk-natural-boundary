import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Asymptotics.Defs

/-! Sharp descent from a simple-pole bound for an actual derivative chain.
A first integration costs a logarithm; the logarithm is integrable, so every
further lower derivative is bounded. No lower-jet conclusion is a premise. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology Interval

private theorem norm_le_anchor_add_majorant_integral {F G : ℝ → ℂ} {g : ℝ → ℝ}
    {epsilon a : ℝ} (he : 0 < epsilon) (hea : epsilon ≤ a)
    (hder : ∀ x ∈ Ioc 0 a, HasDerivAt F (G x) x)
    (hcont : ContinuousOn G (Ioc 0 a))
    (hbound : ∀ x ∈ Ioc 0 a, ‖G x‖ ≤ g x)
    (hg : IntervalIntegrable g volume epsilon a) :
    ‖F epsilon‖ ≤ ‖F a‖+∫ x in epsilon..a, g x := by
  have hsub : Icc epsilon a ⊆ Ioc 0 a := fun x hx => ⟨he.trans_le hx.1, hx.2⟩
  have hGi : IntervalIntegrable G volume epsilon a :=
    (hcont.mono hsub).intervalIntegrable_of_Icc hea
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hder x (hsub (by simpa only [uIcc_of_le hea] using hx))) hGi
  have hb := intervalIntegral.norm_integral_le_of_norm_le hea
    (Eventually.of_forall fun x hx => hbound x (hsub (Ioc_subset_Icc_self hx))) hg
  rw [hFTC] at hb
  calc
    ‖F epsilon‖ = ‖F a-(F a-F epsilon)‖ := by congr 1; ring
    _ ≤ ‖F a‖+‖F a-F epsilon‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl hb

/-- A derivative bounded by C/x gives the sharp logarithmic primitive bound. -/
theorem logarithmic_bound_of_derivative_inv {F G : ℝ → ℂ} {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C)
    (hder : ∀ x ∈ Ioc 0 a, HasDerivAt F (G x) x)
    (hcont : ContinuousOn G (Ioc 0 a))
    (hbound : ∀ x ∈ Ioc 0 a, ‖G x‖ ≤ C/x) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F x‖ ≤ B*(1+|Real.log x|) := by
  let B := ‖F a‖+C*|Real.log a|+C+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro x hx
  have hgi : IntervalIntegrable (fun t : ℝ => C/t) volume x a := by
    apply ContinuousOn.intervalIntegrable_of_Icc hx.2
    exact continuousOn_const.div continuousOn_id
      (fun t ht => (hx.1.trans_le ht.1).ne')
  have hh := norm_le_anchor_add_majorant_integral hx.1 hx.2 hder hcont hbound hgi
  have hi : (∫ t in x..a, C/t) = C*(Real.log a-Real.log x) := by
    simp only [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hx.1 ha,
      Real.log_div ha.ne' hx.1.ne']
  rw [hi] at hh
  have hlog : Real.log a-Real.log x ≤ |Real.log a|+|Real.log x| :=
    (sub_le_sub (le_abs_self _) (neg_abs_le _)).trans_eq (sub_neg_eq_add _ _)
  have hb := hh.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hC))
  have hbase : 0 ≤ ‖F a‖+C*|Real.log a| :=
    add_nonneg (norm_nonneg _) (mul_nonneg hC (abs_nonneg _))
  calc
    ‖F x‖ ≤ (‖F a‖+C*|Real.log a|)+C*|Real.log x| := by linarith [hb]
    _ ≤ B+B*|Real.log x| := add_le_add (by dsimp [B]; linarith)
      (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (abs_nonneg _))
    _ = B*(1+|Real.log x|) := by ring

/-- An integrable derivative majorant gives a bound uniform down to zero. -/
theorem bounded_of_derivative_integrable_majorant {F G : ℝ → ℂ} {g : ℝ → ℝ} {a : ℝ}
    (ha : 0 < a)
    (hder : ∀ x ∈ Ioc 0 a, HasDerivAt F (G x) x)
    (hcont : ContinuousOn G (Ioc 0 a))
    (hg : IntervalIntegrable g volume 0 a) (hg0 : ∀ x, 0 ≤ g x)
    (hbound : ∀ x ∈ Ioc 0 a, ‖G x‖ ≤ g x) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F x‖ ≤ B := by
  refine ⟨‖F a‖+|∫ t in (0:ℝ)..a, g t|+1,by positivity,?_⟩
  intro x hx
  have hsub : uIcc x a ⊆ uIcc 0 a := by
    rw [uIcc_of_le hx.2, uIcc_of_le ha.le]
    exact Icc_subset_Icc hx.1.le le_rfl
  have hh := norm_le_anchor_add_majorant_integral hx.1 hx.2 hder hcont hbound (hg.mono_set hsub)
  have hi := intervalIntegral.integral_mono_interval hx.1.le hx.2 le_rfl
    (Eventually.of_forall hg0) hg
  have hb := hh.trans (add_le_add le_rfl (hi.trans (le_abs_self _)))
  linarith

/-- In particular a logarithmic derivative bound has a bounded primitive. -/
theorem bounded_of_derivative_logarithmic {F G : ℝ → ℂ} {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C)
    (hder : ∀ x ∈ Ioc 0 a, HasDerivAt F (G x) x)
    (hcont : ContinuousOn G (Ioc 0 a))
    (hbound : ∀ x ∈ Ioc 0 a, ‖G x‖ ≤ C*(1+|Real.log x|)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F x‖ ≤ B := by
  apply bounded_of_derivative_integrable_majorant ha hder hcont _ _ hbound
  · exact ((intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 a).add
      (intervalIntegral.intervalIntegrable_log' : IntervalIntegrable Real.log volume 0 a).abs).const_mul C
  · intro x
    exact mul_nonneg hC (by positivity)

/-- A bounded derivative has a bounded primitive on the same finite interval. -/
theorem bounded_of_derivative_bounded {F G : ℝ → ℂ} {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C)
    (hder : ∀ x ∈ Ioc 0 a, HasDerivAt F (G x) x)
    (hcont : ContinuousOn G (Ioc 0 a))
    (hbound : ∀ x ∈ Ioc 0 a, ‖G x‖ ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F x‖ ≤ B :=
  bounded_of_derivative_integrable_majorant ha hder hcont intervalIntegrable_const
    (fun _ => hC) hbound

/-- Complete sharp lower-jet descent with a fixed unit tangent multiplier. -/
theorem sharp_lower_jets_of_top_inv_bound {F : ℕ → ℝ → ℂ} {v : ℂ}
    {a C : ℝ} {k : ℕ} (ha : 0 < a) (hC : 0 ≤ C) (hk : 2 ≤ k) (hv : ‖v‖=1)
    (hder : ∀ j : ℕ, ∀ x ∈ Ioc 0 a, HasDerivAt (F j) (v*F (j+1) x) x)
    (hTop : ∀ x ∈ Ioc 0 a, ‖F k x‖ ≤ C/x) :
    (∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F (k-1) x‖ ≤ B*(1+|Real.log x|)) ∧
    (∀ j : ℕ, j+1 < k → ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F j x‖ ≤ B) := by
  have hcont (j : ℕ) : ContinuousOn (fun x => v*F (j+1) x) (Ioc 0 a) := by
    intro x hx
    exact (continuousAt_const.mul (hder (j+1) x hx).continuousAt).continuousWithinAt
  have hlog := logarithmic_bound_of_derivative_inv ha hC (hder (k-1)) (hcont (k-1)) (by
    intro x hx
    rw [norm_mul, hv, one_mul, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    exact hTop x hx)
  refine ⟨hlog,?_⟩
  obtain ⟨B,hB,hb⟩ := hlog
  have hbase : ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F (k-2) x‖ ≤ B := by
    apply bounded_of_derivative_logarithmic ha hB.le (hder (k-2)) (hcont (k-2))
    intro x hx
    rw [norm_mul, hv, one_mul, show k-2+1=k-1 by omega]
    exact hb x hx
  have hstep (j : ℕ)
      (hh : ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F (j+1) x‖ ≤ B) :
      ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F j x‖ ≤ B := by
    obtain ⟨D,hD,hd⟩ := hh
    apply bounded_of_derivative_bounded ha hD.le (hder j) (hcont j)
    intro x hx
    rw [norm_mul, hv, one_mul]
    exact hd x hx
  have hdown (m : ℕ) : ∀ j : ℕ, j+m=k-2 →
      ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Ioc 0 a, ‖F j x‖ ≤ B := by
    induction m with
    | zero =>
        intro j hj
        have hj' : j=k-2 := by omega
        rw [hj']
        exact hbase
    | succ m ih =>
        intro j hj
        exact hstep j (ih (j+1) (by omega))
  intro j hj
  exact hdown (k-2-j) j (by omega)

/-- A proved simple-pole asymptotic supplies the uniform top-jet bound on
some actual positive interval, including a fixed anchor strictly inside it. -/
theorem inv_bound_of_simple_pole_asymptotic {F : ℝ → ℂ} {L : ℂ}
    (h : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun x => F x-(x:ℂ)⁻¹*L) (fun x => (x:ℂ)⁻¹)) :
    ∃ a C : ℝ, 0<a ∧ 0≤C ∧ ∀ x ∈ Ioc 0 a, ‖F x‖ ≤ C/x := by
  have he : ∀ᶠ x : ℝ in 𝓝[>] 0, ‖F x‖ ≤ (1+‖L‖)/x := by
    filter_upwards [h.eventuallyLE, self_mem_nhdsWithin] with x hx hx0
    have hnorm : ‖(x:ℂ)⁻¹‖=x⁻¹ := by
      rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    calc
      ‖F x‖ ≤ ‖F x-(x:ℂ)⁻¹*L‖+‖(x:ℂ)⁻¹*L‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖(x:ℂ)⁻¹‖+‖(x:ℂ)⁻¹*L‖ := add_le_add hx le_rfl
      _ = (1+‖L‖)/x := by rw [norm_mul, hnorm]; ring
  obtain ⟨d,hd,hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
  have hd' : 0 < d := hd
  refine ⟨d/2,1+‖L‖,by positivity,by positivity,?_⟩
  intro x hx
  exact hb ⟨hx.1, hx.2.trans_lt (by linarith)⟩

end
end IsingBulk.HT.First
