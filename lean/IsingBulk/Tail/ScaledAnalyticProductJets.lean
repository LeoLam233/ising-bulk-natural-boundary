import IsingBulk.Analysis.JetsNormBounds

namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [DecidableEq ι]

theorem analytic_finset_product_geometric_jets (s : Finset ι) (f : ι → E → ℂ)
    (x : E) (J : ℕ) (V L : ℝ) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (ha : ∀ i ∈ s, AnalyticAt ℂ (f i) x)
    (hb : ∀ i ∈ s, ∀ k ≤ J, ‖iteratedFDeriv ℂ k (f i) x‖ ≤ V * L^k) :
    ∀ k ≤ J, ‖iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      V^s.card * ((s.card : ℝ)*L)^k := by
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    cases k with
    | zero => simp
    | succ k => simp [iteratedFDeriv_succ_const]
  | @insert a s has ih =>
    have haS : ∀ i ∈ s, AnalyticAt ℂ (f i) x := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hbS : ∀ i ∈ s, ∀ k ≤ J, ‖iteratedFDeriv ℂ k (f i) x‖ ≤ V*L^k :=
      fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hp : AnalyticAt ℂ (fun y => ∏ i ∈ s, f i y) x :=
      Finset.analyticAt_fun_prod s (fun i hi => haS i hi)
    intro k hk
    simp only [Finset.prod_insert has, Finset.card_insert_of_notMem has, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ∑ r ∈ Finset.range (k+1), (k.choose r : ℝ) *
          ‖iteratedFDeriv ℂ r (f a) x‖ *
          ‖iteratedFDeriv ℂ (k-r) (fun y => ∏ i ∈ s, f i y) x‖ :=
        IsingBulk.Jets.analytic_product_jet_bound _ _ x k (ha a (Finset.mem_insert_self _ _)) hp
      _ ≤ ∑ r ∈ Finset.range (k+1), (k.choose r : ℝ) * (V*L^r) *
          (V^s.card * ((s.card:ℝ)*L)^(k-r)) := by
        apply Finset.sum_le_sum
        intro r hr
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hb a (Finset.mem_insert_self _ _) r
            ((Nat.le_of_lt_succ (Finset.mem_range.mp hr)).trans hk)) (by positivity)
        · exact ih haS hbS (k-r) ((Nat.sub_le _ _).trans hk)
        · exact norm_nonneg _
        · positivity
      _ = V^(s.card+1) * (L + (s.card:ℝ)*L)^k := by
        rw [add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        rw [pow_succ]
        ring
      _ = _ := by congr 2; ring

/-- Positive scale algebra; only the fixed scale is inverted, never a factor. -/
lemma scaled_jet_power_identity (q : ℝ) (hq : 0 < q) (a : ℤ) (k : ℕ) :
    q^a * (q⁻¹)^k = q^(a-(k:ℤ)) := by
  rw [zpow_sub₀ (ne_of_gt hq)]
  simp [div_eq_mul_inv]

/-- A finite product preserves the exact total scale degree of its factors. -/
theorem analytic_finset_product_scaled_jets (s : Finset ι) (f : ι → E → ℂ)
    (x : E) (J : ℕ) (C q : ℝ) (a : ℤ) (hC : 0 ≤ C) (hq : 0 < q)
    (ha : ∀ i ∈ s, AnalyticAt ℂ (f i) x)
    (hb : ∀ i ∈ s, ∀ k ≤ J,
      ‖iteratedFDeriv ℂ k (f i) x‖ ≤ C * q^(a-(k:ℤ))) :
    ∀ k ≤ J, ‖iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      C^s.card * (s.card : ℝ)^k * q^(a*(s.card:ℤ)-(k:ℤ)) := by
  intro k hk
  have hb' : ∀ i ∈ s, ∀ r ≤ J,
      ‖iteratedFDeriv ℂ r (f i) x‖ ≤ (C*q^a)*(q⁻¹)^r := by
    intro i hi r hr
    simpa only [mul_assoc, scaled_jet_power_identity q hq] using hb i hi r hr
  have h := analytic_finset_product_geometric_jets s f x J (C*q^a) q⁻¹
    (by positivity) (by positivity) ha hb' k hk
  have he : (q^a)^s.card * (q⁻¹)^k = q^(a*(s.card:ℤ)-(k:ℤ)) := by
    rw [← zpow_natCast (q^a) s.card, ← zpow_mul]
    exact scaled_jet_power_identity q hq _ k
  convert h using 1
  simp only [mul_pow]
  rw [← he]
  ring

/-- Degree-one factors with derivative cost C lose only one scale per derivative. -/
theorem analytic_finset_product_contraction_jets (s : Finset ι) (f : ι → E → ℂ)
    (x : E) (J : ℕ) (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q)
    (ha : ∀ i ∈ s, AnalyticAt ℂ (f i) x)
    (hb : ∀ i ∈ s, ∀ k ≤ J,
      ‖iteratedFDeriv ℂ k (f i) x‖ ≤ C^k * q^(1-(k:ℤ))) :
    ∀ k ≤ J, ‖iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      C^k * (s.card : ℝ)^k * q^((s.card:ℤ)-(k:ℤ)) := by
  intro k hk
  have hb' : ∀ i ∈ s, ∀ r ≤ J,
      ‖iteratedFDeriv ℂ r (f i) x‖ ≤ q*(C*q⁻¹)^r := by
    intro i hi r hr
    have he := scaled_jet_power_identity q hq 1 r
    simp only [zpow_one] at he
    calc
      _ ≤ C^r*q^(1-(r:ℤ)) := hb i hi r hr
      _ = q*(C*q⁻¹)^r := by rw [← he, mul_pow]; ring
  have h := analytic_finset_product_geometric_jets s f x J q (C*q⁻¹)
    (le_of_lt hq) (by positivity) ha hb' k hk
  have he : q^s.card*(q⁻¹)^k = q^((s.card:ℤ)-(k:ℤ)) := by
    simpa only [zpow_natCast] using scaled_jet_power_identity q hq (s.card:ℤ) k
  convert h using 1
  simp only [mul_pow]
  rw [← he]
  ring

end
end IsingBulk.Tail
