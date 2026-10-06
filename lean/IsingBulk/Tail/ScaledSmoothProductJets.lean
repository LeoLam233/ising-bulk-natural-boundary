import IsingBulk.Tail.ScaledAnalyticProductJets
import IsingBulk.Tail.ChangedPairProductJets

/-! Real smooth finite products with exact scale degree. No factor is divided
out, and no real angular bump is treated as analytic. -/
namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped BigOperators Topology ContDiff
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq ι]

theorem smooth_two_factor_jet_bound (f g : E → ℂ) (x : E) (k : ℕ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖≤
      ∑ i∈Finset.range (k+1), (k.choose i:ℝ)*‖iteratedFDeriv ℝ i f x‖*
        ‖iteratedFDeriv ℝ (k-i) g x‖ := by
  have hfk : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (k:ℕ∞ω) f y :=
    (hf.of_le (show (k:ℕ∞ω)≤∞ by simp)).eventually (by simp)
  have hgk : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (k:ℕ∞ω) g y :=
    (hg.of_le (show (k:ℕ∞ω)≤∞ by simp)).eventually (by simp)
  obtain ⟨U,hU,hopen,hx⟩ := eventually_nhds_iff.mp (hfk.and hgk)
  have hfU : ContDiffOn ℝ (k:ℕ∞ω) f U := fun y hy => (hU y hy).1.contDiffWithinAt
  have hgU : ContDiffOn ℝ (k:ℕ∞ω) g U := fun y hy => (hU y hy).2.contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_mul_le hfU hgU hopen.uniqueDiffOn hx (n := k) (by simp)
  simpa only [iteratedFDerivWithin_of_isOpen _ hopen hx] using hb

theorem smooth_finset_product_geometric_jets (s : Finset ι) (f : ι → E → ℂ)
    (x : E) (J : ℕ) (V L : ℝ) (hV : 0 ≤ V) (hL : 0 ≤ L)
    (ha : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x)
    (hb : ∀ i ∈ s, ∀ k ≤ J, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ V * L^k) :
    ∀ k ≤ J, ‖iteratedFDeriv ℝ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      V^s.card * ((s.card : ℝ)*L)^k := by
  induction s using Finset.induction_on with
  | empty =>
    intro k hk
    cases k with
    | zero => simp
    | succ k => simp [iteratedFDeriv_succ_const]
  | @insert a s has ih =>
    have haS : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x := fun i hi => ha i (Finset.mem_insert_of_mem hi)
    have hbS : ∀ i ∈ s, ∀ k ≤ J, ‖iteratedFDeriv ℝ k (f i) x‖ ≤ V*L^k :=
      fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hp : ContDiffAt ℝ ∞ (fun y => ∏ i ∈ s, f i y) x :=
      contDiffAt_prod (fun i hi => haS i hi)
    intro k hk
    simp only [Finset.prod_insert has, Finset.card_insert_of_notMem has, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ∑ r ∈ Finset.range (k+1), (k.choose r : ℝ) *
          ‖iteratedFDeriv ℝ r (f a) x‖ *
          ‖iteratedFDeriv ℝ (k-r) (fun y => ∏ i ∈ s, f i y) x‖ :=
        smooth_two_factor_jet_bound _ _ x k (ha a (Finset.mem_insert_self _ _)) hp
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

/-- A finite product preserves the exact total scale degree of its factors. -/
theorem smooth_finset_product_scaled_jets (s : Finset ι) (f : ι → E → ℂ)
    (x : E) (J : ℕ) (C q : ℝ) (a : ℤ) (hC : 0 ≤ C) (hq : 0 < q)
    (ha : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x)
    (hb : ∀ i ∈ s, ∀ k ≤ J,
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C * q^(a-(k:ℤ))) :
    ∀ k ≤ J, ‖iteratedFDeriv ℝ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      C^s.card * (s.card : ℝ)^k * q^(a*(s.card:ℤ)-(k:ℤ)) := by
  intro k hk
  have hb' : ∀ i ∈ s, ∀ r ≤ J,
      ‖iteratedFDeriv ℝ r (f i) x‖ ≤ (C*q^a)*(q⁻¹)^r := by
    intro i hi r hr
    simpa only [mul_assoc, scaled_jet_power_identity q hq] using hb i hi r hr
  have h := smooth_finset_product_geometric_jets s f x J (C*q^a) q⁻¹
    (by positivity) (by positivity) ha hb' k hk
  have he : (q^a)^s.card * (q⁻¹)^k = q^(a*(s.card:ℤ)-(k:ℤ)) := by
    rw [← zpow_natCast (q^a) s.card, ← zpow_mul]
    exact scaled_jet_power_identity q hq _ k
  convert h using 1
  simp only [mul_pow]
  rw [← he]
  ring

/-- Degree-one factors with derivative cost C lose only one scale per derivative. -/
theorem smooth_finset_product_contraction_jets (s : Finset ι) (f : ι → E → ℂ)
    (x : E) (J : ℕ) (C q : ℝ) (hC : 0 ≤ C) (hq : 0 < q)
    (ha : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x)
    (hb : ∀ i ∈ s, ∀ k ≤ J,
      ‖iteratedFDeriv ℝ k (f i) x‖ ≤ C^k * q^(1-(k:ℤ))) :
    ∀ k ≤ J, ‖iteratedFDeriv ℝ k (fun y => ∏ i ∈ s, f i y) x‖ ≤
      C^k * (s.card : ℝ)^k * q^((s.card:ℤ)-(k:ℤ)) := by
  intro k hk
  have hb' : ∀ i ∈ s, ∀ r ≤ J,
      ‖iteratedFDeriv ℝ r (f i) x‖ ≤ q*(C*q⁻¹)^r := by
    intro i hi r hr
    have he := scaled_jet_power_identity q hq 1 r
    simp only [zpow_one] at he
    calc
      _ ≤ C^r*q^(1-(r:ℤ)) := hb i hi r hr
      _ = q*(C*q⁻¹)^r := by rw [← he, mul_pow]; ring
  have h := smooth_finset_product_geometric_jets s f x J q (C*q⁻¹)
    (le_of_lt hq) (by positivity) ha hb' k hk
  have he : q^s.card*(q⁻¹)^k = q^((s.card:ℤ)-(k:ℤ)) := by
    simpa only [zpow_natCast] using scaled_jet_power_identity q hq (s.card:ℤ) k
  convert h using 1
  simp only [mul_pow]
  rw [← he]
  ring


end
end IsingBulk.Tail
