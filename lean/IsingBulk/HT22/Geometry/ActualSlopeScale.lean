import IsingBulk.HT22.Geometry.FullSlopeCone
import IsingBulk.HT22.Geometry.BumpSecants

namespace IsingBulk.HT22.Geometry
noncomputable section
open scoped Topology BigOperators
open Set IsingBulk.Preferred22

/-- The branch displacement is controlled by the actual shell scale.
If the positive occupancy vanishes it is zero; otherwise an actual
positive angle forces T≥b/2. Arbitrary fixed occupancies cannot replace
this step. -/
theorem actual_occupancy_branch_scale (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {N : ℕ} (hN : 0<N) (θ : Fin N → ℝ) {ε τ μ r x : ℝ}
    (hε : 0<ε) (hτ : 0≤τ) (hτ1 : τ≤1) (hr : 0<r)
    (hθ : ∀ i, θ i∈Icc (-Real.pi) Real.pi)
    (hwin : ∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r)
    (hx : μ-2*r≤x+d.b ∧ x+d.b≤μ+2*r) :
    |x+d.b|+ε+τ*(occupancy B.p θ/(N:ℝ)) ≤ (3+2/d.b)*(|μ|+r+ε) := by
  have hbpos := d.b_pos
  let T := |μ|+r+ε
  have hT : 0<T := by dsimp [T]; positivity
  have hxabs : |x+d.b|≤|μ|+2*r := abs_le.mpr ⟨by linarith [neg_abs_le μ],by linarith [le_abs_self μ]⟩
  obtain ⟨hσ,_⟩ := actual_occupancy_box hN B θ
  have hδ : τ*(occupancy B.p θ/(N:ℝ))≤(2/d.b)*T := by
    by_cases hP : occupancy B.p θ=0
    · rw [hP,zero_div,mul_zero]
      positivity
    · have hPpos : 0<occupancy B.p θ := lt_of_le_of_ne
        (Finset.sum_nonneg (fun i _ => B.lower_bound (θ i))) (Ne.symm hP)
      obtain ⟨a,ha⟩ : ∃ a : Fin N, 0<B.p (θ a) := by
        by_contra hh
        push Not at hh
        have hz : ∀ a, B.p (θ a)=0 := fun a => le_antisymm (hh a) (B.lower_bound (θ a))
        have hzero : occupancy B.p θ=0 := by simp only [occupancy,hz,Finset.sum_const_zero]
        linarith
      have hs := B.upper_support (θ a) (hθ a) ha.ne'
      have hbT : d.b≤2*T := by dsimp [T]; linarith [(hwin a).2,hs.1,le_abs_self μ,abs_nonneg μ]
      have hδ1 : τ*(occupancy B.p θ/(N:ℝ))≤1 :=
        (mul_le_of_le_one_right hτ hσ.2).trans hτ1
      have hb : 1≤(2/d.b)*T := by
        rw [div_mul_eq_mul_div]
        exact (le_div_iff₀ d.b_pos).mpr (by nlinarith)
      exact hδ1.trans hb
  dsimp [T] at hδ ⊢
  nlinarith [abs_nonneg μ]

theorem shell_window_abs {μ r x b : ℝ} (hx : μ-2*r≤x+b ∧ x+b≤μ+2*r) :
    |x+b|≤|μ|+2*r := abs_le.mpr ⟨by linarith [neg_abs_le μ],by linarith [le_abs_self μ]⟩

/-- Full quantitative lower derivative estimate on the fixed-occupancy
curve determined by an actual configuration, with one constant chosen
before every particle number and shell. -/
theorem actual_inverse_slope_scale (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ c ε₀ τ₀ δB : ℝ, 0<c ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r →
      ∀ θ : Fin N → ℝ, (∀ i, θ i∈Icc (-d.b-δB) B.delta) →
      (∀ i, μ-2*r≤θ i+d.b ∧ θ i+d.b≤μ+2*r) →
      let f := occupancyInverseV d B.m B.p ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ))
      (∀ x∈Icc (-d.b-δB) B.delta, HasDerivAt f (deriv f x) x) ∧
      ContinuousOn (deriv f) (Icc (-d.b-δB) B.delta) ∧
      ∀ x∈Icc (-d.b-δB) B.delta, μ-2*r≤x+d.b → x+d.b≤μ+2*r →
        (1/5:ℝ)*‖deriv f x‖≤(covarianceDirection*deriv f x).re ∧
        c/Real.sqrt (|μ|+r+ε)≤(covarianceDirection*deriv f x).re := by
  obtain ⟨c,a,ρ,e,t,δ,hc,ha,hρ,he,ht,hδ,hδB,hfull⟩ := occupancyInverseV_full_cone d B
  let K := 3+2/d.b
  have hbpos := d.b_pos
  have hK : 1≤K := by dsimp [K]; have := div_pos (by norm_num : (0:ℝ)<2) hbpos; linarith
  have hKpos : 0<K := lt_of_lt_of_le zero_lt_one hK
  let C := min (c/K) (a*Real.sqrt (ρ/2))
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,e,min t 1,δ,hC,he,lt_min ht zero_lt_one,hδ,hδB,?_⟩
  intro N hN ε τ μ r hε hεe hτ hτt hr θ hθ hwin
  obtain ⟨hσ,hυ⟩ := actual_occupancy_box hN B θ
  obtain ⟨hder,hcont,hbound⟩ := hfull ε τ _ _ hε hεe hτ
    (hτt.trans_le (min_le_left _ _)) hσ hυ
  refine ⟨hder,hcont,?_⟩
  intro x hx hxlo hxhi
  obtain ⟨hcone,hlow⟩ := hbound x hx
  refine ⟨hcone,?_⟩
  let T := |μ|+r+ε
  have hT : 0<T := by dsimp [T]; positivity
  have hTs : 0<Real.sqrt T := Real.sqrt_pos.mpr hT
  have hxabs := shell_window_abs (b:=d.b) ⟨hxlo,hxhi⟩
  by_cases hsmall : |x+d.b|<ρ
  · simp only [ite_eq_left hsmall] at hlow
    let q := |x+d.b|+ε+τ*(occupancy B.p θ/(N:ℝ))
    have hσ0 := hσ.1
    have hq : 0<q := by dsimp [q]; positivity
    have hqT : q≤K*T := actual_occupancy_branch_scale d B hN θ hε hτ
      (hτt.trans_le (min_le_right _ _)).le hr
      (fun i => ⟨by have := (hθ i).1; linarith [B.branch_plateau,hδB],
        by have := (hθ i).2; linarith [B.delta_alpha,d.alpha_lt,Real.pi_pos]⟩)
      hwin ⟨hxlo,hxhi⟩
    have hsq : Real.sqrt q≤K*Real.sqrt T := by
      have hqK : q≤K^2*T := hqT.trans (mul_le_mul_of_nonneg_right (by nlinarith) hT.le)
      have hs := Real.sqrt_le_sqrt hqK
      rw [Real.sqrt_mul (sq_nonneg K),Real.sqrt_sq_eq_abs,abs_of_pos hKpos] at hs
      exact hs
    have hh : (c/K)/Real.sqrt T ≤ c/Real.sqrt q := by
      rw [div_div]
      exact div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hq) hsq
    exact (div_le_div_of_nonneg_right (min_le_left _ _) hTs.le).trans (hh.trans hlow)
  · simp only [ite_eq_right hsmall] at hlow
    have hrT : ρ/2≤T := by dsimp [T]; have := le_of_not_gt hsmall; linarith [abs_nonneg μ]
    have hs := Real.sqrt_le_sqrt hrT
    have hCa : C≤a*Real.sqrt T := (min_le_right _ _).trans (mul_le_mul_of_nonneg_left hs ha.le)
    exact ((div_le_iff₀ hTs).mpr hCa).trans hlow

end
end IsingBulk.HT22.Geometry
