import IsingBulk.Anisotropic.NegativeCycles.ComplexFactorBounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeCycles Set Filter Metric
open scoped Topology BigOperators
set_option maxHeartbeats 800000

def regularAngularPair (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (t a b : ℂ) : ℂ :=
  (halfSineSlope (a-b)/Complex.sinh
    ((negativePhase B phi hphi t a+negativePhase B phi hphi t b)/2))^2

theorem regularAngularPair_analyticAt (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularAngularPair B phi hphi z.1 z.2.1 z.2.2) 0 := by
  have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => negativePhase B phi hphi p.1 p.2) (0,0) := by
    simpa using negativePhase_analyticAt_center B phi hphi 0 (by simpa using hB)
  have ha : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.1) 0 := analyticAt_fst.comp analyticAt_snd
  have hb : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => z.2.2) 0 := analyticAt_snd.comp analyticAt_snd
  have h1 : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => negativePhase B phi hphi z.1 z.2.1) 0 :=
    hg.comp_of_eq (analyticAt_fst.prod ha) rfl
  have h2 : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => negativePhase B phi hphi z.1 z.2.2) 0 :=
    hg.comp_of_eq (analyticAt_fst.prod hb) rfl
  have hz : negativePhase B phi hphi 0 0=(phi:ℂ)*Complex.I := by
    simpa using negativePhase_center B phi hphi 0
  have hden : Complex.sinh ((negativePhase B phi hphi 0 0+negativePhase B phi hphi 0 0)/2)≠0 := by
    rw [hz,show ((phi:ℂ)*Complex.I+(phi:ℂ)*Complex.I)/2=(phi:ℂ)*Complex.I by ring]
    rw [Complex.sinh_mul_I,←Complex.ofReal_sin]
    exact mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero
  exact ((halfSineSlope_analyticAt.comp_of_eq (ha.sub hb) (by simp)).div
    (Complex.analyticAt_sinh.comp ((h1.add h2).div_const)) hden).pow 2


theorem regularAngularPair_uniform_bound (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) :
    ∃ δ M : ℝ, 0<δ ∧ 1≤M ∧ ∀t a b : ℂ, ‖t‖<δ → ‖a‖<δ → ‖b‖<δ →
      ‖regularAngularPair B phi hphi t a b‖≤M := by
  let M := ‖regularAngularPair B phi hphi 0 0 0‖+1
  have hm : 1≤M := by dsimp [M]; linarith [norm_nonneg (regularAngularPair B phi hphi 0 0 0)]
  have he : ∀ᶠ z : ℂ × ℂ × ℂ in 𝓝 0,
      ‖regularAngularPair B phi hphi z.1 z.2.1 z.2.2‖<M :=
    (regularAngularPair_analyticAt B phi hphi hB).continuousAt.norm.eventually_lt_const (by
      change ‖regularAngularPair B phi hphi 0 0 0‖<M
      dsimp [M]; linarith)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,M,hδ,hm,?_⟩
  intro t a b ht ha hb
  have hmem : dist (t,a,b) (0 : ℂ × ℂ × ℂ)<δ := by
    simpa [dist_zero_right,Prod.norm_def,max_lt_iff] using And.intro ht (And.intro ha hb)
  exact (hd hmem).le

theorem regularNumerator_norm_bound {n : ℕ} (B rootB : ℂ→ℂ)
    (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    {M : ℝ} (hM : 1≤M) (hB : ‖B t‖≤M) (hr : ‖rootB t‖≤M)
    (hone : ∀ i, ‖(Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹‖≤M)
    (hpair : ∀i j, ‖regularAngularPair B phi hphi t (d+v i) (d+v j)‖≤M) :
    ‖regularNumerator B rootB phi hphi d t v‖≤M^(1+alpha n+n+n.choose 2) := by
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hpi : 1≤‖2*(Real.pi:ℂ)‖ := by
    norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hden : 1≤‖((n.factorial:ℂ)*(2*(Real.pi:ℂ))^(n-1))‖ := by
    rw [norm_mul,norm_pow,Complex.norm_natCast]
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos n) (one_le_pow₀ hpi)
  have hpre : ‖densityPrefactor B rootB n t‖≤M*M^(alpha n) := by
    rw [densityPrefactor,norm_div]
    calc
      _ ≤ ‖rootB t*B t^(alpha n)‖ := div_le_self (norm_nonneg _) hden
      _ = ‖rootB t‖*‖B t‖^(alpha n) := by rw [norm_mul,norm_pow]
      _ ≤ M*M^(alpha n) := mul_le_mul hr (pow_le_pow_left₀ (norm_nonneg _) hB _) (by positivity) hM0
  have ho : ‖∏ i, (Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹‖≤M^n := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin n, M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hone i)
      _ = _ := by simp
  have hp : ‖∏ p∈firstStrictPairs n,
      (halfSineSlope (v p.1-v p.2)/pairDenominator B phi hphi d t (v p.1) (v p.2))^2‖≤M^(n.choose 2) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _p∈firstStrictPairs n,M := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro p _
        simpa only [regularAngularPair,pairDenominator,add_sub_add_left_eq_sub] using hpair p.1 p.2
      _ = _ := by simp [firstStrictPairs_card]
  rw [regularNumerator,norm_mul,norm_mul]
  calc
    _ ≤ ((M*M^(alpha n))*M^n)*M^(n.choose 2) :=
      mul_le_mul (mul_le_mul hpre ho (norm_nonneg _) (by positivity)) hp (norm_nonneg _) (by positivity)
    _ = _ := by simp only [pow_add,pow_one,mul_assoc]

/-- Coarse but genuine dimension-uniform full-density bound retaining every
Vandermonde zero. Its exponential N² cost is sufficient in the high range. -/
theorem formFactorNumerator_vandermonde_uniform_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hr : AnalyticAt ℂ rootB 0) :
    ∃ δ M : ℝ,0<δ ∧ 1≤M ∧ ∀n : ℕ, ∀d t : ℂ, ∀v : Config n,
      ‖d‖<δ → ‖t‖<δ → (∀i, ‖v i‖<δ) →
      ‖formFactorNumerator B rootB phi hphi d t v‖≤
        ‖vandermonde v‖^2*M^(1+alpha n+n+n.choose 2) := by
  obtain ⟨δ₁,M₁,hδ₁,hM₁,hscalar⟩ := local_complex_factors_bounded B rootB phi hphi hB hr
  obtain ⟨δ₂,M₂,hδ₂,hM₂,hpair⟩ := regularAngularPair_uniform_bound B phi hphi hB
  let δ := min δ₁ δ₂ / 2
  let M := max M₁ M₂
  have hδ : 0<δ := div_pos (lt_min hδ₁ hδ₂) (by norm_num)
  have hδ1 : 2*δ≤δ₁ := by dsimp [δ]; linarith [min_le_left δ₁ δ₂]
  have hδ2 : 2*δ≤δ₂ := by dsimp [δ]; linarith [min_le_right δ₁ δ₂]
  have hM : 1≤M := hM₁.trans (le_max_left _ _)
  refine ⟨δ,M,hδ,hM,?_⟩
  intro n d t v hd ht hv
  have ht1 : ‖t‖<δ₁ := by linarith
  have ht2 : ‖t‖<δ₂ := by linarith
  have ha (i) : ‖d+v i‖<2*δ := (norm_add_le d (v i)).trans_lt (by linarith [hv i])
  have hs := hscalar t 0 ht1 (by simpa using hδ₁)
  have hh := regularNumerator_norm_bound B rootB phi hphi d t v hM
    (hs.1.trans (le_max_left _ _)) (hs.2.1.trans (le_max_left _ _))
    (fun i => ((hscalar t (d+v i) ht1 ((ha i).trans_le hδ1)).2.2).trans (le_max_left _ _))
    (fun i j => (hpair t (d+v i) (d+v j) ht2 ((ha i).trans_le hδ2) ((ha j).trans_le hδ2)).trans (le_max_right _ _))
  rw [formFactorNumerator_factor,norm_mul,norm_pow]
  exact mul_le_mul_of_nonneg_left hh (sq_nonneg _)

end
end IsingBulk.Anisotropic.NegativeDominance
