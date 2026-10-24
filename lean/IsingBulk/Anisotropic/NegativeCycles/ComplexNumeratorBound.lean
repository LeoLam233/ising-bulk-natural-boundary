import Mathlib.Analysis.Real.Pi.Bounds
import IsingBulk.Anisotropic.NegativeCycles.ComplexNumeratorFactor
import IsingBulk.Anisotropic.NegativeCycles.ComplexFactorBounds

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm
open scoped BigOperators

theorem formFactorNumerator_odd_norm_bound (m : ℕ) (B rootB : ℂ→ℂ)
    (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config (2*m+1))
    {M : ℝ} (hM : 1≤M) (hB : ‖B t‖≤M) (hr : ‖rootB t‖≤M)
    (hone : ∀ i, ‖(Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹‖≤M)
    (hpair : ∀i j, ‖localCompletePair B phi hphi t (d+v i) (d+v j)‖≤(1/2:ℝ)) :
    ‖formFactorNumerator B rootB phi hphi d t v‖≤
      (M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2) := by
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hpi : 1≤‖2*(Real.pi:ℂ)‖ := by
    norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hden : 1≤‖(((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))‖ := by
    rw [norm_mul,norm_pow,Complex.norm_natCast]
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos (2*m+1))
      (one_le_pow₀ hpi)
  have hpre : ‖rootB t*B t^m / (((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))‖≤M*M^m := by
    rw [norm_div]
    calc
      _ ≤ ‖rootB t*B t^m‖ := div_le_self (norm_nonneg _) hden
      _ = ‖rootB t‖*‖B t‖^m := by rw [norm_mul,norm_pow]
      _ ≤ M*M^m := mul_le_mul hr (pow_le_pow_left₀ (norm_nonneg _) hB m) (by positivity) hM0
  have ho : ‖∏ i, (Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹‖≤M^(2*m+1) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin (2*m+1), M := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hone i)
      _ = _ := by simp
  have hp : ‖∏ p∈firstStrictPairs (2*m+1), localCompletePair B phi hphi t (d+v p.1) (d+v p.2)‖≤
      (1/2:ℝ)^((2*m+1).choose 2) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _p∈firstStrictPairs (2*m+1), (1/2:ℝ) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p _ => hpair p.1 p.2)
      _ = _ := by simp [firstStrictPairs_card]
  rw [formFactorNumerator_odd_complete_pairs,norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul hpre ho (norm_nonneg _) (by positivity)) hp
    (norm_nonneg _) (by positivity)

/-- Actual all-particle Gaussian suppression on one common complex local domain. -/
theorem formFactorNumerator_complex_uniform_bound (B rootB : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hr : AnalyticAt ℂ rootB 0) :
    ∃ δ M : ℝ,0<δ ∧ 1≤M ∧ ∀m : ℕ, ∀d t : ℂ, ∀v : Config (2*m+1),
      ‖d‖<δ → ‖t‖<δ → (∀i, ‖v i‖<δ) →
      ‖formFactorNumerator B rootB phi hphi d t v‖≤
        (M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2) := by
  obtain ⟨δ₁,M,hδ₁,hM,hscalar⟩ := local_complex_factors_bounded B rootB phi hphi hB hr
  obtain ⟨δ₂,hδ₂,hpair⟩ := localCompletePair_uniform_contraction B phi hphi hB
  let δ := min δ₁ δ₂ / 2
  have hδ : 0<δ := div_pos (lt_min hδ₁ hδ₂) (by norm_num)
  have hδ1 : 2*δ≤δ₁ := by dsimp [δ]; linarith [min_le_left δ₁ δ₂]
  have hδ2 : 2*δ≤δ₂ := by dsimp [δ]; linarith [min_le_right δ₁ δ₂]
  refine ⟨δ,M,hδ,hM,?_⟩
  intro m d t v hd ht hv
  have ht1 : ‖t‖<δ₁ := by linarith
  have ht2 : ‖t‖<δ₂ := by linarith
  have ha (i) : ‖d+v i‖<2*δ := (norm_add_le d (v i)).trans_lt (by linarith [hv i])
  have hs := hscalar t 0 ht1 (by simpa using hδ₁)
  exact formFactorNumerator_odd_norm_bound m B rootB phi hphi d t v hM hs.1 hs.2.1
    (fun i => (hscalar t (d+v i) ht1 ((ha i).trans_le hδ1)).2.2)
    (fun i j => hpair t (d+v i) (d+v j) ht2 ((ha i).trans_le hδ2) ((ha j).trans_le hδ2))

end IsingBulk.Anisotropic.NegativeCycles
