import IsingBulk.Anisotropic.NegativeDominance.AllParticleBoundaryCauchy
import IsingBulk.Anisotropic.RegularEdges.TailSummability

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges
open scoped BigOperators

theorem particleEdgeMajorant_uniform_bound {r C M : ℝ}
    (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) :
    ∃ H : ℝ, 0<H ∧ ∀ n, particleEdgeMajorant r C M n≤H := by
  have hs : Summable (particleEdgeMajorant r C M) := by
    simpa only [pow_zero,one_mul] using particleEdgeMajorant_polynomial_summable hr hr1 hC hM 0
  have hn (n : ℕ) := particleEdgeMajorant_nonneg hr.le hC.le hM.le n
  refine ⟨1+∑' n,particleEdgeMajorant r C M n,by have ht : 0≤∑' n,particleEdgeMajorant r C M n := tsum_nonneg hn; linarith,?_⟩
  intro n
  have hh := hs.le_tsum n (fun k _ => hn k)
  linarith

/-- Convert the proved all-particle Cauchy estimate into a simple normalized
Taylor-coefficient bound. The particle majorant is bounded by its actual sum. -/
theorem normalized_particle_cauchy_bound {a r C M K : ℝ}
    (ha : 0<a) (hr : 0<r) (hr1 : r<1) (hC : 0<C) (hM : 0<M) (hK : 0<K)
    (g : ℕ → ℂ → ℂ)
    (hbound : ∀ (j n : ℕ), Odd (n+1) → ‖iteratedDeriv j (g n) 0‖≤
      (j.factorial : ℝ)*(K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1))/
        (a/((n+1 : ℕ) : ℝ)^3)^j) :
    ∃ D : ℝ, 0<D ∧ ∀ (j n : ℕ), Odd (n+1) →
      ‖iteratedDeriv j (g n) 0/(j.factorial : ℂ)‖≤
        D*((n+1 : ℕ) : ℝ)^2*(((n+1 : ℕ) : ℝ)^3/a)^j := by
  obtain ⟨H,hH,hmajor⟩ := particleEdgeMajorant_uniform_bound hr hr1 hC hM
  refine ⟨K*H,mul_pos hK hH,?_⟩
  intro j n hn
  have hj : (j.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hN : ((n+1 : ℕ) : ℝ)≠0 := by positivity
  rw [norm_div,Complex.norm_natCast]
  calc
    ‖iteratedDeriv j (g n) 0‖/(j.factorial : ℝ) ≤
      ((j.factorial : ℝ)*(K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1))/
        (a/((n+1 : ℕ) : ℝ)^3)^j)/(j.factorial : ℝ) :=
      div_le_div_of_nonneg_right (hbound j n hn) (by positivity)
    _ = K*((n+1 : ℕ) : ℝ)^2*particleEdgeMajorant r C M (n+1)*(((n+1 : ℕ) : ℝ)^3/a)^j := by
      rw [div_pow,div_pow]
      field_simp [ha.ne',hj,hN]
    _ ≤ K*((n+1 : ℕ) : ℝ)^2*H*(((n+1 : ℕ) : ℝ)^3/a)^j := by
      gcongr
      exact hmajor (n+1)
    _ = (K*H)*((n+1 : ℕ) : ℝ)^2*(((n+1 : ℕ) : ℝ)^3/a)^j := by ring

/-- Uniform control of every growing low-index set. In particular L may be
floor(log j); no fixed finite family is substituted for that range. -/
theorem growing_low_sum_bound {a D : ℝ} (ha : 0<a) (hD : 0≤D)
    (g : ℕ → ℂ → ℂ)
    (hbound : ∀ (j n : ℕ), Odd (n+1) →
      ‖iteratedDeriv j (g n) 0/(j.factorial : ℂ)‖≤
        D*((n+1 : ℕ) : ℝ)^2*(((n+1 : ℕ) : ℝ)^3/a)^j)
    (j L : ℕ) (S : Finset ℕ) (hodd : ∀ n∈S, Odd (n+1)) (hsmall : ∀ n∈S, n+1≤L) :
    (∑ n∈S,‖iteratedDeriv j (g n) 0/(j.factorial : ℂ)‖)≤
      D*(L : ℝ)^3*((L : ℝ)^3/a)^j := by
  have hcard : S.card≤L := by
    apply le_trans (Finset.card_le_card (show S⊆Finset.range L from ?_))
      (by simp)
    intro n hn
    exact Finset.mem_range.mpr (by have := hsmall n hn; omega)
  calc
    ∑ n∈S,‖iteratedDeriv j (g n) 0/(j.factorial : ℂ)‖ ≤
        ∑ _n∈S,D*(L : ℝ)^2*((L : ℝ)^3/a)^j := by
      apply Finset.sum_le_sum
      intro n hn
      apply (hbound j n (hodd n hn)).trans
      have hle : ((n+1 : ℕ) : ℝ)≤L := by exact_mod_cast hsmall n hn
      gcongr
    _ = (S.card : ℝ)*(D*(L : ℝ)^2*((L : ℝ)^3/a)^j) := by simp
    _ ≤ (L : ℝ)*(D*(L : ℝ)^2*((L : ℝ)^3/a)^j) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = D*(L : ℝ)^3*((L : ℝ)^3/a)^j := by ring

end
end IsingBulk.Anisotropic.NegativeDominance
