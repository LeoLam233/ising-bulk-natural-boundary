import IsingBulk.First.ShapeVandermonde
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First
open scoped BigOperators

/-- The finite AM–GM bound in a form useful for literal density factors. -/
theorem prod_le_power_of_sum_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i∈S, 0≤f i) {A : ℝ} (_hA : 0≤A)
    (hs : ∑ i∈S,f i≤S.card*A) : ∏ i∈S,f i≤A^S.card := by
  by_cases hz : S.card=0
  · have he : S=∅ := Finset.card_eq_zero.mp hz
    simp [he]
  have hc : (0 : ℝ)<S.card := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hp : 0≤∏ i∈S,f i := Finset.prod_nonneg hf
  have hm : (∏ i∈S,f i)^((S.card : ℝ)⁻¹)≤(∑ i∈S,f i)/(S.card : ℝ) := by
    simpa using Real.geom_mean_le_arith_mean S (fun _ => (1 : ℝ)) f
      (fun _ _ => by norm_num) (by simpa using hc) hf
  have hmean : (∑ i∈S,f i)/(S.card : ℝ)≤A := (div_le_iff₀ hc).mpr (by simpa [mul_comm] using hs)
  have hh := pow_le_pow_left₀ (Real.rpow_nonneg hp _) (hm.trans hmean) S.card
  have he : ((∏ i∈S,f i)^((S.card : ℝ)⁻¹))^S.card=∏ i∈S,f i := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hp,inv_mul_cancel₀ hc.ne',Real.rpow_one]
  simpa only [he] using hh

/-- A dimension-uniform pair-energy bound. No zero-mean premise is needed. -/
theorem strict_pair_energy_le {N : ℕ} (v : Fin N → ℝ) :
    (∑ p∈firstStrictPairs N,(v p.1-v p.2)^2)≤4*(N : ℝ)*(∑ i,(v i)^2) := by
  calc
    _ ≤ ∑ p : Fin N × Fin N,(v p.1-v p.2)^2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ ∑ p : Fin N × Fin N,(2*(v p.1)^2+2*(v p.2)^2) := by
      apply Finset.sum_le_sum
      intro p _
      nlinarith only [sq_nonneg (v p.1+v p.2)]
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.sum_add_distrib,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [←Finset.mul_sum]
      ring

/-- On the genuine energy ball the full real Vandermonde has the decisive
N² log N suppression. The numerical constant is deliberately non-sharp. -/
theorem vandermonde_sq_energy_ball {N : ℕ} (hN : 2≤N) (v : Fin N → ℝ)
    (hv : ∑ i,(v i)^2≤1) :
    firstVandermonde v^2≤(16/(N : ℝ))^(N.choose 2) := by
  have hNR : (2 : ℝ)≤N := by exact_mod_cast hN
  have hNp : (0 : ℝ)<N := by linarith
  rw [firstVandermonde,←Finset.prod_pow]
  have hs := (strict_pair_energy_le v).trans
    (mul_le_mul_of_nonneg_left hv (by positivity : 0≤4*(N : ℝ)))
  have hcard : 4*(N : ℝ)≤((firstStrictPairs N).card : ℝ)*(16/(N : ℝ)) := by
    rw [firstStrictPairs_card,Nat.cast_choose_two]
    field_simp
    nlinarith only [hNR]
  have hh := prod_le_power_of_sum_bound (firstStrictPairs N) (fun p => (v p.1-v p.2)^2)
    (fun _ _ => sq_nonneg _) (by positivity : 0≤16/(N : ℝ)) (hs.trans (by simpa using hcard))
  simpa only [firstStrictPairs_card] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
