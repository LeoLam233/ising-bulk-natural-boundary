import IsingBulk.Anisotropic.NegativeDominance.ResonantMiddleSmall
import IsingBulk.Anisotropic.NegativeDominance.CrossingMiddleRange

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology BigOperators

def resonantMiddleIndices (p j : ℕ) : Finset ℕ :=
  (Finset.range (j+1)).filter (fun i => Real.log j<(resonantParticle p i : ℝ) ∧
    (resonantParticle p i : ℝ)^2≤j/Real.sqrt (Real.log j))

theorem resonant_index_le_particle {p : ℕ} (hp : 0<p) (i : ℕ) :
    i≤resonantParticle p i := by
  have hh := Nat.le_mul_of_pos_left (2*i+1) hp
  unfold resonantParticle
  omega

theorem middle_square_le_order {N j : ℕ} (hs : 1≤Real.sqrt (Real.log j))
    (hcut : (N : ℝ)^2≤j/Real.sqrt (Real.log j)) : N^2≤j := by
  have hj : (0 : ℝ)≤j := Nat.cast_nonneg j
  have hd := div_le_self hj hs
  exact_mod_cast hcut.trans hd

theorem middle_index_mem_iff {p j : ℕ} (hp : 0<p) (hs : 1≤Real.sqrt (Real.log j)) (i : ℕ) :
    i∈resonantMiddleIndices p j ↔ Real.log j<(resonantParticle p i : ℝ) ∧
      (resonantParticle p i : ℝ)^2≤j/Real.sqrt (Real.log j) := by
  classical
  constructor
  · intro hi; exact (Finset.mem_filter.mp hi).2
  intro hi
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hi⟩
  have hh := middle_square_le_order hs hi.2
  have hle := resonant_index_le_particle hp i
  have hsq : resonantParticle p i≤(resonantParticle p i)^2 := Nat.le_self_pow (by norm_num) _
  omega

theorem middle_indices_gamma_range {p j i : ℕ} (hs : 1≤Real.sqrt (Real.log j))
    (hi : i∈resonantMiddleIndices p j) : 2*alpha (resonantParticle p i)≤j := by
  have hh := middle_square_le_order hs (Finset.mem_filter.mp hi).2.2
  unfold alpha
  have hmul : resonantParticle p i*resonantParticle p i=(resonantParticle p i)^2 := by ring
  rw [hmul]
  omega

theorem eventually_selected_mem_middle {p : ℕ} (hp : 0<p) :
    ∀ᶠ n : ℕ in atTop,∀ell : ℕ,resonantParticle p ell=n → ∀j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) → (j : ℝ)≤upperCrossingOrder n → n≤j →
      ell+1∈resonantMiddleIndices p j := by
  have ht : Tendsto (fun j : ℕ => Real.sqrt (Real.log j)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (1 : ℝ)))
  filter_upwards [eventually_crossing_middle_range p,eventually_ge_atTop J] with n hn hnJ
  intro ell he j hjL hjH hnj
  have hcut := hn j hjL hjH hnj
  apply (middle_index_mem_iff hp (hJ j (hnJ.trans hnj)) (ell+1)).mpr
  have hcenter : resonantParticle p (ell+1)=n+2*p := by rw [←he]; unfold resonantParticle; ring
  simpa only [hcenter] using hcut

end
end IsingBulk.Anisotropic.NegativeDominance
