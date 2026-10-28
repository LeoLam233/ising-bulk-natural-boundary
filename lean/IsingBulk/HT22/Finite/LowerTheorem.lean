import IsingBulk.HT22.Finite.LowerRight
import IsingBulk.HT22.Finite.SourceChoice
import IsingBulk.HT22.Finite.ComponentBound
import IsingBulk.HT22.Finite.OneParticle
namespace IsingBulk.HT22.Finite
noncomputable section
open IsingBulk.Preferred22 IsingBulk.PrimeFamily Arithmetic Physical Physical.FiniteAssembly
open Filter Set
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- Every actual lower odd coefficient is logarithmically bounded, for all
fixed complex derivative orders. No local, contour, remainder or derivative
estimate is left among the hypotheses. The one-particle term is retained. -/
theorem prime_lower_coefficient_bound {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {N : ℕ} (hN : Odd N) (hNp : N<p) (j : ℕ) :
    ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖iteratedDeriv j (signedCoefficient (negativeSide (angle p a)) N)
        (IsingBulk.Branch.radialParameter (primeBranchData hp hp5 ha).alpha ε)‖≤C*(1+|Real.log ε|) := by
  let d := primeBranchData hp hp5 ha
  let negative := negativeSide (angle p a)
  by_cases hN1 : N=1
  · subst N
    exact one_particle_bound d negative j
  obtain ⟨k,hk⟩ : ∃k : ℕ,N=2*(k+1)+1 := by
    obtain ⟨q,hq⟩ := hN
    exact ⟨q-1,by omega⟩
  subst N
  obtain ⟨g,hg,hR⟩ := prime_lower_right_bound_of_separated_remainder hp hp5 ha
  obtain ⟨B,δ,τ,e,r,hδ,hδg,hτ,he,hcut,hFA,hrem⟩ := actual_finite_source_choice d hg
  obtain ⟨C,hC,hFA⟩ := hFA j
  apply coefficient_log_bound_of_components negative k d B hτ.le r hcut.2.2.1 j
  · exact ⟨C,e,hC,he,fun ε hε hεe => (hFA negative k ε hε hεe).1⟩
  · exact ⟨C,e,hC,he,fun ε hε hεe => (hFA negative k ε hε hεe).2⟩
  · apply hR B τ hτ.le δ hδg r hcut (2*(k+1)) hN hNp j
    intro rem hsmooth hsep
    obtain ⟨CR,hCR,hbound⟩ := hrem negative (2*(k+1)) hN (by omega) rem hsmooth hsep j
    exact ⟨CR,e,hCR,he,hbound⟩

/-- Actual epsilon-scaled lower coefficient vanishing, including N=1. -/
theorem prime_lower_coefficient_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {N : ℕ} (hN : Odd N) (hNp : N<p) (j : ℕ) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv j (signedCoefficient (negativeSide (angle p a)) N)
      (IsingBulk.Branch.radialParameter (primeBranchData hp hp5 ha).alpha ε)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
  complex_epsilon_zero_of_log_bound _ (prime_lower_coefficient_bound hp hp5 ha hN hNp j)

/-- The whole finite lower part of the original effective signed odd series
vanishes at the first singular scale, without discarding its first particle. -/
theorem prime_lower_sum_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) (j : ℕ) :
    Tendsto (fun ε : ℝ => ε • (∑ n ∈ Finset.range (p/2),
      iteratedDeriv j (signedCoefficient (negativeSide (angle p a)) (2*n+1))
        (IsingBulk.Branch.radialParameter (primeBranchData hp hp5 ha).alpha ε)))
      (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  have hodd := hp.odd_of_ne_two (by omega)
  have hlocal (n : ℕ) (hn : n∈Finset.range (p/2)) :=
    prime_lower_coefficient_limit hp hp5 ha (show Odd (2*n+1) from ⟨n,rfl⟩)
      (show 2*n+1<p by
        have hn' := Finset.mem_range.mp hn
        obtain ⟨q,hq⟩ := hodd
        omega) j
  have hh := tendsto_finsetSum (Finset.range (p/2)) hlocal
  simpa only [Finset.sum_const_zero,Finset.smul_sum] using hh
end
end IsingBulk.HT22.Finite
