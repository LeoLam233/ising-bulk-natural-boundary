import IsingBulk.HT22.Finite.FirstRight
import IsingBulk.HT22.Finite.FirstReflection
import IsingBulk.HT22.Finite.SourceChoice

/-! The complete finite FIRST coefficient, with every population, cutoff,
regular neighborhood and separated remainder discharged by actual sources. -/
namespace IsingBulk.HT22.Finite
noncomputable section
open Complex Set Filter IsingBulk.First IsingBulk.Branch IsingBulk.HT.First
open IsingBulk.PrimeFamily Arithmetic LocalLimit Physical IsingBulk.Preferred22
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem actual_prime_first_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv (derivativeOrder p)
      (signedCoefficient (negativeSide (angle p a)) p)
      (radialParameter (primeBranchData hp hp5 ha).alpha ε))
      (𝓝[>] 0) (𝓝 (physicalCriticalLeadingCoefficient p (angle p a))) := by
  let d := primeBranchData hp hp5 ha
  let negative := negativeSide (angle p a)
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  have he : p-1+1=p := by omega
  obtain ⟨g,hg,hR⟩ := prime_right_limit_of_separated_remainder hp hp5 ha
  obtain ⟨B,δ,τ,e,r,_hδ,hδg,hτ,hepos,hcut,hcomp,hfar⟩ := actual_finite_source_choice d hg
  have hright := hR B τ hτ.le δ hδg r hcut (by
    intro rem hrem hsep
    obtain ⟨C,hC,hb⟩ := hfar negative (p-1) (he.symm ▸ ho) (by omega) rem hrem hsep (derivativeOrder p)
    exact ⟨C,e,hC,hepos,hb⟩)
  obtain ⟨k,hk⟩ : ∃k : ℕ,2*(k+1)+1=p := by
    obtain ⟨q,hq⟩ := ho
    exact ⟨q-1,by omega⟩
  have hdim : 2*(k+1)=p-1 := by omega
  obtain ⟨C,hC,hcomp⟩ := hcomp (derivativeOrder p)
  have ht := coefficient_limit_of_right_limit negative k d B hτ.le r hcut.2.2.1 (derivativeOrder p)
    (L := (1/2:ℂ)*physicalCriticalLeadingCoefficient p (angle p a))
    ⟨C,e,hC,hepos,fun ε hε hεe => (hcomp negative k ε hε hεe).1⟩
    ⟨C,e,hC,hepos,fun ε hε hεe => (hcomp negative k ε hε hεe).2⟩
    (by simpa only [hdim] using hright)
  simpa only [hk,show (2:ℂ)*((1/2:ℂ)*physicalCriticalLeadingCoefficient p (angle p a))=
      physicalCriticalLeadingCoefficient p (angle p a) by ring] using ht

/-- Exact original unsigned F001 FIRST phase, including upper-left members
of the prime family, not only the effective signed nonzero obstruction. -/
theorem actual_original_prime_first_limit {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    Tendsto (fun ε : ℝ => ε • iteratedDeriv (derivativeOrder p)
      (signedCoefficient false p) (radialParameter (angle p a) ε))
      (𝓝[>] 0) (𝓝 (equalAngleLeadingCoefficient p (angle p a))) :=
  original_first_limit_of_effective_signed hp hp5 ha (actual_prime_first_limit hp hp5 ha)

theorem actual_original_prime_first_asymptotic {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) :
    equalAngleLeadingCoefficient p (angle p a)≠0 ∧
    Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun ε => iteratedDeriv (derivativeOrder p) (signedCoefficient false p)
        (radialParameter (angle p a) ε)-(ε:ℂ)⁻¹*equalAngleLeadingCoefficient p (angle p a))
      (fun ε => (ε:ℂ)⁻¹) :=
  ⟨(prime_two_chart_asymptotic hp hp5 ha).1,
    normalized_epsilon_limit_isLittleO (actual_original_prime_first_limit hp hp5 ha)⟩

end
end IsingBulk.HT22.Finite
