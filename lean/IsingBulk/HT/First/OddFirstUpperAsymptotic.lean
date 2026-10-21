import IsingBulk.HT.First.OddSelectedLocalPair
import IsingBulk.HT.First.OddComplementBound
import IsingBulk.First.LocalizedAnalytic

/-! The two constructed local source integrals and the actual complementary
integral are assembled. All three s-derivatives use the same fixed evaluation radius. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Filter IsingBulk.Branch IsingBulk.First
open scoped Topology

theorem first_upper_odd_asymptotic {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) (hab : a ≠ b) :
    let n := p-1
    let k := derivativeOrder (n+1)
    let A := selectedOrderedChart ha hb
    let L := -I*localLeadingCoefficient A n k
    L ≠ 0 ∧
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun epsilon => iteratedDeriv k (upperFormFactor (n+1)) (radialParameter A.theta epsilon)-
          (epsilon:ℂ)⁻¹*(2*L))
        (fun epsilon => (epsilon:ℂ)⁻¹) := by
  dsimp only
  let n := p-1
  let k := derivativeOrder (n+1)
  let A := selectedOrderedChart ha hb
  obtain ⟨hL,U,c,hLeft,hRight⟩ := odd_selected_local_pair_asymptotic hp (by omega) ha hb hab
  obtain ⟨eC,heC,hComplement⟩ := odd_selected_compatible_complement_bounded hp hp11 ha hb c
  obtain ⟨d,hd,_,hMargin⟩ := radial_disk_source_trace_margin A.sin_theta_pos
  have hSplit (epsilon : ℝ) (heps : 0 < epsilon) (hepsd : epsilon < d) (j : ℕ) :
      iteratedDeriv j (upperFormFactor (n+1)) (radialParameter A.theta epsilon) =
        radialWeightedDerivative n j A.theta c.leftWeight epsilon +
        radialWeightedDerivative n j A.theta c.rightWeight epsilon +
        iteratedDeriv j (fun s => localizedDoubleFormFactor (n+1)
          (sourceRadialPair A.theta epsilon).1 s (fun u => c.remainder u.2))
          (sourceRadialPair A.theta epsilon).2 := by
    have hr : 0 < (sourceRadialPair A.theta epsilon).1 := Real.exp_pos _
    have hr1 : (sourceRadialPair A.theta epsilon).1 < 1 := by
      change Real.exp (-(Real.sin A.theta/4)*epsilon) < 1
      rw [Real.exp_lt_one_iff]
      nlinarith [mul_pos A.sin_theta_pos heps]
    have hm := (hMargin epsilon heps hepsd (radialParameter A.theta epsilon)
      (by simpa using mul_pos (div_pos A.sin_theta_pos (by norm_num) : 0 < Real.sin A.theta/16) heps)).2
    have hs := upperFormFactor_iteratedDeriv_split (n+1) (Nat.succ_pos n) j hr hr1 hm
      c.leftWeight c.rightWeight c.left_smooth.continuous c.right_smooth.continuous
    simpa only [radialWeightedDerivative,sourceRadialPair,CompatibleYCutoffData.leftWeight,
      CompatibleYCutoffData.rightWeight,CompatibleYCutoffData.remainder,fixedYComplement] using hs
  obtain ⟨Ck,_,hCk⟩ := hComplement k
  have hComp : Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
      (fun epsilon => iteratedDeriv k (fun s => localizedDoubleFormFactor (n+1)
        (sourceRadialPair A.theta epsilon).1 s (fun u => c.remainder u.2))
        (sourceRadialPair A.theta epsilon).2)
      (fun epsilon => (epsilon:ℂ)⁻¹) := by
    apply bounded_radial_term_epsilon_isLittleO heC
    intro epsilon hp he
    simpa only [iteratedDeriv_eq_iterate,n,A] using! (hCk epsilon hp he)
  refine ⟨hL,?_⟩
  · apply ((hLeft.add hRight).add hComp).congr' ?_ (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with epsilon hp he
    rw [hSplit epsilon hp he k]
    ring

end
end IsingBulk.HT.First
