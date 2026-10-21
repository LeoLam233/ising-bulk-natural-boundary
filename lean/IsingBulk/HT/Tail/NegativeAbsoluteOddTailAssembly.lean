import IsingBulk.HT.Tail.NegativeIntermediateWindowAssembly
import IsingBulk.HT.Tail.NoncancellationBridge
import IsingBulk.HT.Contour.SignedReflectionJets

/-! The complete reflected odd offsite tail at every HT derivative order.
All source sectors are constructed internally. Reflection is an exact
identity of actual fixed-radius germs, so it introduces no N-dependent cost. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Contour
open Filter Asymptotics MeasureTheory Set
open scoped Topology

theorem negative_ht_common_source_odd_tail_small {p order : ℕ} {d : LocalBranchData}
    (cfg : NegativeHTCommonAllSectorParameters p d order) (hp : Odd p)
    (j : ℕ) (hj : j ≤ order) :
    (∀ᶠ ε : ℝ in 𝓝[>] 0,Summable (fun n : ℕ =>
      ‖iteratedDeriv j (signedSourceIntegral (-1) (oddTailParticle p n)
        (Real.exp (-d.c₀*ε))) (radialParameter d.theta ε)‖)) ∧
    (fun ε : ℝ => ∑' n : ℕ,
      ‖iteratedDeriv j (signedSourceIntegral (-1) (oddTailParticle p n)
        (Real.exp (-d.c₀*ε))) (radialParameter d.theta ε)‖)
      =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε)⁻¹) := by
  have hhigh := radial_tendsto_littleO_inv_sqrt (cfg.high_tendsto j hj)
  have hmiddle := negative_ht_common_intermediateOddKSNormWindow_littleO cfg j hj
  have htotal := (((cfg.f_small j hj).add (cfg.large_small j hj)).add hmiddle).add hhigh
  obtain ⟨e,he,hsource⟩ := cfg.source_summability
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Summable (fun n : ℕ => ‖iteratedDeriv j
        (signedSourceIntegral (-1) (oddTailParticle p n) (Real.exp (-d.c₀*ε)))
        (radialParameter d.theta ε)‖) ∧
      (∑' n : ℕ,‖iteratedDeriv j
        (signedSourceIntegral (-1) (oddTailParticle p n) (Real.exp (-d.c₀*ε)))
        (radialParameter d.theta ε)‖) ≤
      (∑' n : ℕ,‖iteratedDeriv j
        (signedSelectedIntegral (-1) (2*n+1) (constructedSelector d.thetaB cfg.eta d.alpha)
          (Real.exp (-d.c₀*ε)) d.tau) (radialParameter d.theta ε)‖) +
      (∑' n : ℕ,‖∫ lam in (ε^cfg.beta)..1,
        signedDifferentiatedCurrentSlice (-1) (2*n+1) (constructedSelector d.thetaB cfg.eta d.alpha)
          (Real.exp (-d.c₀*ε)) d.tau lam j (radialParameter d.theta ε)‖) +
      negativeIntermediateOddKSNormWindow p d cfg.eta d.alpha d.tau j cfg.D ε (ε^cfg.beta) +
      signedHighKSNormTail (-1) d cfg.eta d.alpha d.tau j cfg.D ε (ε^cfg.beta) := by
    filter_upwards [self_mem_nhdsWithin,
      radial_power_cutoff_eventually_pos_le_one cfg.beta_pos.le,
      radial_source_eventually_damping d cfg.c0_small,
      (show ∀ᶠ ε : ℝ in 𝓝[>] 0,ε<e from
        mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he))]
      with ε hε hcut hdom hsmall
    obtain ⟨hF,hL,hK⟩ := hsource j hj ε (ε^cfg.beta) hε hsmall hcut.1 hcut.2
    exact signed_actual_higher_odd_tail_domination (-1) (by norm_num) hp d
      cfg.eta d.alpha d.tau cfg.D ε (ε^cfg.beta) cfg.selector_regular d.tau_pos.le
      hε ⟨hcut.1.le,hcut.2⟩ hdom.2.2 j hF hL hK
  exact ⟨hbound.mono (fun _ h => h.1),
    radial_tsum_littleO_of_nonnegative_domination (fun _ _ => norm_nonneg _)
      (hbound.mono (fun _ h => h.2)) htotal⟩

theorem negative_ht_common_absoluteUpperOddTailSmall {p order : ℕ} {d : LocalBranchData}
    (cfg : NegativeHTCommonAllSectorParameters p d order) (hp : Odd p)
    (j : ℕ) (hj : j ≤ order) :
    AbsoluteUpperOddTailSmall p (Real.pi-d.theta) j := by
  have hsmall := (negative_ht_common_source_odd_tail_small cfg hp j hj).2
  apply hsmall.congr'
  · filter_upwards [radial_source_eventually_damping d cfg.c0_small] with ε hdom
    apply tsum_congr
    intro n
    have hNodd : Odd (oddTailParticle p n) :=
      ((mem_oddTailParticle_range hp).mp ⟨n,rfl⟩).2
    have hNpos : 0 < oddTailParticle p n := by dsimp [oddTailParticle]; omega
    exact (upperFormFactor_reflected_radial_odd_iteratedDeriv_norm (oddTailParticle p n)
      hNodd hNpos (constructedSelector d.thetaB cfg.eta d.alpha)
      (Real.exp (-d.c₀*ε)) d.tau d.theta ε hdom.1 hdom.2.1 hdom.2.2.2 j).symm
  · exact Eventually.of_forall (fun _ => rfl)

/-- All odd particle numbers strictly above p, and every derivative through
(p²−1)/2, at the reflection of a positive selected point. The original negative integer-angle
family is handled separately in NegativeOriginalOddTailAssembly. -/
theorem selected_negative_absolute_upper_odd_tail_small {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (_hab : a ≠ b) :
    ∀ j : ℕ,j ≤ (p^2-1)/2 →
      AbsoluteUpperOddTailSmall p (Real.pi-(selectedOrderedChart ha hb).theta) j := by
  obtain ⟨tau,alpha,htau,halpha,⟨cfg⟩⟩ :=
    negative_ht_common_all_sector_parameters hp ha hb ((p^2-1)/2) le_rfl
  intro j hj
  simpa only [selectedLocalBranchData_theta] using
    negative_ht_common_absoluteUpperOddTailSmall cfg (hp.odd_of_ne_two (by omega)) j hj

/-- The reflected target norm series converges at every positive radial
parameter and every finite derivative order, independently of asymptotics. -/
theorem selected_negative_upper_odd_tail_summable {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n))
      (radialParameter (Real.pi-(selectedOrderedChart ha hb).theta) ε)‖) := by
  exact actual_upper_odd_tail_summable (hp.odd_of_ne_two (by omega)) j
    (by simpa only [Real.sin_pi_sub] using (selectedOrderedChart ha hb).sin_theta_pos) hε

theorem selected_negative_complex_upper_odd_tail_small {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (hab : a ≠ b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    (fun ε : ℝ => ∑' n : ℕ,iteratedDeriv j (upperFormFactor (oddTailParticle p n))
      (radialParameter (Real.pi-(selectedOrderedChart ha hb).theta) ε))
      =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε:ℂ)⁻¹) := by
  apply complex_odd_tail_small_of_absolute (hp.odd_of_ne_two (by omega))
    (by simpa only [Real.sin_pi_sub] using (selectedOrderedChart ha hb).sin_theta_pos) j
  exact selected_negative_absolute_upper_odd_tail_small hp hp11 ha hb hab j hj

theorem selected_negative_upper_odd_tail_epsilon_zero {p : ℕ} (hp : p.Prime)
    (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (hab : a ≠ b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    Tendsto (fun ε : ℝ => ε • ∑' n : ℕ,
      iteratedDeriv j (upperFormFactor (oddTailParticle p n))
        (radialParameter (Real.pi-(selectedOrderedChart ha hb).theta) ε))
      (𝓝[>] 0) (𝓝 (0:ℂ)) :=
  epsilon_smul_tendsto_zero_of_invSqrt_littleO
    (selected_negative_complex_upper_odd_tail_small hp hp11 ha hb hab j hj)

end
end IsingBulk.HT.Tail
