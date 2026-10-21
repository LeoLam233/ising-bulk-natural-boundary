import IsingBulk.HT.Tail.IntermediateWindowAssembly
import IsingBulk.Tail.AbsoluteTailAssembly

/-!
# Positive-family complete differentiated odd offsite tail

This endpoint concerns the literal offsite coefficients `T_N` on the
positive-kernel upper-trace chart. The tail contains every odd N>p and
every j≤(p²−1)/2. Its proof constructs the source-sector estimates and
does not receive a tail-smallness or analytic certificate hypothesis.

The full C_N=f_N+2T_N boundary-uniform tail and the original negative
family are assembled in separate HT modules. The physical susceptibility
conclusion is outside this leaf.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Filter Asymptotics MeasureTheory Set
open scoped Topology

/-- All actual positive-kernel source sectors combine at common parameters.
`cfg` is constructed in the theorem below, not left as an external input to
the selected-family endpoint. -/
theorem ht_common_absoluteUpperOddTailSmall {p order : ℕ} {d : LocalBranchData}
    (cfg : HTCommonAllSectorParameters p d order) (hp : Odd p)
    (j : ℕ) (hj : j ≤ order) :
    AbsoluteUpperOddTailSmall p d.theta j := by
  have hhigh := radial_tendsto_littleO_inv_sqrt (cfg.high_tendsto j hj)
  have hmiddle := ht_common_intermediateOddKSNormWindow_littleO cfg j hj
  have htotal := (((cfg.f_small j hj).add (cfg.large_small j hj)).add hmiddle).add hhigh
  apply radial_tsum_littleO_of_nonnegative_domination
    (fun _ _ => norm_nonneg _) _ htotal
  obtain ⟨e, he, hsource⟩ := cfg.source_summability
  filter_upwards [self_mem_nhdsWithin,
    radial_power_cutoff_eventually_pos_le_one cfg.beta_pos.le,
    radial_source_eventually_damping d cfg.c0_small,
    (show ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < e from
      mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he))]
    with eps heps hcut hdamping hsmall
  obtain ⟨hF, hL, hK⟩ := hsource j hj eps (eps ^ cfg.beta)
    heps hsmall hcut.1 hcut.2
  exact actual_higher_odd_tail_domination hp d cfg.eta d.alpha d.tau cfg.D eps
    (eps ^ cfg.beta) cfg.selector_regular d.tau_pos.le heps
    ⟨hcut.1.le, hcut.2⟩ hdamping.2.2 j hF hL hK

/-- The whole infinite odd offsite tail on the actual selected positive
family. This is not a finite truncation and has no unproved tail premise.
The odd first order and the HT derivative ceiling occur literally. -/
theorem selected_absolute_upper_odd_tail_small {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (_hab : a ≠ b) :
    ∀ j : ℕ, j ≤ (p ^ 2 - 1) / 2 →
      AbsoluteUpperOddTailSmall p (selectedOrderedChart ha hb).theta j := by
  obtain ⟨tau, alpha, htau, halpha, ⟨cfg⟩⟩ :=
    ht_common_all_sector_parameters hp ha hb ((p ^ 2 - 1) / 2) le_rfl
  intro j hj
  simpa only [selectedLocalBranchData_theta] using
    ht_common_absoluteUpperOddTailSmall cfg (hp.odd_of_ne_two (by omega)) j hj

end
end IsingBulk.HT.Tail
