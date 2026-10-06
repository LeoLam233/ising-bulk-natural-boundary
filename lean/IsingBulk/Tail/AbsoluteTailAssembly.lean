import IsingBulk.Tail.IntermediateWindowAssembly
import IsingBulk.Tail.RadialSourceDomain
import IsingBulk.Final.UpperNoncancellation

/-! Assembly of the actual absolute higher-even tail at the FIRST scale.
All source estimates use the same selector parameters. Absolute values
remain inside the infinite sum throughout the argument. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Asymptotics MeasureTheory Set
open scoped Topology

/-- The source current cutoff is strictly positive and belongs to the legal
unit interval on one eventual radial neighborhood. -/
theorem radial_power_cutoff_eventually_pos_le_one {beta : ℝ} (hbeta : 0 ≤ beta) :
    ∀ᶠ eps : ℝ in 𝓝[>] 0, 0 < eps^beta ∧ eps^beta ≤ 1 := by
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < 1 from
      mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds (zero_lt_one : (0:ℝ)<1)))]
    with eps heps heps1
  exact ⟨Real.rpow_pos_of_pos heps _, Real.rpow_le_one heps.le heps1.le hbeta⟩

/-- A finite radial limit is negligible compared with the FIRST singular
scale. This is used with the internally proved high-KS limit at Q = 0. -/
theorem radial_tendsto_littleO_inv_sqrt {f : ℝ → ℝ} {L : ℝ}
    (hf : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 L)) :
    f =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  have hone : (fun _ : ℝ => (1:ℝ)) =o[𝓝[>] 0]
      (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
    simpa only [zero_mul, Real.exp_zero] using radial_log_square_growth_littleO 0
  exact (hf.isBigO_one ℝ).trans_isLittleO hone

/-- Domination is applied to an infinite sum of nonnegative source terms,
not to a complex sum and not to individual particle orders. -/
theorem radial_tsum_littleO_of_nonnegative_domination
    {E : ℝ → ℕ → ℝ} {G : ℝ → ℝ}
    (hE : ∀ eps N, 0 ≤ E eps N)
    (hbound : ∀ᶠ eps : ℝ in 𝓝[>] 0, (∑' N : ℕ, E eps N) ≤ G eps)
    (hG : G =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹)) :
    (fun eps : ℝ => ∑' N : ℕ, E eps N) =o[𝓝[>] 0]
      (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  apply IsBigO.trans_isLittleO (g := G) _ hG
  apply IsBigO.of_bound'
  filter_upwards [hbound] with eps hb
  calc
    ‖∑' N : ℕ, E eps N‖ = ∑' N : ℕ, E eps N :=
      Real.norm_of_nonneg (tsum_nonneg (hE eps))
    _ ≤ G eps := hb
    _ ≤ ‖G eps‖ := le_abs_self _

/-- The exact target sequence is genuinely summable at every positive
radial parameter. In particular its `tsum` is never used as a substitute
for convergence in the tail argument. -/
theorem actual_upper_tail_summable (p j : ℕ) {theta eps : ℝ}
    (htheta : 0 < Real.sin theta) (heps : 0 < eps) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperFormFactor (2*(n+p+1)))
      (radialParameter theta eps)‖) := by
  exact (upperEven_derivative_summable j
    (IsingBulk.Final.sourceRadialTrace_pos htheta heps)).comp_injective
      (show Function.Injective (fun n : ℕ => n+p) from
        fun _ _ h => Nat.add_right_cancel h)

/-- All completed source sectors and the exact intermediate window combine
at one common selector, current cutoff and particle threshold. The structure
argument is constructed internally by `common_all_sector_parameters`. -/
theorem common_absoluteUpperTailSmall {p order : ℕ} {d : LocalBranchData}
    (cfg : CommonAllSectorParameters p d order) (j : ℕ) (hj : j ≤ order) :
    IsingBulk.Final.AbsoluteUpperTailSmall p d.theta j := by
  have hhigh := radial_tendsto_littleO_inv_sqrt (cfg.high_tendsto j hj)
  have hmiddle := common_intermediateKSNormWindow_littleO cfg j hj
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
  obtain ⟨hF, hL, hK⟩ := hsource j hj eps (eps^cfg.beta) heps hsmall hcut.1 hcut.2
  exact actual_higher_tail_domination p d cfg.eta d.alpha d.tau cfg.D eps (eps^cfg.beta)
    cfg.selector_regular d.tau_pos.le heps ⟨hcut.1.le, hcut.2⟩ hdamping.2.2 j hF hL hK

/-- The requested all-order absolute tail for the actual selected prime
family. The infinite norm series and the full derivative ceiling are kept
literally; no physical or fixed-order smoothness input is used here. -/
theorem selected_absolute_upper_tail_small {p : ℕ} (hp : p.Prime) (_hp11 : 11 ≤ p)
    {a b : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (_hab : a ≠ b) :
    ∀ j : ℕ, j ≤ (2*p)^2/2-1 →
      IsingBulk.Final.AbsoluteUpperTailSmall p (selectedOrderedChart ha hb).theta j := by
  obtain ⟨tau, alpha, htau, halpha, ⟨cfg⟩⟩ :=
    common_all_sector_parameters hp ha hb ((2*p)^2/2-1) le_rfl
  intro j hj
  simpa only [selectedLocalBranchData_theta] using common_absoluteUpperTailSmall cfg j hj

end
end IsingBulk.Tail
