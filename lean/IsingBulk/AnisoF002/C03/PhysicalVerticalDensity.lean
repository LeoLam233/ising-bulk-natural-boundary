import IsingBulk.AnisoF002.C03.PhysicalAngularIdentification
import IsingBulk.AnisoF002.C03.PhysicalLatticeIntegral

/-!
# The literal vertical-displacement angular density

The full finite numerator and every transfer-root power are retained.
Continuity, exact coordinate periodicity, and the integer geometric
majorant are derived from the actual canonical physical root.  They
justify the second lattice exchange after total-angle Fourier inversion.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory IsingBulk.First IsingBulk.Anisotropic
  IsingBulk.Anisotropic.FormFactors IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

def literalRealVerticalDensity {N : ℕ} (lam x : ℝ) (m : ℤ) (q : Fin N → ℝ) : ℂ :=
  ((angularWeight (realB lam x) (realC lam x) q *
    rootProduct (realB lam x) (realC lam x) q ^ m.natAbs : ℝ) : ℂ)

theorem literal_verticalDensity_eq_canonical {N : ℕ} {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (m : ℤ) (q : Fin N → ℝ) :
    literalRealVerticalDensity lam x m q =
      fullRootNumeratorF002 lam (x : ℂ) (Real.sqrt (realB lam x) : ℂ) q *
        (∏ i, spectralSmallRootF002 lam (x : ℂ) (q i)) ^ m.natAbs := by
  rw [canonical_numerator_eq_published_real hlam hx hp]
  simp only [literalRealVerticalDensity, rootProduct, canonical_root_eq_published_real hlam hx hp,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod]

theorem literal_verticalDensity_continuous {N : ℕ} {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (m : ℤ) :
    Continuous (literalRealVerticalDensity (N := N) lam x m) := by
  have hz := positive_real_not_mem_spectralSetF002 hlam hx hp
  have hroot : Continuous (fun q : Fin N → ℝ =>
      ∏ i, spectralSmallRootF002 lam (x : ℂ) (q i)) :=
    continuous_finsetProd _ (fun i _ => (canonical_root_continuous_angles hz).comp (continuous_apply i))
  have he : literalRealVerticalDensity (N := N) lam x m = fun q =>
      fullRootNumeratorF002 lam (x : ℂ) (Real.sqrt (realB lam x) : ℂ) q *
        (∏ i, spectralSmallRootF002 lam (x : ℂ) (q i)) ^ m.natAbs :=
    funext (literal_verticalDensity_eq_canonical hlam hx hp m)
  rw [he]
  exact (canonical_numerator_continuous_angles hz (Real.sqrt (realB lam x) : ℂ)).mul
    (hroot.pow m.natAbs)

theorem canonical_numerator_congr_angles {N : ℕ} {lam : ℝ} {z b : ℂ}
    (hz : z ∉ spectralSetF002 lam) (q t : Fin N → ℝ)
    (hy : ∀ i, realAngleExp (q i) = realAngleExp (t i)) :
    fullRootNumeratorF002 lam z b q = fullRootNumeratorF002 lam z b t := by
  have hr (i : Fin N) : spectralSmallRootF002 lam z (q i) = spectralSmallRootF002 lam z (t i) :=
    spectralSmallRootF002_eq_of_cos_eq hz (cos_eq_of_realAngleExp_eq (hy i))
  simp only [realAngleExp] at hy
  simp only [fullRootNumeratorF002, spectralOneBodyF002, spectralCanceledPairF002, canceledPair, hr, hy]

theorem literal_verticalDensity_congr_angles {N : ℕ} {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1)
    (m : ℤ) (q t : Fin N → ℝ) (hy : ∀ i, realAngleExp (q i) = realAngleExp (t i)) :
    literalRealVerticalDensity lam x m q = literalRealVerticalDensity lam x m t := by
  have hz := positive_real_not_mem_spectralSetF002 hlam hx hp
  have hr (i : Fin N) : spectralSmallRootF002 lam (x : ℂ) (q i) = spectralSmallRootF002 lam (x : ℂ) (t i) :=
    spectralSmallRootF002_eq_of_cos_eq hz (cos_eq_of_realAngleExp_eq (hy i))
  simp only [literal_verticalDensity_eq_canonical hlam hx hp,
    canonical_numerator_congr_angles hz q t hy, hr]

theorem literal_verticalDensity_periodic {N : ℕ} {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (m : ℤ) :
    CoordinatePeriodic N (literalRealVerticalDensity lam x m) := by
  intro q i
  apply literal_verticalDensity_congr_angles hlam hx hp
  intro j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    exact realAngleExp_periodic _
  · rw [Function.update_of_ne hji]

theorem literal_flatAngles_continuous (n : ℕ) : Continuous (flatConstrainedAngles (n := n)) := by
  unfold flatConstrainedAngles
  have hlast : Continuous (fun q : Fin n → ℝ => -(∑ i, q i)) :=
    (continuous_finsetSum Finset.univ fun i _ => continuous_apply i).neg
  exact continuous_id.finSnoc (A := fun _ : Fin (n + 1) => ℝ) hlast

theorem literal_flatAngles_update_exps {n : ℕ} (q : Fin n → ℝ) (i : Fin n)
    (j : Fin (n + 1)) :
    realAngleExp (flatConstrainedAngles (Function.update q i (q i + 2 * Real.pi)) j) =
      realAngleExp (flatConstrainedAngles q j) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [flatConstrainedAngles, Fin.snoc_last]
    have hsum : (∑ j, Function.update q i (q i + 2 * Real.pi) j) = ∑ j, q j + 2 * Real.pi := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i),
        Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i) q]
      ring
    rw [hsum, neg_add]
    exact realAngleExp_periodic.sub_eq _
  · simp only [flatConstrainedAngles, Fin.snoc_castSucc]
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      exact realAngleExp_periodic _
    · rw [Function.update_of_ne hji]

theorem literal_constrainedVerticalDensity_periodic {n : ℕ} {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (m : ℤ) :
    CoordinatePeriodic n (fun q => literalRealVerticalDensity lam x m (flatConstrainedAngles q)) := by
  intro q i
  exact literal_verticalDensity_congr_angles hlam hx hp m _ _ (literal_flatAngles_update_exps q i)

theorem literal_constrainedVerticalDensity_majorant (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) :
    ∃ C rho : ℝ, 0 ≤ C ∧ 0 ≤ rho ∧ rho < 1 ∧ ∀ m : ℤ, ∀ q ∈ regularAngularBox n,
      ‖literalRealVerticalDensity lam x m (flatConstrainedAngles q)‖ ≤ C * rho ^ m.natAbs := by
  have hz := positive_real_not_mem_spectralSetF002 hlam hx hp
  obtain ⟨rho, hr0, hr1, hr⟩ := spectralSmallRootF002_compact_gap
    (isCompact_singleton (x := (x : ℂ))) (by simpa only [singleton_subset_iff, Set.mem_compl_iff] using hz)
  obtain ⟨M, hM⟩ := (regularAngularBox_compact n).exists_bound_of_continuousOn
    ((canonical_numerator_continuous_angles hz (Real.sqrt (realB lam x) : ℂ)).comp
      (literal_flatAngles_continuous n)).continuousOn
  refine ⟨max M 0, rho, le_max_right _ _, hr0, hr1, ?_⟩
  intro m q hq
  have hprod : ‖∏ i, spectralSmallRootF002 lam (x : ℂ) (flatConstrainedAngles q i)‖ ≤ rho := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin (n + 1), rho := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => hr (x : ℂ) (mem_singleton _) (flatConstrainedAngles q i))
      _ = rho ^ (n + 1) := by simp
      _ ≤ rho := by rw [pow_succ]; exact mul_le_of_le_one_left hr0 (pow_le_one₀ hr0 hr1.le)
  rw [literal_verticalDensity_eq_canonical hlam hx hp, norm_mul, norm_pow]
  exact mul_le_mul ((hM q hq).trans (le_max_left M 0))
    (pow_le_pow_left₀ (norm_nonneg _) hprod _) (pow_nonneg (norm_nonneg _) _) (le_max_right _ _)

theorem literal_verticalDensity_tsum {N : ℕ} (hN : 0 < N) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) (q : Fin N → ℝ) :
    (∑' m : ℤ, literalRealVerticalDensity lam x m q) = canonicalAngularDensityF002 lam (x : ℂ) q := by
  have hz := positive_real_not_mem_spectralSetF002 hlam hx hp
  simp_rw [literal_verticalDensity_eq_canonical hlam hx hp]
  rw [tsum_mul_left, (literal_complex_integer_geometric (canonical_root_product_norm_lt_one hN hz q)).tsum_eq]
  have hsqrt : Complex.sqrt (spectralRatioF002 lam (x : ℂ)) = (Real.sqrt (realB lam x) : ℂ) := by
    rw [spectralRatio_real_f002, Complex.sqrt_of_nonneg (by exact_mod_cast (realB_pos_f002 hlam hx).le)]
    rfl
  simp only [canonicalAngularDensityF002, hsqrt]

theorem literal_constrainedVerticalDensity_integral_tsum (n : ℕ) {lam x : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x ≠ 1) :
    (∑' m : ℤ, ∫ q, literalRealVerticalDensity lam x m (flatConstrainedAngles q)
      ∂regularAngularProbability n) =
      ∫ q, canonicalAngularDensityF002 lam (x : ℂ) (flatConstrainedAngles q)
        ∂regularAngularProbability n := by
  let F (m : ℤ) (q : Fin n → ℝ) := literalRealVerticalDensity lam x m (flatConstrainedAngles q)
  obtain ⟨C, rho, hC, hr0, hr1, hb⟩ := literal_constrainedVerticalDensity_majorant n hlam hx hp
  have hi (m : ℤ) : Integrable (F m) (regularAngularProbability n) := by
    apply Integrable.mono' (integrable_const (C * rho ^ m.natAbs))
      (((literal_verticalDensity_continuous hlam hx hp m).comp (literal_flatAngles_continuous n)).aestronglyMeasurable)
    filter_upwards [regularAngularProbability_ae_mem n] with q hq
    exact hb m q hq
  have hs : Summable (fun m : ℤ => ∫ q, ‖F m q‖ ∂regularAngularProbability n) := by
    apply ((literal_integer_geometric_summable hr0 hr1).mul_left C).of_nonneg_of_le
    · intro m
      exact integral_nonneg (fun _ => norm_nonneg _)
    · intro m
      calc
        _ ≤ ∫ _q : Fin n → ℝ, C * rho ^ m.natAbs ∂regularAngularProbability n := by
          apply integral_mono_ae (hi m).norm (integrable_const _)
          filter_upwards [regularAngularProbability_ae_mem n] with q hq
          exact hb m q hq
        _ = _ := by simp
  change (∑' m : ℤ, ∫ q, F m q ∂regularAngularProbability n) = _
  rw [integral_tsum_of_summable_integral_norm hi hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun q => literal_verticalDensity_tsum (Nat.succ_pos n) hlam hx hp _)

end
end IsingBulk.AnisoF002.RegularTail.C03
