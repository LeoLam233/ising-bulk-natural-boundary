import IsingBulk.AnisoF002.C03.PhysicalRealFactors

/-!
# Continuity and exact angular periodicity of the complete canonical density

These statements concern the actual full particle integrand.  They
include the constrained last angle and the complete rational site factor,
and are used to identify the original iterated angular measures exactly.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators

theorem canonical_root_continuous_angles {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) : Continuous (spectralSmallRootF002 lam z) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (spectralSmallRootF002_continuousAt q hz).comp
    (f := fun t : ℝ => (z, t)) (continuousAt_const.prodMk continuousAt_id)

theorem canonical_root_product_norm_lt_one {N : ℕ} (hN : 0 < N) {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (q : Fin N → ℝ) :
    ‖∏ i, spectralSmallRootF002 lam z (q i)‖ < 1 := by
  obtain ⟨rho, hr0, hr1, hr⟩ := spectralSmallRootF002_compact_gap
    (isCompact_singleton (x := z)) (by simpa only [singleton_subset_iff, Set.mem_compl_iff] using hz)
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : Fin N, rho := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => hr z (mem_singleton z) (q i))
    _ = rho ^ N := by simp
    _ < 1 := pow_lt_one₀ hr0 hr1 (ne_of_gt hN)

theorem canonical_root_product_denominator {N : ℕ} (hN : 0 < N) {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (q : Fin N → ℝ) :
    1 - ∏ i, spectralSmallRootF002 lam z (q i) ≠ 0 := by
  intro he
  have hh := canonical_root_product_norm_lt_one hN hz q
  rw [← sub_eq_zero.mp he, norm_one] at hh
  exact (lt_irrefl _) hh

theorem canonical_numerator_continuous_angles {N : ℕ} {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (b : ℂ) :
    Continuous (fun q : Fin N → ℝ => fullRootNumeratorF002 lam z b q) := by
  have hr (i : Fin N) : Continuous (fun q : Fin N → ℝ => spectralSmallRootF002 lam z (q i)) :=
    (canonical_root_continuous_angles hz).comp (continuous_apply i)
  have hy (i : Fin N) : Continuous (fun q : Fin N → ℝ => Complex.exp ((q i : ℂ) * Complex.I)) := by
    fun_prop
  have hbody (i : Fin N) : Continuous (fun q : Fin N → ℝ => spectralOneBodyF002 lam z (q i)) := by
    apply (continuous_const.mul (hr i)).div (continuous_const.sub ((hr i).pow 2))
    intro q
    change 1 - spectralSmallRootF002 lam z (q i) ^ 2 ≠ 0
    simpa only [pow_two] using pair_root_denominator_ne_zero
      (spectralSmallRootF002_spec (q i) hz).2 (spectralSmallRootF002_spec (q i) hz).2
  have hpair (i j : Fin N) : Continuous (fun q : Fin N → ℝ =>
      spectralCanceledPairF002 lam z (q i) (q j)) := by
    unfold spectralCanceledPairF002 canceledPair
    apply (((continuous_const.mul (((hy i).sub (hy j)).pow 2)).mul (hr i)).mul (hr j)).div
      (((hy i).mul (hy j)).mul ((continuous_const.sub ((hr i).mul (hr j))).pow 2))
    intro q
    exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
      (pow_ne_zero _ (pair_root_denominator_ne_zero
        (spectralSmallRootF002_spec (q i) hz).2 (spectralSmallRootF002_spec (q j) hz).2))
  exact ((continuous_const.mul (continuous_finsetProd _ (fun i _ => hbody i))).mul
    (continuous_finsetProd _ (fun ij _ => hpair ij.1 ij.2)))

theorem canonical_density_continuous_angles {N : ℕ} (hN : 0 < N) {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) : Continuous (fun q : Fin N → ℝ =>
      canonicalAngularDensityF002 lam z q) := by
  have hr : Continuous (fun q : Fin N → ℝ => ∏ i, spectralSmallRootF002 lam z (q i)) :=
    continuous_finsetProd _ (fun i _ => (canonical_root_continuous_angles hz).comp (continuous_apply i))
  exact (canonical_numerator_continuous_angles hz _).mul
    ((continuous_const.add hr).div (continuous_const.sub hr)
      (canonical_root_product_denominator hN hz))

def realAngleExp (q : ℝ) : ℂ := Complex.exp ((q : ℂ) * Complex.I)

theorem realAngleExp_periodic : Function.Periodic realAngleExp (2 * Real.pi) := by
  intro q
  simp only [realAngleExp, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat,
    add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem cos_eq_of_realAngleExp_eq {q t : ℝ} (h : realAngleExp q = realAngleExp t) :
    Real.cos q = Real.cos t := by
  have hh := congrArg Complex.re h
  simpa only [realAngleExp, Complex.exp_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, mul_one, add_zero, Real.exp_zero, one_mul] using hh

theorem canonical_density_congr_angles {N : ℕ} {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (q t : Fin N → ℝ)
    (hy : ∀ i, realAngleExp (q i) = realAngleExp (t i)) :
    canonicalAngularDensityF002 lam z q = canonicalAngularDensityF002 lam z t := by
  have hr (i : Fin N) : spectralSmallRootF002 lam z (q i) = spectralSmallRootF002 lam z (t i) :=
    spectralSmallRootF002_eq_of_cos_eq hz (cos_eq_of_realAngleExp_eq (hy i))
  simp only [realAngleExp] at hy
  simp only [canonicalAngularDensityF002, fullRootNumeratorF002, spectralOneBodyF002,
    spectralCanceledPairF002, canceledPair, hr, hy]

theorem canonical_constrained_density_periodic {n : ℕ} {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) (q : Fin n → ℝ) (i : Fin n) :
    canonicalAngularDensityF002 lam z
      (flatConstrainedAngles (Function.update q i (q i + 2 * Real.pi))) =
        canonicalAngularDensityF002 lam z (flatConstrainedAngles q) := by
  apply canonical_density_congr_angles hz
  intro j
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

end
end IsingBulk.AnisoF002.RegularTail.C03
