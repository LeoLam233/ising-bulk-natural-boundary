import IsingBulk.Tail.AllBranchExteriorCollisionPower
import IsingBulk.Tail.AllBranchExteriorOriginalAmplitude
import IsingBulk.Tail.AllBranchExteriorTruncatedPole

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff
set_option maxHeartbeats 800000

def allBranchExteriorNearLocalCost (j N G C : ℕ) (D c A W H : ℝ) : ℝ :=
  (3+3*N:ℝ)^j*((2^j*((2^j*(G:ℝ)*(N:ℝ)^G*D)*(max 1 c⁻¹)^(2*j))*W)*
    ((C:ℝ)*(N:ℝ)^C)*allBranchExteriorNearNumeratorCost A j N*H^(N*(N-1)))

/-- The entire actual generated near-source sum has a common bound independent
of the artificial pair-cutoff scale. Only the spatial weight jets are left
abstract here; the chart-cutoff theorem supplies them for the source partition. -/
theorem allBranchExterior_near_source_budget {d : LocalBranchData} (B : BranchEstimates d) (j : ℕ) :
    ∃ G C : ℕ, 0 < G ∧ 0 < C ∧ ∃ D c A r : ℝ,
      1 ≤ D ∧ 0 < c ∧ 0 < A ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ n : ℕ, 2*j ≤ (n+1)*n → ∀ p q : Fin (n+1), p ≠ q →
      ∀ h : ℝ, 0 < h → ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      ∀ u : AngularSpace n, (∀ i, |u i| ≤ r) → u p ≠ u q →
      ∀ a H W : ℝ, 0 < a → 1 ≤ H → B.magnitudeUpper/Real.sqrt a ≤ H → 0 ≤ W →
      ((∀ i, a ≤ u i) ∨ (∀ i, u i ≤ -a)) →
      allBranchExteriorDiameter u ≤ 1 → H*allBranchExteriorDiameter u ≤ 1 →
      (∀ l : List (Fin (n+1)), l.length ≤ j →
        ‖cutoffJet l w u‖ ≤ W/allBranchExteriorDiameter u^l.length) →
      ‖sourceTermSum p q (-d.c₀*ε) d.thetaB (allBranchSingleTruncatedWeight (j+1) h p q w)
        (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) j
        (radialParameter d.theta ε) u‖ ≤
        allBranchExteriorNearLocalCost j (n+1) G C D c A W H*
          allBranchExteriorDiameter u^((n+1)*n-2*j)*allBranchExteriorKernelDensity d ε u := by
  obtain ⟨G,hG,D,c,rG,hD,hc,hrG,hguard⟩ := allBranchExterior_single_truncated_pole d (j+1) j (by omega) (by omega)
  obtain ⟨C,hC,rC,hrC,hcoeff⟩ := allBranchExterior_original_coefficients d j 0
  obtain ⟨A,rA,hA,hrA,hnum⟩ := allBranchExterior_original_near_numerator B j
  obtain ⟨rM,hrM,hchart⟩ := original_microcore_chart d
  let r := min rG (min rC (min rA rM))/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : r < rG ∧ r < rC ∧ r < rA ∧ r < rM := by
    have hh : r < min rG (min rC (min rA rM)) := half_lt_self (lt_min hrG (lt_min hrC (lt_min hrA hrM)))
    simpa only [lt_min_iff] using hh
  refine ⟨G,C,hG,hC,D,c,A,r,hD,hc,hA,hr,?_⟩
  intro ε hε hεr n hP p q hpq h hh w hw u hu hupq a H W ha hH hHmag hW hsign hdiam1 hHD hwjets
  have hdiam : 0 < allBranchExteriorDiameter u :=
    (abs_pos.mpr (sub_ne_zero.mpr hupq)).trans_le (allBranchExterior_pair_le_diameter u p q)
  have hp := hchart ε hε (hεr.trans_lt hs.2.2.2) n u (fun i => (hu i).trans_lt hs.2.2.2)
  let W₀ := 2^j*((2^j*(G:ℝ)*(n+1:ℝ)^G*D)*(max 1 c⁻¹)^(2*j))*W
  let C₀ := (C:ℝ)*(n+1:ℝ)^C
  let A₀ := allBranchExteriorNearNumeratorCost A j (n+1)
  have hW₀ : 0 ≤ W₀ := by dsimp [W₀]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hA₀ : 0 ≤ A₀ := by unfold A₀ allBranchExteriorNearNumeratorCost; positivity
  have hterms (T : SourceJetTerm (n+1)) (hT : T ∈ sourceJetTerms p q j) :
      ‖T.sourceValue p q (-d.c₀*ε) d.thetaB (allBranchSingleTruncatedWeight (j+1) h p q w)
        (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
        (radialParameter d.theta ε) u‖ ≤
        (W₀*C₀*A₀*H^((n+1)*n))*allBranchExteriorDiameter u^((n+1)*n-2*j)*allBranchExteriorKernelDensity d ε u := by
    have ht := sourceJetTerms_valid p q j T hT
    have hdegree := mixed_word_degree T.numerator
    have hcut : T.cutoff.length ≤ j := by omega
    have hlen : T.numerator.length ≤ j := by omega
    have hm : T.pole ≤ 2*j := by omega
    have hguardT := hguard ε hε (hεr.trans hs.1.le) (n+1) (by omega) h hh p q u
      (fun i => (hu i).trans hs.1.le) hupq w hw W hW hwjets T.cutoff hcut T.pole (by omega)
    have hpow : (c⁻¹)^T.pole ≤ (max 1 c⁻¹)^(2*j) :=
      (pow_le_pow_left₀ (inv_nonneg.mpr hc.le) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hm)
    have hwT : ‖cutoffJet T.cutoff (allBranchSingleTruncatedWeight (j+1) h p q w) u‖/
        ‖selectedDifferenceCLM p q (radialParameter d.theta ε,
          chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖^T.pole ≤
        W₀/allBranchExteriorDiameter u^(T.pole+T.cutoff.length) := by
      change ‖cutoffJet T.cutoff (allBranchSingleTruncatedWeight (j+1) h p q w) u‖/
        ‖chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u q-
          chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u p‖^T.pole ≤ _
      rw [original_chartMap_eq,norm_sub_rev]
      apply hguardT.trans
      apply div_le_div_of_nonneg_right _ (pow_nonneg hdiam.le _)
      dsimp [W₀]
      push_cast
      gcongr
    have hreg := ((hcoeff ε hε (hεr.trans hs.2.1.le) (n+1) (by omega) p q hpq).2 u
      (fun i => (hu i).trans hs.2.1.le) T hT).bound 0 (by omega)
    have hnumT := hnum ε hε (hεr.trans hs.2.2.1.le) (n+1) (by omega) (by simp only [Nat.add_sub_cancel]; omega)
      u (fun i => (hu i).trans hs.2.2.1.le) a H ha hH hHmag hsign hdiam hHD T.numerator hlen
    apply allBranchExterior_source_term_collision_power d ε p q j T hT _ _ u hp hP hdiam hdiam1 H W₀ C₀ A₀
      hH hW₀ hC₀ hA₀ hwT
    · simpa only [original_chartMap_eq,norm_iteratedFDeriv_zero,Nat.cast_add,Nat.cast_one] using hreg
    · simpa only [original_chartMap_eq,Nat.add_sub_cancel] using hnumT
  have hh := allBranchExterior_source_sum_norm p q j (-d.c₀*ε) d.thetaB
    (allBranchSingleTruncatedWeight (j+1) h p q w)
    (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
    (radialParameter d.theta ε) u _ hterms
  change ‖sourceTermSum p q (-d.c₀*ε) d.thetaB _ _ j (radialParameter d.theta ε) u‖ ≤ _ at hh
  apply hh.trans_eq
  unfold allBranchExteriorNearLocalCost
  dsimp [W₀,C₀,A₀]
  push_cast
  ring

end
end IsingBulk.Tail
