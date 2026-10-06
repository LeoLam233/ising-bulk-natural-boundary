import IsingBulk.Tail.AllBranchExteriorNearSourceBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie
open scoped ContDiff BigOperators
set_option maxHeartbeats 800000

def allBranchExteriorFarNumeratorCost (A : ℝ) (j N : ℕ) : ℝ :=
  (2:ℝ)^j*((2:ℝ)^j*((2^j*A)^N+(2^j*A)^N)*
    (A^j*((N.choose 2:ℝ)+1)^j*(1/2:ℝ)^((N.choose 2:ℤ)-(j:ℤ))))*(2^j*A)^N

def allBranchExteriorFarLocalCost (j N G C : ℕ) (D c A W σ : ℝ) : ℝ :=
  (3+3*N:ℝ)^j*((2^j*((2^j*(G:ℝ)*(N:ℝ)^G*D)*(max 1 c⁻¹)^(2*j))*W)/σ^(2*j)*
    ((C:ℝ)*(N:ℝ)^C)*allBranchExteriorFarNumeratorCost A j N)

/-- The actual far-source sum retains the Gaussian pair-product factor.
All losses of separation are explicit and uniform in the artificial puncture. -/
theorem allBranchExterior_far_source_budget (d : LocalBranchData) (j : ℕ) :
    ∃ G C : ℕ, 0 < G ∧ 0 < C ∧ ∃ D c A r : ℝ,
      1 ≤ D ∧ 0 < c ∧ 1 ≤ A ∧ 0 < r ∧ ∀ ε : ℝ, 0 < ε → ε ≤ r →
      ∀ n : ℕ, ∀ p q : Fin (n+1), p ≠ q → ∀ h : ℝ, 0 < h →
      ∀ w : AngularSpace n → ℝ, ContDiff ℝ ∞ w →
      ∀ u : AngularSpace n, (∀ i, |u i| ≤ r) → u p ≠ u q →
      ∀ σ W : ℝ, 0 < σ → σ ≤ 1 → 0 ≤ W → σ ≤ allBranchExteriorDiameter u →
      (∀ l : List (Fin (n+1)), l.length ≤ j →
        ‖cutoffJet l w u‖ ≤ W/allBranchExteriorDiameter u^l.length) →
      ‖sourceTermSum p q (-d.c₀*ε) d.thetaB (allBranchSingleTruncatedWeight (j+1) h p q w)
        (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2)) j
        (radialParameter d.theta ε) u‖ ≤
        allBranchExteriorFarLocalCost j (n+1) G C D c A W σ*allBranchExteriorKernelDensity d ε u := by
  obtain ⟨G,hG,D,c,rG,hD,hc,hrG,hguard⟩ := allBranchExterior_single_truncated_pole d (j+1) j (by omega) (by omega)
  obtain ⟨C,hC,rC,hrC,hcoeff⟩ := allBranchExterior_original_coefficients d j 0
  obtain ⟨A,rA,hA,hrA,hnum⟩ := allBranchExterior_original_numerator_jets d j
  obtain ⟨rM,hrM,hchart⟩ := original_microcore_chart d
  let r := min rG (min rC (min rA rM))/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : r < rG ∧ r < rC ∧ r < rA ∧ r < rM := by
    have hh : r < min rG (min rC (min rA rM)) := half_lt_self (lt_min hrG (lt_min hrC (lt_min hrA hrM)))
    simpa only [lt_min_iff] using hh
  refine ⟨G,C,hG,hC,D,c,A,r,hD,hc,hA,hr,?_⟩
  intro ε hε hεr n p q hpq h hh w hw u hu hupq σ W hσ hσ1 hW hsep hwjets
  have hp := hchart ε hε (hεr.trans_lt hs.2.2.2) n u (fun i => (hu i).trans_lt hs.2.2.2)
  let W₀ := 2^j*((2^j*(G:ℝ)*(n+1:ℝ)^G*D)*(max 1 c⁻¹)^(2*j))*W
  let C₀ := (C:ℝ)*(n+1:ℝ)^C
  let A₀ := allBranchExteriorFarNumeratorCost A j (n+1)
  have hW₀ : 0 ≤ W₀ := by dsimp [W₀]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hterms (T : SourceJetTerm (n+1)) (hT : T ∈ sourceJetTerms p q j) :
      ‖T.sourceValue p q (-d.c₀*ε) d.thetaB (allBranchSingleTruncatedWeight (j+1) h p q w)
        (unfactoredNumerator (fun t : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude t.1 t.2))
        (radialParameter d.theta ε) u‖ ≤
        (W₀/σ^(2*j)*C₀*A₀)*allBranchExteriorKernelDensity d ε u := by
    have ht := sourceJetTerms_valid p q j T hT
    have hd := mixed_word_degree T.numerator
    have hcut : T.cutoff.length ≤ j := by omega
    have hlen : T.numerator.length ≤ j := by omega
    have hm : T.pole+T.cutoff.length ≤ 2*j := by omega
    have hguardT := hguard ε hε (hεr.trans hs.1.le) (n+1) (by omega) h hh p q u
      (fun i => (hu i).trans hs.1.le) hupq w hw W hW hwjets T.cutoff hcut T.pole (by omega)
    have hpow : (c⁻¹)^T.pole ≤ (max 1 c⁻¹)^(2*j) :=
      (pow_le_pow_left₀ (inv_nonneg.mpr hc.le) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    have hden : σ^(2*j) ≤ allBranchExteriorDiameter u^(T.pole+T.cutoff.length) :=
      (pow_le_pow_of_le_one hσ.le hσ1 hm).trans (pow_le_pow_left₀ hσ.le hsep _)
    have hwT : ‖cutoffJet T.cutoff (allBranchSingleTruncatedWeight (j+1) h p q w) u‖/
        ‖selectedDifferenceCLM p q (radialParameter d.theta ε,
          chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖^T.pole ≤ W₀/σ^(2*j) := by
      change ‖cutoffJet T.cutoff (allBranchSingleTruncatedWeight (j+1) h p q w) u‖/
        ‖chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u q-
          chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u p‖^T.pole ≤ _
      rw [original_chartMap_eq,norm_sub_rev]
      apply hguardT.trans
      apply div_le_div₀ (by positivity) _ (pow_pos hσ _) hden
      dsimp [W₀]
      push_cast
      gcongr
    have hreg := ((hcoeff ε hε (hεr.trans hs.2.1.le) (n+1) (by omega) p q hpq).2 u
      (fun i => (hu i).trans hs.2.1.le) T hT).bound 0 (by omega)
    have hnumT := allBranchExterior_numerator_word_bound _ _ j A₀
      (hnum ε hε (hεr.trans hs.2.2.1.le) (n+1) u (fun i => (hu i).trans hs.2.2.1.le)) T.numerator hlen
    have hb := allBranchExterior_sourceTerm_norm T p q (-d.c₀*ε) d.thetaB _ _
      (radialParameter d.theta ε) u (W₀/σ^(2*j)) C₀ A₀ (by positivity) hC₀ hwT
      (by simpa only [original_chartMap_eq,norm_iteratedFDeriv_zero,Nat.cast_add,Nat.cast_one] using hreg)
      (by simpa only [original_chartMap_eq] using hnumT)
    have hrφ (i : Fin (n+1)) : 0 < (originalW d ε (u i)).re := by
      simpa only [original_chartW_eq] using hp.re_pos i
    have hiφ (i : Fin (n+1)) : 0 < (originalW d ε (u i)).im := by
      simpa only [original_chartW_eq] using hp.im_pos i
    rw [original_chartJacobian_norm d ε u hrφ hiφ,original_chartMap_eq] at hb
    exact hb.trans_eq (by unfold allBranchExteriorKernelDensity; ring)
  have hh := allBranchExterior_source_sum_norm p q j (-d.c₀*ε) d.thetaB _ _
    (radialParameter d.theta ε) u _ hterms
  change ‖sourceTermSum p q (-d.c₀*ε) d.thetaB _ _ j (radialParameter d.theta ε) u‖ ≤ _ at hh
  apply hh.trans_eq
  unfold allBranchExteriorFarLocalCost
  dsimp [W₀,C₀,A₀]
  push_cast
  ring

end
end IsingBulk.Tail
