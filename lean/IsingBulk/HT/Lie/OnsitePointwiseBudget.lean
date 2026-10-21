import IsingBulk.HT.Lie.OnsiteActualExpansion
import IsingBulk.HT.Lie.OnsiteVelocityJets
import IsingBulk.Tail.MixedDensityPointwiseBudget
import IsingBulk.Tail.MixedSourceNormalization
import IsingBulk.Tail.MixedActualDensityBound

/-! Sparse onsite descendants have only polynomial dimension cost. The
whole branch volume remains exposed for its actual L1 estimate. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem onsiteJetTerms_pointwise_budget {N : ℕ} (J : Finset (Fin N))
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (w : (Fin N → ℝ) → ℝ) (F : MixedActiveSpace N → ℂ)
    (order k : ℕ) (hk : k≤order) (A B D : ℝ) (hA : 1≤A)
    (hV : ∀ i,JetBound (onsiteActiveVelocity J s
      (fun i => mixedContourPhase f r τ lam s θ i) i) 0 order A)
    (hF : JetBound F 0 order D)
    (hcut : ∀ l : List (Fin N),l.length≤k → |cutoffJet l w θ|≤B) :
    let φ := fun i => mixedContourPhase f r τ lam s θ i
    ‖((onsiteJetTerms J s φ F k).map
      (fun T => T.onsiteValue J f r τ lam s φ w s θ)).sum‖≤
      ((N+1:ℕ):ℝ)^k*(B*‖mixedHybridVolume J f r τ lam s θ‖*
        ((1+4*2^order*A)^k*D)) := by
  let φ := fun i => mixedContourPhase f r τ lam s θ i
  let L := onsiteJetTerms J s φ F k
  let P := ‖mixedHybridVolume J f r τ lam s θ‖
  let M := (1+4*2^order*A)^k*D
  have hP : 0≤P := norm_nonneg _
  have hB : 0≤B := (abs_nonneg (cutoffJet [] w θ)).trans (hcut [] (by simp))
  have hzero : JetBound (fun _ : MixedActiveSpace N => (0:ℂ)) 0 (order+1) A :=
    (JetBound.const 0 0 (order+1)).mono le_rfl (by simpa using zero_le_one.trans hA)
  have hbudget := mixedDensityJetTerms_jet_budget (mixedActiveParameterDirection N) 0 0
    (mixedActiveParameterDirection_norm N) (by simp) (by simp)
    (fun _ => 0) (fun _ => 0) F (onsiteActiveVelocity J s φ) 0 order k hk A D hA
    hzero hzero hV hF
  have hb := norm_list_sum_le_length_mul
    (L.map (fun T => T.onsiteValue J f r τ lam s φ w s θ)) (B*P*M) (by
      intro a ha
      obtain ⟨T,hT,rfl⟩ := List.mem_map.mp ha
      have hreg : ‖T.regularPart 0‖≤M := by
        simpa only [norm_iteratedFDeriv_zero] using (hbudget T hT).bound 0 (Nat.zero_le _)
      have hc := hcut T.cutoff (mixedDensityJetTerms_cutoff_length _ _ _
        (fun _ => 0) (fun _ => 0) F (onsiteActiveVelocity J s φ) k T hT)
      calc
        ‖T.onsiteValue J f r τ lam s φ w s θ‖=
            |cutoffJet T.cutoff w θ| *(P*‖T.regularPart 0‖) := by
          simp only [MixedDensityJetTerm.onsiteValue,onsiteRegularModel,φ,P,
            onsiteDisplacement_base,norm_mul,Complex.norm_real,Real.norm_eq_abs]
        _ ≤ B*(P*M) := mul_le_mul hc (mul_le_mul_of_nonneg_left hreg hP)
          (mul_nonneg hP (norm_nonneg _)) hB
        _ = B*P*M := by ring)
  have hlen : L.length=(N+1)^k := mixedDensityJetTerms_length _ _ _
    (fun _ => 0) (fun _ => 0) F (onsiteActiveVelocity J s φ) k
  rw [List.length_map,hlen,Nat.cast_pow] at hb
  exact hb

/-- Apply the literal all-order expansion, rather than a formal density
model assumed to match the physical source. -/
theorem onsite_actual_density_bound {n : ℕ}
    (J : Finset (Fin (n+1))) (q : Fin (n+1)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ) (hf : RegularSelector f)
    (hΩ : (s,θ)∈onsiteLieDomain J f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hp : ∀ i∈J,f.p =ᶠ[𝓝 (θ i)] fun _ => f.p (θ i))
    (hm : ∀ i∈J,f.m =ᶠ[𝓝 (θ i)] fun _ => f.m (θ i))
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (order k : ℕ) (hk : k≤order) (A B D : ℝ) (hA : 1≤A)
    (hV : ∀ i,JetBound (onsiteActiveVelocity J s
      (fun i => mixedContourPhase f r τ lam s θ i) i) 0 order A)
    (hF : JetBound (onsiteActiveRegularAmplitude J q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0 order D)
    (hcut : ∀ l : List (Fin (n+1)),l.length≤k → |cutoffJet l w θ|≤B) :
    ‖((lieStep (onsiteBranchField J f r τ lam))^[k]
      (fun t a => (w a:ℂ)*onsitePulledDensity f r τ lam t a)) s θ‖≤
      ((n+1+1:ℕ):ℝ)^k*(B*‖mixedHybridVolume J f r τ lam s θ‖*
        ((1+4*2^order*A)^k*(2^order*‖mixedDensityNormalization f τ lam θ‖*D))) := by
  rw [onsite_actual_density_all_order J q f hr τ lam s θ hf.p_smooth hf.m_smooth hΩ
    hbranch hp hm (fun i => (hV i).analytic) hF.analytic w hw k]
  exact onsiteJetTerms_pointwise_budget J f r τ lam s θ w _ order k hk A B _ hA hV
    ((JetBound.const _ 0 order).mul hF) hcut

/-- The onsite recurrence retains the complete Gaussian suppression. -/
theorem onsite_actual_density_gaussian_bound {n : ℕ}
    (J : Finset (Fin (n+1))) (q : Fin (n+1)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ) (hf : RegularSelector f)
    (hΩ : (s,θ)∈onsiteLieDomain J f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hp : ∀ i∈J,f.p =ᶠ[𝓝 (θ i)] fun _ => f.p (θ i))
    (hm : ∀ i∈J,f.m =ᶠ[𝓝 (θ i)] fun _ => f.m (θ i))
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (order k : ℕ) (hk : k≤order) (A B H D κ : ℝ) (hA : 1≤A)
    (hB : 0≤B) (hH : 0≤H) (hD : 0≤D)
    (hV : ∀ i,JetBound (onsiteActiveVelocity J s
      (fun i => mixedContourPhase f r τ lam s θ i) i) 0 order A)
    (hF : JetBound (onsiteActiveRegularAmplitude J q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0 order
      (D^(n+1)*((n+1:ℕ):ℝ)^(3*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)))
    (hnorm : ‖mixedDensityNormalization f τ lam θ‖≤H^(n+1))
    (hcut : ∀ l : List (Fin (n+1)),l.length≤k → |cutoffJet l w θ|≤B^(n+1)) :
    ‖((lieStep (onsiteBranchField J f r τ lam))^[k]
      (fun t a => (w a:ℂ)*onsitePulledDensity f r τ lam t a)) s θ‖≤
      ((2*(1+4*2^order*A))^order*B*(2^order*H)*D)^(n+1)*
        ((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
        ‖mixedHybridVolume J f r τ lam s θ‖ := by
  have hn : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast (show 1≤n+1 by omega)
  have hA0 : 0≤A := zero_le_one.trans hA
  have hAA : A≤((n+1:ℕ):ℝ)*A := by nlinarith
  have hNA : 1≤((n+1:ℕ):ℝ)*A := hA.trans hAA
  have hh := onsite_actual_density_bound J q f hr τ lam s θ hf hΩ hbranch hp hm w hw
    order k hk _ _ _ hNA (fun i => (hV i).mono le_rfl hAA) hF hcut
  have hPow : (2:ℝ)^order≤(2^order)^(n+1) := by
    simpa only [pow_one] using pow_le_pow_right₀
      (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) (show 1≤n+1 by omega)
  have hNorm : (2:ℝ)^order*‖mixedDensityNormalization f τ lam θ‖≤(2^order*H)^(n+1) := by
    rw [mul_pow]
    exact mul_le_mul hPow hnorm (norm_nonneg _) (by positivity)
  apply hh.trans
  calc
    _ = ((n+1+1:ℕ):ℝ)^k*(B^(n+1)*(2^order*‖mixedDensityNormalization f τ lam θ‖)*
      ‖mixedHybridVolume J f r τ lam s θ‖*
      ((1+4*2^order*(((n+1:ℕ):ℝ)*A))^k*
      (D^(n+1)*((n+1:ℕ):ℝ)^(3*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)))) := by ring
    _ ≤ ((n+1+1:ℕ):ℝ)^k*(B^(n+1)*(2^order*H)^(n+1)*
      ‖mixedHybridVolume J f r τ lam s θ‖*
      ((1+4*2^order*(((n+1:ℕ):ℝ)*A))^k*
      (D^(n+1)*((n+1:ℕ):ℝ)^(3*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)))) := by
        gcongr
    _ ≤ _ := mixed_density_budget_gaussian (by omega) hk hA hB (by positivity) hD
      (norm_nonneg _) (Real.exp_pos _).le

end
end IsingBulk.HT.Lie
