import IsingBulk.HT.Lie.OriginalFluxData
import IsingBulk.HT.Lie.SignedKernelDensity
import IsingBulk.HT.Lie.ShapeFlux

/-! Literal geometric flux of the actual signed source descendants with the
manuscript rational selected-pair weight. All pointwise coefficient,
numerator and selected-pole estimates are instantiated on the physical chart. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail
open Set Filter MeasureTheory
open scoped BigOperators Topology
set_option maxHeartbeats 1200000

def signedOriginalFlux {n : ℕ} (σ : ℂ) (d : LocalBranchData) (ε : ℝ)
    (M j : ℕ) (p q : Fin (n+1)) (u : AngularSpace n) (i : Fin (n+1)) : ℂ :=
  actualField (-d.c₀*ε) d.thetaB p q (radialParameter d.theta ε) u i*
    signedSourceTermSum σ p q (-d.c₀*ε) d.thetaB (allBranchExteriorPairWeight M p q)
      (unfactoredNumerator (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2))
      j (radialParameter d.theta ε) u

def originalFluxCost (j N G C : ℕ) (E c A H : ℝ) : ℝ :=
  (3+3*N:ℝ)^j*((G:ℝ)*(N:ℝ)^G*(max 1 c⁻¹)^(2*j+1))*
    (3*E^2*N*((C:ℝ)*(N:ℝ)^C))*allBranchExteriorNearNumeratorCost A j N*H^(N*(N-1))

/-- The selected zero persists through all generated source terms. -/
theorem signedOriginalFlux_zero_selected {n M j : ℕ} (σ : ℂ) (d : LocalBranchData)
    (ε : ℝ) (p q : Fin (n+1)) (u : AngularSpace n) (i : Fin (n+1))
    (hM : 2*j+2 < M) (hd : 0 < allBranchExteriorDiameter u) (he : u p=u q) :
    signedOriginalFlux σ d ε M j p q u i=0 := by
  obtain ⟨C,hC,hjets⟩ := rational_weight_jets M j hM
  have hzero : signedSourceTermSum σ p q (-d.c₀*ε) d.thetaB
      (allBranchExteriorPairWeight M p q)
      (unfactoredNumerator (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2))
      j (radialParameter d.theta ε) u=0 := by
    unfold signedSourceTermSum
    apply List.sum_eq_zero
    intro a ha
    obtain ⟨T,hT,rfl⟩ := List.mem_map.mp ha
    have hv := sourceJetTerms_valid p q j T hT
    have hb := hjets (n+1) (by omega) p q u hd T.cutoff (by omega)
    have hcut : cutoffJet T.cutoff (allBranchExteriorPairWeight M p q) u=0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [he,sub_self,abs_zero,zero_pow (by omega : 2*M-T.cutoff.length ≠ 0),
        mul_zero,zero_div] using hb
    simp [signedSourceValue,hcut]
  rw [signedOriginalFlux,hzero,mul_zero]

/-- Full actual field-source flux bound. Its loss is exactly 2j+1 and
its remaining kernel is the literal signed physical kernel density. -/
theorem signed_original_flux_bound {d : LocalBranchData} (B : BranchEstimates d)
    (M j : ℕ) (hM : 2*j+2 < M) :
    ∃ G C : ℕ, 0 < G ∧ 0 < C ∧ ∃ E c A r : ℝ,
      1 ≤ E ∧ 0 < c ∧ 0 < A ∧ 0 < r ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ σ : ℂ, ∀ n : ℕ,
      2*j+1 ≤ (n+1)*n → ∀ p q : Fin (n+1), p ≠ q →
      ∀ u : AngularSpace n, (∀ i, |u i| ≤ r) →
      0 < allBranchExteriorDiameter u → allBranchExteriorDiameter u ≤ 1 →
      ∀ H : ℝ, 1 ≤ H → B.magnitudeUpper/Real.sqrt ε ≤ H →
      H*allBranchExteriorDiameter u ≤ 1 → ∀ i,
      ‖signedOriginalFlux σ d ε M j p q u i‖ ≤
        originalFluxCost j (n+1) G C E c A H*
          allBranchExteriorDiameter u^((n+1)*n-(2*j+1))*signedExteriorKernelDensity σ d ε u := by
  obtain ⟨G,hG,c,rG,hc,hrG,hguard⟩ := rational_weight_absorbs_flux_terms d M j hM
  obtain ⟨C,hC,rC,hrC,hcoeff⟩ := allBranchExterior_original_coefficients d j 0
  obtain ⟨E,rE,hE,hrE,hscalar⟩ := original_scalar_bounds d 0
  obtain ⟨A,rA,hA,hrA,hnum⟩ := fixed_epsilon_numerator_power B j
  obtain ⟨rP,hrP,hpoint⟩ := allBranchExterior_original_actual_chart d
  let r := min rG (min rC (min rE (min rA rP)))
  have hr : 0 < r := lt_min hrG (lt_min hrC (lt_min hrE (lt_min hrA hrP)))
  have hs : r ≤ rG ∧ r ≤ rC ∧ r ≤ rE ∧ r ≤ rA ∧ r ≤ rP := by
    exact ⟨min_le_left _ _,(min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
      (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))⟩
  refine ⟨G,C,hG,hC,E,c,A,r,hE,hc,hA,hr,?_⟩
  intro ε hε hεr σ n hP p q hpq u hu hd hd1 H hH hHmag hHD i
  let W₀ := (G:ℝ)*(n+1:ℝ)^G*(max 1 c⁻¹)^(2*j+1)
  let C₀ := 3*E^2*(n+1:ℝ)*((C:ℝ)*(n+1:ℝ)^C)
  let A₀ := allBranchExteriorNearNumeratorCost A j (n+1)
  have hW₀ : 0 ≤ W₀ := by dsimp [W₀]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀,allBranchExteriorNearNumeratorCost]; positivity
  by_cases hupq : u p=u q
  · rw [signedOriginalFlux_zero_selected σ d ε p q u i hM hd hupq,norm_zero]
    have hk := signed_kernel_density_nonneg σ d ε u
    unfold originalFluxCost
    positivity
  have hp := hpoint ε hε (hεr.trans hs.2.2.2.2) n p q u
    (fun l => (hu l).trans hs.2.2.2.2) hupq
  have hmicro : MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u :=
    ⟨hp.s_ne,hp.re_pos,hp.im_pos,hp.g_pos,hp.sin_ne,hp.slit⟩
  have hterms (T : SourceJetTerm (n+1)) (hT : T∈sourceJetTerms p q j) :
      ‖actualField (-d.c₀*ε) d.thetaB p q (radialParameter d.theta ε) u i*
        signedSourceValue σ T p q (-d.c₀*ε) d.thetaB (allBranchExteriorPairWeight M p q)
          (unfactoredNumerator (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2))
          (radialParameter d.theta ε) u‖ ≤
        (W₀*C₀*A₀*H^((n+1)*n))*allBranchExteriorDiameter u^((n+1)*n-(2*j+1))*
          signedExteriorKernelDensity σ d ε u := by
    have ht := sourceJetTerms_valid p q j T hT
    have hw := hguard ε hε (hεr.trans hs.1) (n+1) (by omega) p q u
      (fun l => (hu l).trans hs.1) hupq j le_rfl T hT
    have hpow : (c⁻¹)^(T.pole+1) ≤ (max 1 c⁻¹)^(2*j+1) :=
      (pow_le_pow_left₀ (inv_nonneg.mpr hc.le) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    have hwT : ‖cutoffJet T.cutoff (allBranchExteriorPairWeight M p q) u‖/
        ‖selectedDifferenceCLM p q (radialParameter d.theta ε,
          chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖^(T.pole+1) ≤
        W₀/allBranchExteriorDiameter u^(T.pole+1+T.cutoff.length) := by
      change ‖cutoffJet T.cutoff (allBranchExteriorPairWeight M p q) u‖/
        ‖chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u q-
          chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u p‖^(T.pole+1) ≤ _
      rw [original_chartMap_eq,norm_sub_rev]
      apply hw.trans
      simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc,W₀,Nat.cast_add,Nat.cast_one] using
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (G:ℝ)*(n+1:ℝ)^G))
          (pow_nonneg hd.le (T.cutoff.length+T.pole+1))
    have hsc := hscalar ε hε (hεr.trans hs.2.2.1) (n+1) p q u
      (fun l => (hu l).trans hs.2.2.1)
    have hreg := (hcoeff ε hε (hεr.trans hs.2.1) (n+1) (by omega) p q hpq).2 u
      (fun l => (hu l).trans hs.2.1) T hT
    have hregT := (fieldFluxTerm_regular_bound T p q i _ hsc (by omega) hreg).bound 0 le_rfl
    have hnumT := hnum ε hε (hεr.trans hs.2.2.2.1) (n+1) (by omega)
      (by simpa only [Nat.add_sub_cancel] using (show j ≤ (n+1)*n by omega)) u
      (fun l => (hu l).trans hs.2.2.2.1) H hH hHmag hd hHD T.numerator
      (by have hm := mixed_word_degree T.numerator; omega)
    rw [signed_kernel_density_eq_chart σ d ε u hmicro]
    apply signed_flux_term_collision_power σ T p q i hT _ _ _ _ _ u hp hP
      H W₀ C₀ A₀ hH hW₀ hC₀ hA₀ hd hd1 hwT
    · simpa only [original_chartMap_eq,norm_iteratedFDeriv_zero,pow_zero,one_mul,mul_one,
        Nat.cast_add,Nat.cast_one,C₀] using hregT
    · simpa only [original_chartMap_eq,Nat.add_sub_cancel,A₀] using hnumT
  unfold signedOriginalFlux signedSourceTermSum
  rw [← List.sum_map_mul_left]
  have hh := norm_list_sum_le_length_mul
    ((sourceJetTerms p q j).map (fun T => actualField (-d.c₀*ε) d.thetaB p q
      (radialParameter d.theta ε) u i*signedSourceValue σ T p q (-d.c₀*ε) d.thetaB
        (allBranchExteriorPairWeight M p q)
        (unfactoredNumerator (fun z : ℂ × (Fin (n+1) → ℂ) => microRegularAmplitude z.1 z.2))
        (radialParameter d.theta ε) u)) _ (by
      intro x hx
      obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hx
      exact hterms T hT)
  apply hh.trans_eq
  simp only [List.length_map,sourceJetTerms_length,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_one]
  dsimp [originalFluxCost,W₀,C₀,A₀]
  push_cast
  ring

end
end IsingBulk.HT.Lie
