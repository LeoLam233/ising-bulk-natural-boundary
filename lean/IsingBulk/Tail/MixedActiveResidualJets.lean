import IsingBulk.Tail.MixedRotatingCoefficientJets
import IsingBulk.Analysis.JetsNormBounds

/-! The active residual chart retains every spectator's temperature dependence.
Only its compact anchor angle moves; branch phases are independent chart coordinates. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped BigOperators Topology ContDiff

abbrev MixedActiveSpace (N : ℕ) := ℂ × ((Fin N → ℂ) × ℂ)

def mixedActiveBranchCoordinate {N : ℕ} (i : Fin N) : MixedActiveSpace N →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ((Fin N → ℂ) × ℂ)).prod
    ((ContinuousLinearMap.proj (R := ℂ) i).comp
      ((ContinuousLinearMap.fst ℂ (Fin N → ℂ) ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ ((Fin N → ℂ) × ℂ))))

def mixedActiveCompactCoordinate (N : ℕ) : MixedActiveSpace N →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ((Fin N → ℂ) × ℂ)).prod
    ((ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ ((Fin N → ℂ) × ℂ)))

theorem mixedActiveBranchCoordinate_norm {N : ℕ} (i : Fin N) : ‖mixedActiveBranchCoordinate i‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖(u.1,u.2.1 i)‖≤1*‖u‖
  simp only [one_mul,Prod.norm_def]
  exact max_le (le_max_left _ _) ((norm_le_pi_norm u.2.1 i).trans
    ((le_max_left _ _).trans (le_max_right _ _)))

theorem mixedActiveCompactCoordinate_norm (N : ℕ) : ‖mixedActiveCompactCoordinate N‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖(u.1,u.2.2)‖≤1*‖u‖
  simp only [one_mul,Prod.norm_def]
  exact max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))

def mixedActiveBranch (F : ℂ → ℂ → ℂ) {N : ℕ} (s : ℂ) (φ : Fin N → ℂ)
    (i : Fin N) (u : MixedActiveSpace N) : ℂ := F (s+u.1) (φ i+u.2.1 i)

def mixedActiveCompact (F : ℂ → ℂ → ℂ) {N : ℕ} (s : ℂ) (y : Fin N → ℂ)
    (q i : Fin N) (u : MixedActiveSpace N) : ℂ :=
  rotatingCompactCoefficient F s (y i) (decide (i=q)) (mixedActiveCompactCoordinate N u)

def mixedActiveResidualData {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (u : MixedActiveSpace N) : MixedResidualData :=
  (mixedActiveBranch mixedInverseSlope s φ j u,
   mixedActiveCompact mixedRootSlope s y q q u,
   (∑ i∈J,mixedActiveBranch regularA s φ i u)/(N:ℂ),
   (∑ i∈Finset.univ.filter (fun i => i∉J),mixedActiveCompact mixedRootTau s y q i u)/(N:ℂ))

theorem normalized_analytic_subset_sum_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} (hN : 0<N) (J : Finset (Fin N)) (f : Fin N → E → ℂ) (x : E)
    (k : ℕ) {B : ℝ} (hB : 0≤B)
    (hf : ∀ i∈J,AnalyticAt ℂ (f i) x)
    (hb : ∀ i∈J,‖iteratedFDeriv ℂ k (f i) x‖≤B) :
    ‖iteratedFDeriv ℂ k (fun u => (∑ i∈J,f i u)/(N:ℂ)) x‖≤B := by
  have he : (fun u => (∑ i∈J,f i u)/(N:ℂ))=(fun u => (N:ℂ)⁻¹ • (∑ i∈J,f i u)) := by
    funext u
    simp [div_eq_mul_inv,mul_comm]
  have hsum : AnalyticAt ℂ (fun u => ∑ i∈J,f i u) x := Finset.analyticAt_fun_sum _ hf
  rw [he,iteratedFDeriv_const_smul_apply' hsum.contDiffAt,
    iteratedFDeriv_fun_sum_apply (fun i hi => (hf i hi).contDiffAt),norm_smul]
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hc : (J.card:ℝ)≤N := by exact_mod_cast (show J.card≤N by simpa using Finset.card_le_card J.subset_univ)
  have hh : ‖∑ i∈J,iteratedFDeriv ℂ k (f i) x‖≤(N:ℝ)*B :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum hb).trans (by simpa using mul_le_mul_of_nonneg_right hc hB))
  simp only [norm_inv,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hn.le)).trans_eq (by field_simp)


theorem mixedActiveBranch_jet_bound (F : ℂ → ℂ → ℂ) {N : ℕ} (s : ℂ) (φ : Fin N → ℂ)
    (i : Fin N) (k : ℕ)
    (hF : AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2) (s,φ i)) :
    AnalyticAt ℂ (mixedActiveBranch F s φ i) 0 ∧
      ‖iteratedFDeriv ℂ k (mixedActiveBranch F s φ i) 0‖≤
        ‖iteratedFDeriv ℂ k (fun p : ℂ × ℂ => F p.1 p.2) (s,φ i)‖ := by
  have he : mixedActiveBranch F s φ i=(fun u =>
      (fun p : ℂ × ℂ => F p.1 p.2) (mixedActiveBranchCoordinate i u+(s,φ i))) := by
    funext u
    simp [mixedActiveBranch,mixedActiveBranchCoordinate,add_comm]
  have hF' : AnalyticAt ℂ (fun p : ℂ × ℂ => F p.1 p.2)
      (mixedActiveBranchCoordinate i 0+(s,φ i)) := by simpa using hF
  rw [he]
  refine ⟨hF'.comp (f := fun u => mixedActiveBranchCoordinate i u+(s,φ i))
    (((mixedActiveBranchCoordinate i).analyticAt 0).add analyticAt_const),?_⟩
  simpa using analytic_affine_pullback_jet_norm (mixedActiveBranchCoordinate i)
    (fun p : ℂ × ℂ => F p.1 p.2) (s,φ i) 0 hF' (mixedActiveBranchCoordinate_norm i) k

theorem mixedActiveCompact_jet_bound (F : ℂ → ℂ → ℂ) {N : ℕ} (s : ℂ) (y : Fin N → ℂ)
    (q i : Fin N) (k : ℕ)
    (hF : AnalyticAt ℂ (rotatingCompactCoefficient F s (y i) (decide (i=q))) 0) :
    AnalyticAt ℂ (mixedActiveCompact F s y q i) 0 ∧
      ‖iteratedFDeriv ℂ k (mixedActiveCompact F s y q i) 0‖≤
        ‖iteratedFDeriv ℂ k (rotatingCompactCoefficient F s (y i) (decide (i=q))) 0‖ := by
  have hF' : AnalyticAt ℂ (rotatingCompactCoefficient F s (y i) (decide (i=q)))
      (mixedActiveCompactCoordinate N 0) := by simpa using hF
  refine ⟨hF'.comp (f := mixedActiveCompactCoordinate N) ((mixedActiveCompactCoordinate N).analyticAt 0),?_⟩
  exact (analytic_linear_comp_jet_bound _ (mixedActiveCompactCoordinate N) 0 k hF'
    (mixedActiveCompactCoordinate_norm N)).trans_eq (by simp)


/-- The neighborhood and constant precede the number of spectators. The normalized
sums retain every temperature-dependent term and lose no power of N. -/
theorem mixed_active_residual_component_jets (s₀ : ℂ) (c₀ : ℝ) (hs₀ : s₀≠0)
    (hS : s₀+s₀⁻¹=(1+c₀:ℂ)) (hc₀ : |c₀|<1) (order : ℕ) :
    ∃ U : Set (ℂ × ℂ),IsOpen U ∧ (s₀,0)∈U ∧
      ∀ K : Set (ℂ × ℂ),IsCompact K → K⊆mixedRootPairDomain → ∃ C : ℝ,0<C ∧
      ∀ (N : ℕ) (J : Finset (Fin N)) (j q : Fin N) (s : ℂ) (φ y : Fin N → ℂ),
      0<N → j∈J → q∉J → (∀ i∈J,(s,φ i)∈U) → (∀ i∉J,(s,y i)∈K) →
      AnalyticAt ℂ (mixedActiveResidualData J j q s φ y) 0 ∧ ∀ k≤order,
      ‖iteratedFDeriv ℂ k (fun u => (mixedActiveResidualData J j q s φ y u).1) 0‖≤C ∧
      ‖iteratedFDeriv ℂ k (fun u => (mixedActiveResidualData J j q s φ y u).2.1) 0‖≤C ∧
      ‖iteratedFDeriv ℂ k (fun u => (mixedActiveResidualData J j q s φ y u).2.2.1) 0‖≤C ∧
      ‖iteratedFDeriv ℂ k (fun u => (mixedActiveResidualData J j q s φ y u).2.2.2) 0‖≤C := by
  have hβ := mixedInverseSlope_analytic_base s₀ c₀ hs₀ hS hc₀
  have hA := regularA_analytic_base s₀ c₀ hs₀ hS hc₀
  obtain ⟨B,hB,hβb⟩ := finite_analytic_jets_bounded _ _ hβ order
  obtain ⟨A,hApos,hAb⟩ := finite_analytic_jets_bounded _ _ hA order
  obtain ⟨U,hU,hUopen,hUbase⟩ := eventually_nhds_iff.mp
    ((hβ.eventually_analyticAt.and hA.eventually_analyticAt).and (hβb.and hAb))
  refine ⟨U,hUopen,hUbase,?_⟩
  intro K hK hKD
  obtain ⟨D,hD,hDb⟩ := compact_rotating_coefficient_uniform_jets K hK mixedRootSlope
    (fun p hp => (mixedRootCoefficients_analyticAt (hKD hp).1 (hKD hp).2.1 (hKD hp).2.2).1) order
  obtain ⟨T,hT,hTb⟩ := compact_rotating_coefficient_uniform_jets K hK mixedRootTau
    (fun p hp => (mixedRootCoefficients_analyticAt (hKD hp).1 (hKD hp).2.1 (hKD hp).2.2).2) order
  let C := max (max B A) (max D T)
  have hBC : B≤C := (le_max_left B A).trans (le_max_left _ _)
  have hAC : A≤C := (le_max_right B A).trans (le_max_left _ _)
  have hDC : D≤C := (le_max_left D T).trans (le_max_right _ _)
  have hTC : T≤C := (le_max_right D T).trans (le_max_right _ _)
  refine ⟨C,hB.trans_le hBC,?_⟩
  intro N J j q s φ y hN hj hq hφ hy
  have hba := (mixedActiveBranch_jet_bound mixedInverseSlope s φ j 0 (hU _ (hφ j hj)).1.1).1
  have hqa := (mixedActiveCompact_jet_bound mixedRootSlope s y q q 0
    (hDb (s,y q) (hy q hq) (decide (q=q))).1).1
  have hAa : AnalyticAt ℂ (fun u => (∑ i∈J,mixedActiveBranch regularA s φ i u)/(N:ℂ)) 0 :=
    (Finset.analyticAt_fun_sum J (fun i hi =>
      (mixedActiveBranch_jet_bound regularA s φ i 0 (hU _ (hφ i hi)).1.2).1)).div_const
  have hDa : AnalyticAt ℂ (fun u =>
      (∑ i∈Finset.univ.filter (fun i => i∉J),mixedActiveCompact mixedRootTau s y q i u)/(N:ℂ)) 0 :=
    (Finset.analyticAt_fun_sum _ (fun i hi =>
      (mixedActiveCompact_jet_bound mixedRootTau s y q i 0
        (hTb (s,y i) (hy i (Finset.mem_filter.mp hi).2) (decide (i=q))).1).1)).div_const
  refine ⟨hba.prod (hqa.prod (hAa.prod hDa)),?_⟩
  intro k hk
  have hb := mixedActiveBranch_jet_bound mixedInverseSlope s φ j k (hU _ (hφ j hj)).1.1
  have hd := hDb (s,y q) (hy q hq) true
  have hqdec : decide (q=q)=true := by simp
  have hd' : AnalyticAt ℂ (rotatingCompactCoefficient mixedRootSlope s (y q) (decide (q=q))) 0 := by
    simpa only [hqdec,decide_true] using hd.1
  refine ⟨hb.2.trans ((hU _ (hφ j hj)).2.1 k hk |>.trans hBC),
    (mixedActiveCompact_jet_bound mixedRootSlope s y q q k hd').2.trans
      (by simpa only [hqdec,decide_true] using (hd.2 k hk).trans hDC),?_,?_⟩
  · apply (normalized_analytic_subset_sum_jet hN J (mixedActiveBranch regularA s φ) 0 k hApos.le
      (fun i hi => (mixedActiveBranch_jet_bound regularA s φ i k (hU _ (hφ i hi)).1.2).1)
      (fun i hi => (mixedActiveBranch_jet_bound regularA s φ i k (hU _ (hφ i hi)).1.2).2.trans
        ((hU _ (hφ i hi)).2.2 k hk))).trans hAC
  · apply (normalized_analytic_subset_sum_jet hN (Finset.univ.filter (fun i => i∉J))
      (mixedActiveCompact mixedRootTau s y q) 0 k hT.le ?_ ?_).trans hTC
    · intro i hi
      exact (mixedActiveCompact_jet_bound mixedRootTau s y q i k
        (hTb (s,y i) (hy i (Finset.mem_filter.mp hi).2) (decide (i=q))).1).1
    · intro i hi
      have ht := hTb (s,y i) (hy i (Finset.mem_filter.mp hi).2) (decide (i=q))
      exact (mixedActiveCompact_jet_bound mixedRootTau s y q i k ht.1).2.trans (ht.2 k hk)


theorem analytic_four_components_jet_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → MixedResidualData) (x : E) (hF : AnalyticAt ℂ F x) (k : ℕ) {C : ℝ}
    (h₁ : ‖iteratedFDeriv ℂ k (fun u => (F u).1) x‖≤C)
    (h₂ : ‖iteratedFDeriv ℂ k (fun u => (F u).2.1) x‖≤C)
    (h₃ : ‖iteratedFDeriv ℂ k (fun u => (F u).2.2.1) x‖≤C)
    (h₄ : ‖iteratedFDeriv ℂ k (fun u => (F u).2.2.2) x‖≤C) :
    ‖iteratedFDeriv ℂ k F x‖≤C := by
  have he : F=(fun u => ((F u).1,((F u).2.1,((F u).2.2.1,(F u).2.2.2)))) := rfl
  rw [he,iteratedFDeriv_prodMk (n := ω) hF.contDiffAt.fst hF.contDiffAt.snd (by simp),
    iteratedFDeriv_prodMk (n := ω) hF.contDiffAt.snd.fst hF.contDiffAt.snd.snd (by simp),
    iteratedFDeriv_prodMk (n := ω) hF.contDiffAt.snd.snd.fst hF.contDiffAt.snd.snd.snd (by simp)]
  simp only [ContinuousMultilinearMap.opNorm_prod]
  exact max_le h₁ (max_le h₂ (max_le h₃ h₄))

end
end IsingBulk.Tail
