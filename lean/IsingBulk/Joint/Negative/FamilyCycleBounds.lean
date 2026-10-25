import IsingBulk.Joint.Negative.FamilyCycleScalar

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeCycles
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_cycle_scalar_bound (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta)) :
    ∃ δ M : ℝ, 0<δ ∧ 1≤M ∧ ∀ eta∈Q, ∀ t a : ℂ, ‖t‖<δ → ‖a‖<δ →
      ‖B (t,eta)‖≤M ∧ ‖rootB (t,eta)‖≤M ∧
      ‖(Complex.sinh (negativePhase (familyMember B eta) phi hphi t a))⁻¹‖≤M := by
  obtain ⟨rb,Mb,hrb,hMb,hb⟩ := compact_analytic_uniform_bound B hQ hB
  obtain ⟨rr,Mr,hrr,hMr,hr⟩ := compact_analytic_uniform_bound rootB hQ hroot
  obtain ⟨ro,Mo,hro,hMo,ho⟩ := compact_analytic_uniform_bound
    (fun q : (ℂ × ℂ) × E => (Complex.sinh (negativePhase (familyMember B q.2) phi hphi q.1.1 q.1.2))⁻¹)
    hQ (fun eta heta => family_cycle_oneBody_analyticAt B phi hphi (hB eta heta))
  refine ⟨min rb (min rr ro),1+Mb+Mr+Mo,lt_min hrb (lt_min hrr hro),by linarith,?_⟩
  intro eta heta t a ht ha
  have hbb := (hb eta heta t (ht.trans_le (min_le_left _ _))).2
  have hrr' := (hr eta heta t (ht.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).2
  have hoo := (ho eta heta (t,a) ((max_lt ht ha).trans_le ((min_le_right _ _).trans (min_le_right _ _)))).2
  exact ⟨by linarith,by linarith,by linarith⟩

theorem compact_family_cycle_pair_contraction (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) :
    ∃ δ : ℝ, 0<δ ∧ ∀ eta∈Q, ∀ t a b : ℂ, ‖t‖<δ → ‖a‖<δ → ‖b‖<δ →
      ‖localCompletePair (familyMember B eta) phi hphi t a b‖≤(1/2:ℝ) := by
  let U : Set ((ℂ × ℂ × ℂ) × E) := {q |
    ‖localCompletePair (familyMember B q.2) phi hphi q.1.1 q.1.2.1 q.1.2.2‖<(1/2:ℝ)}
  have hc (eta : E) (heta : eta∈Q) : (0,eta)∈interior U := by
    apply mem_interior_iff_mem_nhds.mpr
    exact (family_cycle_pair_analyticAt B phi hphi (hB eta heta)).continuousAt.norm.eventually_lt_const
      (by simp only [Prod.fst_zero,Prod.snd_zero,localCompletePair_center,norm_zero]; norm_num)
  obtain ⟨δ,hδ,hu⟩ := compact_product_tube hQ isOpen_interior hc
  refine ⟨δ,hδ,?_⟩
  intro eta heta t a b ht ha hb
  exact (interior_subset (s := U) (hu eta heta (t,a,b) (max_lt ht (max_lt ha hb)))).le

theorem compact_family_cycle_numerator_gaussian (B rootB : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hroot : ∀ eta∈Q, AnalyticAt ℂ rootB (0,eta)) :
    ∃ δ M : ℝ,0<δ ∧ 1≤M ∧ ∀ eta∈Q, ∀m : ℕ, ∀d t : ℂ, ∀v : Config (2*m+1),
      ‖d‖<δ → ‖t‖<δ → (∀i, ‖v i‖<δ) →
      ‖formFactorNumerator (familyMember B eta) (familyMember rootB eta) phi hphi d t v‖≤
        (M*M^m)*M^(2*m+1)*(1/2:ℝ)^((2*m+1).choose 2) := by
  obtain ⟨δ₁,M,hδ₁,hM,hscalar⟩ := compact_family_cycle_scalar_bound B rootB phi hphi hQ hB hroot
  obtain ⟨δ₂,hδ₂,hpair⟩ := compact_family_cycle_pair_contraction B phi hphi hQ hB
  let δ := min δ₁ δ₂ / 2
  have hδ : 0<δ := div_pos (lt_min hδ₁ hδ₂) (by norm_num)
  have hδ1 : 2*δ≤δ₁ := by dsimp [δ]; linarith [min_le_left δ₁ δ₂]
  have hδ2 : 2*δ≤δ₂ := by dsimp [δ]; linarith [min_le_right δ₁ δ₂]
  refine ⟨δ,M,hδ,hM,?_⟩
  intro eta heta m d t v hd ht hv
  have ht1 : ‖t‖<δ₁ := by linarith
  have ht2 : ‖t‖<δ₂ := by linarith
  have ha (i) : ‖d+v i‖<2*δ := (norm_add_le d (v i)).trans_lt (by linarith [hv i])
  have hs := hscalar eta heta t 0 ht1 (by simpa using hδ₁)
  exact formFactorNumerator_odd_norm_bound m (familyMember B eta) (familyMember rootB eta) phi hphi d t v hM hs.1 hs.2.1
    (fun i => (hscalar eta heta t (d+v i) ht1 ((ha i).trans_le hδ1)).2.2)
    (fun i j => hpair eta heta t (d+v i) (d+v j) ht2 ((ha i).trans_le hδ2) ((ha j).trans_le hδ2))


end
end IsingBulk.Joint.Negative
