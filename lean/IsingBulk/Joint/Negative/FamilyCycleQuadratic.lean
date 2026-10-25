import IsingBulk.Joint.Negative.FamilyRootBounds
import IsingBulk.Anisotropic.NegativeCycles.ActualPoleComparison

/-! Actual pole quadratic comparison on one compact-family neighborhood. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeCycles
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem compact_family_cycle_quadratic (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hBn : ∀ eta∈Q, B (0,eta)≠0) :
    ∃ r : ℝ, 0<r ∧ ∀ eta∈Q, ∀ n : ℕ, n≠0 → ∀ d t : ℂ, ∀ v : Config n,
      ‖d‖<r → ‖t‖<r → (∀ i, ‖v i‖<r) → ZeroMean v →
      poleEquation (familyMember B eta) phi hphi d t v=0 →
      ‖t-(1-Complex.cos d)-quadratic v/(2*n)‖≤absoluteEnergy v/(64*n) := by
  obtain ⟨r,L,hr,_hL,hs,_hLip⟩ := compact_family_root_small B phi hphi hQ hB hBn (1/256) (by norm_num)
  let U : Set ((ℂ × ℂ) × E) := {q |
    phaseParameterQuotient (familyMember B q.2) phi hphi q.1.2 q.1.1≠0 ∧
    ‖centralHessian (familyMember B q.2) phi q.1.2-1‖<1/256 ∧
    centralHessian (familyMember B q.2) phi q.1.2≠0}
  have hc (eta : E) (heta : eta∈Q) : ((0,0),eta)∈interior U := by
    apply mem_interior_iff_mem_nhds.mpr
    have hqa := family_parameterQuotient_analyticAt B phi hphi eta (hB eta heta)
    have hh : AnalyticAt ℂ (fun q : (ℂ × ℂ) × E => centralHessian (familyMember B q.2) phi q.1.2) ((0,0),eta) :=
      (family_hessian_analyticAt B phi eta (hB eta heta)).comp_of_eq
        (f := fun q : (ℂ × ℂ) × E => (q.1.2,q.2))
        ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd) rfl
    have hq0 : phaseParameterQuotient (familyMember B eta) phi hphi 0 0≠0 := by
      have hc := phaseParameterQuotient_center (familyMember B eta) phi hphi 0
        (by simpa using familyMember_analyticAt (hB eta heta))
      simp only [Complex.cos_zero,sub_self] at hc
      rw [hc]
      exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)) (hBn eta heta)
    exact (hqa.continuousAt.eventually_ne hq0).and
      (((hh.continuousAt.sub continuousAt_const).norm.eventually_lt continuousAt_const
        (by change ‖centralHessian (familyMember B eta) phi 0-1‖<(1/256:ℝ); rw [centralHessian_zero]; norm_num)).and
        (hh.continuousAt.eventually_ne (by change centralHessian (familyMember B eta) phi 0≠0; rw [centralHessian_zero]; exact one_ne_zero)))
  obtain ⟨a,ha,hau⟩ := compact_product_tube hQ isOpen_interior hc
  refine ⟨min r a,lt_min hr ha,?_⟩
  intro eta heta n hn d t v hd ht hv hm hp
  have hu := interior_subset (s := U) (hau eta heta (t,d)
    (max_lt (ht.trans_le (min_le_right _ _)) (hd.trans_le (min_le_right _ _))))
  apply pole_quadratic_comparison_of_scalar_bounds hn (familyMember B eta) phi hphi d t v hm hu.2.2 hu.1 hp hu.2.1.le
  intro i
  exact (hs eta heta (t,(d,v i))
    (max_lt (ht.trans_le (min_le_left _ _)) (max_lt (hd.trans_le (min_le_left _ _))
      ((hv i).trans_le (min_le_left _ _))))).2

theorem compact_family_actualPole_quadratic_comparison (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {Q : Set E} (hQ : IsCompact Q)
    (hB : ∀ eta∈Q, AnalyticAt ℂ B (0,eta)) (hBn : ∀ eta∈Q, B (0,eta)≠0)
    (r C : ℝ) (hr : 0<r) :
    ∃δ : ℝ,0<δ ∧ δ≤r ∧ ∀ eta∈Q, ∀n : ℕ, n≠0 → ∀d : ℂ, ‖d‖<δ →
      ∀P : UniformProjectedWitness (familyMember B eta) phi hphi n d r C,
      ∀v : Config n, ‖v‖<δ → ZeroMean v →
      ‖P.T v-(1-Complex.cos d)-quadratic v/(2*n)‖≤absoluteEnergy v/(64*n) := by
  obtain ⟨a,ha,hcmp⟩ := compact_family_cycle_quadratic B phi hphi hQ hB hBn
  have ht : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
  have he : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<a/2 :=
    ht.norm.eventually_lt continuousAt_const (by simpa using half_pos ha)
  obtain ⟨b,hb,hbs⟩ := Metric.mem_nhds_iff.mp he
  let δ := min r (min (a/4) b)
  have hδ : 0<δ := lt_min hr (lt_min (by positivity) hb)
  have hδr : δ≤r := min_le_left _ _
  have hδa : δ≤a/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hδb : δ≤b := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ,hδ,hδr,?_⟩
  intro eta heta n hn d hd P v hv hm
  have hvR : ‖v‖<2*r := by linarith
  have htau := hbs (show d∈ball (0:ℂ) b by simpa using hd.trans_le hδb)
  change ‖1-Complex.cos d‖<a/2 at htau
  have hl := P.t_lip v 0 hvR (by simpa using mul_pos (by norm_num : (0:ℝ)<2) hr)
  rw [P.t_zero,sub_zero] at hl
  have htA : ‖P.T v‖<a := by
    have hn := norm_add_le (P.T v-(1-Complex.cos d)) (1-Complex.cos d)
    rw [sub_add_cancel] at hn
    linarith
  apply hcmp eta heta n hn d (P.T v) v (by linarith) htA
  · intro i
    exact (norm_le_pi_norm v i).trans_lt (by linarith)
  · exact hm
  · exact (P.t_pole v hvR).1


end
end IsingBulk.Joint.Negative
