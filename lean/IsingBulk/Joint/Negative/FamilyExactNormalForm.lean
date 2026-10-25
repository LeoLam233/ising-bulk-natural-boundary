import IsingBulk.Joint.Negative.FamilyCorrectionInverse
import IsingBulk.Anisotropic.NegativeNormalForm.UniformExactNormalForm
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology BigOperators
set_option maxHeartbeats 2000000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem compact_family_exact_normal_form (B : ℂ × E→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀eta∈K,AnalyticAt ℂ B (0,eta)) (hB0 : ∀eta∈K,B (0,eta)≠0) :
    ∃ δ R r C : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<C ∧ δ≤R/2 ∧ 4*R≤r ∧
      ∀eta∈K,∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ P : UniformProjectedWitness (familyMember B eta) phi hphi n d r C,
      ∃ J : UniformCorrectionWitness (familyMember B eta) phi hphi n d r C P R,
        AnalyticOnNhd ℂ (fun y => P.V (J.W y)) (ball 0 δ) ∧ P.V (J.W 0)=0 ∧
        HasFDerivAt (fun y => P.V (J.W y)) (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
        (∀ e y, P.V (J.W (permute e y))=permute e (P.V (J.W y))) ∧
        (∀ y, ‖y‖≤δ → ‖P.V (J.W y)‖≤4*‖y‖ ∧ ‖P.V (J.W y)-y‖≤(3/32)*‖y‖ ∧
          (ZeroMean y → ZeroMean (P.V (J.W y)) ∧
            P.T (P.V (J.W y))=1-Complex.cos d+centralHessian (familyMember B eta) phi d/(2*n)*quadratic y)) := by
  obtain ⟨R,r,C,hR,hr,hC,hRr,hex⟩ := compact_family_correction_witness B phi hphi hK hB hB0
  let G : Set ((ℂ × ℂ) × E) := {q | phaseParameterQuotient (familyMember B q.2) phi hphi q.1.2 q.1.1≠0}
  have hcenter (eta : E) (heta : eta∈K) : ((0,0),eta)∈interior G := by
    apply mem_interior_iff_mem_nhds.mpr
    have hq0 : phaseParameterQuotient (familyMember B eta) phi hphi 0 0≠0 := by
      have hh := phaseParameterQuotient_center (familyMember B eta) phi hphi 0
        (by simpa using familyMember_analyticAt (hB eta heta))
      simp only [Complex.cos_zero,sub_self] at hh
      rw [hh]
      exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)) (hB0 eta heta)
    exact (family_parameterQuotient_analyticAt B phi hphi eta (hB eta heta)).continuousAt.eventually_ne hq0
  obtain ⟨a,ha,hqn0⟩ := compact_product_tube (X:=ℂ × ℂ) hK (isOpen_interior : IsOpen (interior G)) hcenter
  have hqn (eta : E) (heta : eta∈K) (q : ℂ × ℂ) (hq : ‖q‖<a) :
      phaseParameterQuotient (familyMember B eta) phi hphi q.2 q.1≠0 :=
    by
      have hmem : (q,eta)∈interior G := hqn0 eta heta q hq
      have hmemG : (q,eta)∈G := interior_subset hmem
      exact hmemG
  obtain ⟨b0,hb0,hbranch⟩ := compact_family_branch B phi hK hB hB0
  have htau : Tendsto (fun d : ℂ=>1-Complex.cos d) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d : ℂ=>1-Complex.cos d) 0 := by fun_prop
    simpa using hh.tendsto
  obtain ⟨b1,hb1,htau1⟩ := Metric.mem_nhds_iff.mp
    (htau.eventually (Metric.ball_mem_nhds (0:ℂ) (by positivity : 0<a/2)))
  let b := min b0 b1
  have hb : 0<b := lt_min hb0 hb1
  have hbs (eta : E) (heta : eta∈K) (d : ℂ) (hd : ‖d‖<b) :
      ‖1-Complex.cos d‖<a/2 ∧ centralHessian (familyMember B eta) phi d≠0 :=
    ⟨by simpa using htau1 (show d∈ball (0:ℂ) b1 by simpa using hd.trans_le (min_le_right _ _)),
      (hbranch eta heta d (hd.trans_le (min_le_left _ _))).2.2⟩
  let δ := min R (min a b)/16
  have hδ : 0<δ := div_pos (lt_min hR (lt_min ha hb)) (by norm_num)
  have hδR : 16*δ≤R := by dsimp [δ]; linarith [min_le_left R (min a b)]
  have hδa : 16*δ≤a := by
    have hh := (min_le_right R (min a b)).trans (min_le_left a b)
    dsimp [δ]; linarith
  have hδb : δ≤b := by
    have hh := (min_le_right R (min a b)).trans (min_le_right a b)
    dsimp [δ]; linarith
  refine ⟨δ,R,r,C,hδ,hR,hr,hC,by linarith,hRr,?_⟩
  intro eta heta n hn d hd
  obtain ⟨P,⟨J⟩⟩ := hex eta heta n hn d (by linarith)
  have hbd := hbs eta heta d (hd.trans_le hδb)
  obtain ⟨hFa,hFs⟩ := J.corrected_bounds (familyMember B eta) phi hphi d r C R P hr hR (by linarith)
  have hD : HasFDerivAt P.V (ContinuousLinearMap.id ℂ (Config n)) (J.W 0) := by rw [J.w_zero]; exact P.v_deriv
  refine ⟨P,J,hFa.mono (ball_subset_ball (by linarith)),by rw [J.w_zero,P.v_zero],?_,?_,?_⟩
  · simpa using hD.comp 0 J.w_deriv
  · intro e y
    rw [J.w_perm,P.v_perm]
  · intro y hy
    have hys : ‖y‖≤R/2 := by linarith
    have hf := hFs y hys
    refine ⟨hf.1,hf.2,?_⟩
    intro hm
    have hvsource : ‖P.V (J.W y)‖<2*r := by linarith [hf.1]
    have hT := P.t_lip (P.V (J.W y)) 0 hvsource (by simpa using (show 0<2*r by positivity))
    rw [P.t_zero,sub_zero] at hT
    have ht : ‖P.T (P.V (J.W y))‖<a := by
      have ht' := norm_le_norm_sub_add (P.T (P.V (J.W y))) (1-Complex.cos d)
      linarith [hbd.1,hf.1]
    have hq := hqn eta heta (P.T (P.V (J.W y)),d) (max_lt ht (by linarith : ‖d‖<a))
    exact J.exact_energy hn (familyMember B eta) phi hphi d r C R P hr (by linarith) y hys hm hbd.2 hq

end
end IsingBulk.Joint.Negative
