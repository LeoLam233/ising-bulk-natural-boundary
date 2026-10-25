import IsingBulk.Joint.Negative.FamilyDensityScalar
import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueSlopeUniform

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Metric Filter IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

theorem family_residueSlopeRatio_analyticAt (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (eta : E) (hB : AnalyticAt ℂ B (0,eta))
    (hBn : B (0,eta)≠0) :
    AnalyticAt ℂ (fun q : ScalarTriple × E =>
      residueSlopeRatio (familyMember B q.2) phi hphi q.1) (0,eta) := by
  have ht : AnalyticAt ℂ (fun q : ScalarTriple × E => q.1.1) (0,eta) :=
    analyticAt_fst.comp analyticAt_fst
  have hd : AnalyticAt ℂ (fun q : ScalarTriple × E => q.1.2.1) (0,eta) :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hx : AnalyticAt ℂ (fun q : ScalarTriple × E => q.1.2.2) (0,eta) :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  have he : AnalyticAt ℂ (fun q : ScalarTriple × E => q.2) (0,eta) := analyticAt_snd
  have hnum := (familySlope_analyticAt_center phi hphi hB).fun_comp_of_eq
    (f:=fun q : ScalarTriple × E => ((q.1.1,q.1.2.1+q.1.2.2),q.2))
    ((ht.prod (hd.add hx)).prod he) (by simp)
  have hden : AnalyticAt ℂ (fun q : ScalarTriple × E =>
      centralParameterSlope (familyMember B q.2) phi q.1.2.1) (0,eta) :=
    analyticAt_const.mul (hB.fun_comp_of_eq
      ((analyticAt_const.sub (Complex.analyticAt_cos.comp hd)).prod he) (by simp))
  unfold residueSlopeRatio
  apply AnalyticAt.div
  · simpa only [familySlope_eq] using hnum
  · exact hden
  · exact centralParameterSlope_ne_zero (familyMember B eta) phi hphi 0
      (by simpa [familyMember] using hBn)

theorem compact_family_residueSlopeRatio_control (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hBn : ∀ eta ∈ K, B (0,eta)≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ eta ∈ K, ∀ t d x : ℂ,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖x‖<r →
      ‖residueSlopeRatio (familyMember B eta) phi hphi (t,(d,x))-1‖ ≤
        L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖x‖)*‖x‖) := by
  obtain ⟨r,L,hr,hL,h⟩ := compact_family_even_moving_center_control _ hK
    (fun eta heta => family_residueSlopeRatio_analyticAt B phi hphi eta (hB eta heta) (hBn eta heta))
    (fun eta _ t v => by simp only [residueSlopeRatio,zero_add,phaseParameterSlope_even])
  obtain ⟨s,hs,hball⟩ := compact_family_parameter_nonzero B hK hB hBn
  refine ⟨min r s,L,lt_min hr hs,hL,?_⟩
  intro eta heta t d x ht ht₀ hd hx
  have hb := hball eta heta (1-Complex.cos d) (ht₀.trans_le (min_le_right _ _))
  have hba : AnalyticAt ℂ (familyMember B eta) (1-Complex.cos d) :=
    hb.1.comp (f:=fun t : ℂ => (t,eta)) (analyticAt_id.prod analyticAt_const)
  have hh := h eta heta t (1-Complex.cos d) d x (ht.trans_le (min_le_left _ _))
    (ht₀.trans_le (min_le_left _ _)) (hd.trans_le (min_le_left _ _)) (hx.trans_le (min_le_left _ _))
  rwa [residueSlopeRatio_center (familyMember B eta) phi hphi d hba hb.2] at hh

theorem compact_family_poleParameterDerivative_inverse_uniform (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) (hBn : ∀ eta ∈ K, B (0,eta)≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ eta ∈ K, ∀ n : ℕ, n≠0 → ∀ t d : ℂ, ∀ v : Config n,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖v‖<r →
      poleParameterDerivative (familyMember B eta) phi hphi d t v≠0 ∧
      ‖((n:ℂ)*centralParameterSlope (familyMember B eta) phi d)/poleParameterDerivative (familyMember B eta) phi hphi d t v‖≤2 ∧
      ‖((n:ℂ)*centralParameterSlope (familyMember B eta) phi d)/poleParameterDerivative (familyMember B eta) phi hphi d t v-1‖≤
        L*(‖t-(1-Complex.cos d)‖+
          (‖d‖*(∑i,‖v i‖)+absoluteEnergy v)/(n:ℝ)) := by
  obtain ⟨r₀,L,hr₀,hL,hcontrol⟩ := compact_family_residueSlopeRatio_control B phi hphi hK hB hBn
  obtain ⟨rp,hrp,hphase⟩ := compact_family_phase_bidisk B phi hphi hK hB
  obtain ⟨rb,hrb,hBnball⟩ := compact_family_parameter_nonzero B hK hB hBn
  let r := min r₀ (min (rp/4) (min rb (min 1 (1/(8*L)))))
  have hr : 0<r := by dsimp [r]; positivity
  have hb : r≤r₀ ∧ r≤rp/4 ∧ r≤rb ∧ r≤1 ∧ r≤1/(8*L) := by
    have hh : r≤min r₀ (min (rp/4) (min rb (min 1 (1/(8*L))))) := le_rfl
    simpa only [le_min_iff] using hh
  have hLr : L*r≤1/8 := by
    have hh := (le_div_iff₀ (show 0<8*L by positivity)).mp hb.2.2.2.2
    nlinarith
  refine ⟨r,2*L,hr,by positivity,?_⟩
  intro eta heta n hn t d v ht ht₀ hd hv
  have hnR : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hi (i : Fin n) : ‖v i‖<r := (norm_le_pi_norm v i).trans_lt hv
  have hc : centralParameterSlope (familyMember B eta) phi d≠0 := centralParameterSlope_ne_zero (familyMember B eta) phi hphi d
    (hBnball eta heta _ (ht₀.trans_le hb.2.2.1)).2
  have ha (i : Fin n) : AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase (familyMember B eta) phi hphi z.1 z.2) (t,d+v i) := by
    have hh := hphase eta heta t (d+v i)
    apply (hh ?_ ?_).comp (f:=fun q : ℂ × ℂ => (q,eta))
      (analyticAt_id.prod analyticAt_const)
    · exact ht.trans_le (by linarith [hb.2.1])
    · have hh := norm_add_le d (v i)
      have hx := hi i
      linarith [hb.2.1]
  have he (i : Fin n) : ‖residueSlopeRatio (familyMember B eta) phi hphi (t,(d,v i))-1‖≤
      L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖v i‖)*‖v i‖) :=
    hcontrol eta heta t d (v i) (ht.trans_le hb.1) (ht₀.trans_le hb.1) (hd.trans_le hb.1) ((hi i).trans_le hb.1)
  have hsmall (i : Fin n) : ‖residueSlopeRatio (familyMember B eta) phi hphi (t,(d,v i))-1‖≤1/2 := by
    have hdt : ‖t-(1-Complex.cos d)‖≤2*r := (norm_sub_le _ _).trans (by linarith)
    have hx := (hi i).le
    have hquad : (‖d‖+‖v i‖)*‖v i‖≤2*r*r := by
      nlinarith [mul_le_mul hd.le hx (norm_nonneg _) hr.le,sq_le_sq₀ (norm_nonneg _) hr.le |>.mpr hx]
    have hquad' : (‖d‖+‖v i‖)*‖v i‖≤2*r := by nlinarith [hb.2.2.2.1]
    have hh := mul_le_mul_of_nonneg_left (add_le_add hdt hquad') hL.le
    nlinarith [he i]
  obtain ⟨hnz,hbound,herr⟩ := poleParameterDerivative_inverse_ratio hn (familyMember B eta) phi hphi d t v hc ha hsmall
  refine ⟨hnz,hbound,?_⟩
  have hsum : (∑i,‖residueSlopeRatio (familyMember B eta) phi hphi (t,(d,v i))-1‖)≤
      L*((n:ℝ)*‖t-(1-Complex.cos d)‖+‖d‖*(∑i,‖v i‖)+absoluteEnergy v) := by
    calc
      _ ≤ ∑i,L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖v i‖)*‖v i‖) := Finset.sum_le_sum (fun i _ => he i)
      _ = _ := by
        simp only [mul_add,add_mul,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
          Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,absoluteEnergy,pow_two]
        ring
  have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum hnR.le) (show 0≤(2:ℝ) by norm_num)
  apply herr.trans (hh.trans_eq _)
  field_simp
  ring


end
end IsingBulk.Joint.Negative
