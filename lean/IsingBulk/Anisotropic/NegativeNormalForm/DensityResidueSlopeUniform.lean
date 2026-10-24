import IsingBulk.Anisotropic.NegativeNormalForm.DensityResidueAverage
import IsingBulk.Anisotropic.NegativeNormalForm.PairEnergySum

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- The actual inverse Γ_t ratio is uniformly controlled on one fixed ball,
without an n q smallness premise. -/
theorem poleParameterDerivative_inverse_uniform (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hBn : B 0≠0) :
    ∃ r L : ℝ, 0<r ∧ 0<L ∧ ∀ n : ℕ, n≠0 → ∀ t d : ℂ, ∀ v : Config n,
      ‖t‖<r → ‖1-Complex.cos d‖<r → ‖d‖<r → ‖v‖<r →
      poleParameterDerivative B phi hphi d t v≠0 ∧
      ‖((n:ℂ)*centralParameterSlope B phi d)/poleParameterDerivative B phi hphi d t v‖≤2 ∧
      ‖((n:ℂ)*centralParameterSlope B phi d)/poleParameterDerivative B phi hphi d t v-1‖≤
        L*(‖t-(1-Complex.cos d)‖+
          (‖d‖*(∑i,‖v i‖)+absoluteEnergy v)/(n:ℝ)) := by
  obtain ⟨r₀,L,hr₀,hL,hcontrol⟩ := residueSlopeRatio_control B phi hphi hB hBn
  obtain ⟨rp,hrp,hphase⟩ := negativePhase_fixed_bidisk B phi hphi hB
  obtain ⟨rb,hrb,hBnball⟩ := Metric.mem_nhds_iff.mp (hB.continuousAt.eventually_ne hBn)
  let r := min r₀ (min (rp/4) (min rb (min 1 (1/(8*L)))))
  have hr : 0<r := by dsimp [r]; positivity
  have hb : r≤r₀ ∧ r≤rp/4 ∧ r≤rb ∧ r≤1 ∧ r≤1/(8*L) := by
    have hh : r≤min r₀ (min (rp/4) (min rb (min 1 (1/(8*L))))) := le_rfl
    simpa only [le_min_iff] using hh
  have hLr : L*r≤1/8 := by
    have hh := (le_div_iff₀ (show 0<8*L by positivity)).mp hb.2.2.2.2
    nlinarith
  refine ⟨r,2*L,hr,by positivity,?_⟩
  intro n hn t d v ht ht₀ hd hv
  have hnR : 0<(n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hi (i : Fin n) : ‖v i‖<r := (norm_le_pi_norm v i).trans_lt hv
  have hc : centralParameterSlope B phi d≠0 := centralParameterSlope_ne_zero B phi hphi d
    (hBnball (by simpa using ht₀.trans_le hb.2.2.1))
  have ha (i : Fin n) : AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t,d+v i) := by
    apply hphase t (d+v i)
    · exact ht.trans_le (by linarith [hb.2.1])
    · have hh := norm_add_le d (v i)
      have hx := hi i
      linarith [hb.2.1]
  have he (i : Fin n) : ‖residueSlopeRatio B phi hphi (t,(d,v i))-1‖≤
      L*(‖t-(1-Complex.cos d)‖+(‖d‖+‖v i‖)*‖v i‖) :=
    hcontrol t d (v i) (ht.trans_le hb.1) (ht₀.trans_le hb.1) (hd.trans_le hb.1) ((hi i).trans_le hb.1)
  have hsmall (i : Fin n) : ‖residueSlopeRatio B phi hphi (t,(d,v i))-1‖≤1/2 := by
    have hdt : ‖t-(1-Complex.cos d)‖≤2*r := (norm_sub_le _ _).trans (by linarith)
    have hx := (hi i).le
    have hquad : (‖d‖+‖v i‖)*‖v i‖≤2*r*r := by
      nlinarith [mul_le_mul hd.le hx (norm_nonneg _) hr.le,sq_le_sq₀ (norm_nonneg _) hr.le |>.mpr hx]
    have hquad' : (‖d‖+‖v i‖)*‖v i‖≤2*r := by nlinarith [hb.2.2.2.1]
    have hh := mul_le_mul_of_nonneg_left (add_le_add hdt hquad') hL.le
    nlinarith [he i]
  obtain ⟨hnz,hbound,herr⟩ := poleParameterDerivative_inverse_ratio hn B phi hphi d t v hc ha hsmall
  refine ⟨hnz,hbound,?_⟩
  have hsum : (∑i,‖residueSlopeRatio B phi hphi (t,(d,v i))-1‖)≤
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
end IsingBulk.Anisotropic.NegativeNormalForm
