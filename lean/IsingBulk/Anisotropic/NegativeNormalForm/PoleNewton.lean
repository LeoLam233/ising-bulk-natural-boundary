import IsingBulk.Anisotropic.NegativeNormalForm.UniformPhaseSlope
import IsingBulk.Anisotropic.NegativeNormalForm.HalfContraction
import Mathlib.Analysis.Calculus.MeanValue

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric
open scoped BigOperators Topology

theorem mean_sub_const {n : ℕ} (hn : n≠0) (v : Config n) (c : ℂ) :
    mean (fun i => v i-c)=mean v-c := by
  have hn' : (n:ℂ)≠0 := by exact_mod_cast hn
  simp only [mean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem norm_mean_sub_le {n : ℕ} (hn : n≠0) (v : Config n) (c : ℂ) {M : ℝ}
    (hM : 0≤M) (hv : ∀ i, ‖v i-c‖≤M) : ‖mean v-c‖≤M := by
  rw [← mean_sub_const hn]
  exact (norm_mean_le hn _).trans ((pi_norm_le_iff_of_nonneg hM).mpr hv)

def poleNewton {n : ℕ} (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    (d : ℂ) (v : Config n) (t : ℂ) : ℂ :=
  t-(centralParameterSlope B phi 0)⁻¹*poleAverage B phi hphi d t v

theorem poleAverage_hasDerivAt {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (ha : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t,d+v i)) :
    HasDerivAt (fun s => poleAverage B phi hphi d s v)
      (mean (fun i => phaseParameterSlope B phi hphi (t,d+v i))) t := by
  have hh (i : Fin n) : HasDerivAt (fun s => negativePhase B phi hphi s (d+v i))
      (phaseParameterSlope B phi hphi (t,d+v i)) t := by
    rw [phaseParameterSlope_eq]
    exact ((ha i).fun_comp_of_eq (f := fun s : ℂ => (s,d+v i))
      (analyticAt_id.prod analyticAt_const) rfl).differentiableAt.hasDerivAt
  simpa only [poleAverage,poleEquation,mean,Finset.sum_apply] using
    (HasDerivAt.sum (u := Finset.univ) (fun i _ => (hh i).sub_const ((phi:ℂ)*Complex.I))).div_const (n:ℂ)

theorem poleNewton_hasDerivAt {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (ha : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t,d+v i)) :
    HasDerivAt (poleNewton B phi hphi d v)
      (1-(centralParameterSlope B phi 0)⁻¹*mean (fun i => phaseParameterSlope B phi hphi (t,d+v i))) t :=
  (hasDerivAt_id t).sub ((poleAverage_hasDerivAt B phi hphi d t v ha).const_mul _)

theorem poleNewton_slope_norm_le {n : ℕ} (hn : n≠0) (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (hc : centralParameterSlope B phi 0≠0)
    (hb : ∀ i, ‖phaseParameterSlope B phi hphi (t,d+v i)-centralParameterSlope B phi 0‖≤
      ‖centralParameterSlope B phi 0‖/4) :
    ‖1-(centralParameterSlope B phi 0)⁻¹*mean (fun i => phaseParameterSlope B phi hphi (t,d+v i))‖≤1/4 := by
  let c := centralParameterSlope B phi 0
  let a := mean (fun i => phaseParameterSlope B phi hphi (t,d+v i))
  have hh : ‖a-c‖≤‖c‖/4 := norm_mean_sub_le hn _ c (by positivity) hb
  have hc' : c≠0 := hc
  have he : 1-c⁻¹*a= -c⁻¹*(a-c) := by field_simp [hc']; ring
  change ‖1-c⁻¹*a‖≤_
  rw [he,norm_mul,norm_neg,norm_inv]
  calc
    _ ≤ ‖c‖⁻¹*(‖c‖/4) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (norm_nonneg _))
    _ = 1/4 := by field_simp [norm_ne_zero_iff.mpr hc']

theorem poleEquation_analyticAt_of_phase {n : ℕ} (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (ha : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t,d+v i)) :
    AnalyticAt ℂ (fun z : Config n × ℂ => poleEquation B phi hphi d z.2 z.1) (v,t) := by
  apply Finset.univ.analyticAt_fun_sum
  intro i _
  apply AnalyticAt.sub _ analyticAt_const
  exact (ha i).fun_comp_of_eq
    (f := fun z : Config n × ℂ => (z.2,d+z.1 i))
    (analyticAt_snd.prod (analyticAt_const.add
      ((ContinuousLinearMap.proj i : Config n →L[ℂ] ℂ).analyticAt _ |>.comp
        (f := fun z : Config n × ℂ => z.1) analyticAt_fst))) rfl

theorem poleEquation_parameter_deriv_ne_zero_of_close {n : ℕ} (hn : n≠0)
    (B : ℂ → ℂ) (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config n)
    (hc : centralParameterSlope B phi 0≠0)
    (ha : ∀ i, AnalyticAt ℂ (fun z : ℂ × ℂ => negativePhase B phi hphi z.1 z.2) (t,d+v i))
    (hb : ∀ i, ‖phaseParameterSlope B phi hphi (t,d+v i)-centralParameterSlope B phi 0‖≤
      ‖centralParameterSlope B phi 0‖/4) :
    deriv (fun s => poleEquation B phi hphi d s v) t≠0 := by
  let a := mean (fun i => phaseParameterSlope B phi hphi (t,d+v i))
  have han : a≠0 := by
    intro he
    have hh := norm_mean_sub_le hn (fun i => phaseParameterSlope B phi hphi (t,d+v i))
      (centralParameterSlope B phi 0) (by positivity) hb
    change ‖a-centralParameterSlope B phi 0‖≤_ at hh
    rw [he,zero_sub,norm_neg] at hh
    have hp := norm_pos_iff.mpr hc
    linarith
  have hn' : (n:ℂ)≠0 := by exact_mod_cast hn
  have hh := (poleAverage_hasDerivAt B phi hphi d t v ha).mul_const (n:ℂ)
  have he : (fun s => poleAverage B phi hphi d s v*(n:ℂ))=
      (fun s => poleEquation B phi hphi d s v) := by
    funext s
    exact div_mul_cancel₀ _ hn'
  rw [he] at hh
  rw [hh.deriv]
  exact mul_ne_zero han hn'

end
end IsingBulk.Anisotropic.NegativeNormalForm
