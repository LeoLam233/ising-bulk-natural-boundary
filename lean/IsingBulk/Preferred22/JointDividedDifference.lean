/-
Copyright (c) 2026 Dehao Lin. Released under the MIT License.
See LICENSE-LT.txt in DividedDifferenceFoundation for the full license.
Adapted only by namespace/import relocation from the pinned LT repository
commit 43a9ce897ba12de0c96d6e1a636790cd93fae8ff.
Exact source hashes and adaptation scope: PROVENANCE.json.
-/
import IsingBulk.Preferred22.DividedDifferenceFoundation.HadamardFullDomain
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DSlope

/-! Joint analytic divided differences, including a moving base point.
Only the generic factorization and translation lemmas are retained; unrelated
physical phase definitions from the original import closure are absent. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric Filter DividedDifferenceFoundation
open scoped Topology
set_option maxHeartbeats 800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dslope_eq_of_factorization {f A : ℂ → ℂ} {s : Set ℂ}
    (hs : s ∈ 𝓝 (0:ℂ)) (hA : AnalyticAt ℂ A 0)
    (he : ∀ v ∈ s, f v-f 0=v*A v) : ∀ v ∈ s, dslope f 0 v=A v := by
  have hEq : f =ᶠ[𝓝 (0:ℂ)] fun v => v*A v+f 0 := by
    filter_upwards [hs] with v hv
    linear_combination he v hv
  have hd := (((hasDerivAt_id (0:ℂ)).mul hA.differentiableAt.hasDerivAt).add_const (f 0)).congr_of_eventuallyEq hEq
  have hd0 : deriv f 0=A 0 := by simpa using hd.deriv
  intro v hv
  by_cases hv0 : v=0
  · simpa [hv0] using hd0
  · rw [dslope_of_ne _ hv0, slope_def_field]
    simp only [sub_zero]
    rw [he v hv]
    field_simp

theorem dslope_translate (f : ℂ → ℂ) (d v : ℂ) :
    dslope (fun u => f (d+u)) 0 v=dslope f d (d+v) := by
  by_cases hv : v=0
  · simp [hv, deriv_comp_const_add]
  · have hdv : d+v ≠ d := by simpa using hv
    simp [dslope_of_ne _ hv, dslope_of_ne _ hdv, slope_def_field]

theorem coordinateHadamard_identity_axis {F : E × ℂ → ℂ} {x : E}
    (hf : AnalyticAt ℂ F (x,0)) :
    ∀ᶠ p : E × ℂ in 𝓝 (x,0), F p-F (p.1,0)=p.2*coordinateHadamard F p := by
  obtain ⟨r,hr,hs⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  filter_upwards [ball_mem_nhds (x,(0:ℂ)) hr] with p hp
  apply coordinateHadamard_identity_on_segment (f := F) p
  intro s hss
  apply hs
  rw [coordinateContraction_apply,Prod.dist_eq,dist_zero_right,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hss.1]
  have hp' : dist p.1 x<r ∧ ‖p.2‖<r := by
    simpa only [mem_ball,Prod.dist_eq,dist_zero_right,max_lt_iff] using hp
  exact max_lt hp'.1 ((mul_le_of_le_one_left (norm_nonneg _) hss.2).trans_lt hp'.2)

theorem analyticAt_joint_dslope_axis {F : E × ℂ → ℂ} {x : E}
    (hf : AnalyticAt ℂ F (x,0)) :
    AnalyticAt ℂ (fun p : E × ℂ => dslope (fun t => F (p.1,t)) 0 p.2) (x,0) := by
  have hA := coordinateHadamard_analyticAt_axis x hf
  have hid := coordinateHadamard_identity_axis hf
  rw [nhds_prod_eq] at hid
  obtain ⟨pa,hpa,pb,hpb,he⟩ := Filter.eventually_prod_iff.mp hid
  have hc : ContinuousAt (fun p : E × ℂ => (p.1,(0:ℂ))) (x,0) := by fun_prop
  have hrect : ∀ᶠ p : E × ℂ in 𝓝 (x,0), pa p.1 ∧ pb p.2 := by
    rw [nhds_prod_eq]
    exact Filter.eventually_prod_iff.mpr ⟨pa,hpa,pb,hpb,fun {_} hp {_} hq => ⟨hp,hq⟩⟩
  apply hA.congr
  filter_upwards [hrect,hc.tendsto.eventually hA.eventually_analyticAt] with p hp hAp
  have hAv : AnalyticAt ℂ (fun t => coordinateHadamard F (p.1,t)) 0 :=
    hAp.comp (f := fun t : ℂ => (p.1,t)) (analyticAt_const.prod analyticAt_id)
  exact (dslope_eq_of_factorization hpb hAv (fun t ht => he hp.1 ht) p.2 hp.2).symm

theorem analyticAt_joint_dslope_zero {F : E × ℂ → ℂ} {x : E} {t : ℂ}
    (hf : AnalyticAt ℂ F (x,t)) (h0 : AnalyticAt ℂ F (x,0)) :
    AnalyticAt ℂ (fun p : E × ℂ => dslope (fun s => F (p.1,s)) 0 p.2) (x,t) := by
  by_cases ht : t=0
  · subst t
    exact analyticAt_joint_dslope_axis hf
  · have hbase : AnalyticAt ℂ (fun p : E × ℂ => F (p.1,0)) (x,t) :=
      h0.fun_comp_of_eq (f := fun p : E × ℂ => (p.1,(0:ℂ))) (analyticAt_fst.prod analyticAt_const) rfl
    have hquot : AnalyticAt ℂ (fun p : E × ℂ => (F p-F (p.1,0))/p.2) (x,t) :=
      (hf.sub hbase).div analyticAt_snd ht
    apply hquot.congr
    filter_upwards [continuousAt_snd.eventually_ne ht] with p hp
    rw [dslope_of_ne _ hp,slope_def_field,sub_zero]

theorem analyticAt_moving_dslope {F : E × ℂ → ℂ} {T : E → ℂ} {x : E} {t : ℂ}
    (hf : AnalyticAt ℂ F (x,t)) (hfT : AnalyticAt ℂ F (x,T x)) (hT : AnalyticAt ℂ T x) :
    AnalyticAt ℂ (fun p : E × ℂ => dslope (fun s => F (p.1,s)) (T p.1) p.2) (x,t) := by
  let G : E × ℂ → ℂ := fun p => F (p.1,T p.1+p.2)
  have hG : AnalyticAt ℂ G (x,t-T x) := hf.fun_comp_of_eq
    (f := fun p : E × ℂ => (p.1,T p.1+p.2))
    (analyticAt_fst.prod ((hT.comp (f := Prod.fst) analyticAt_fst).add analyticAt_snd)) (by simp)
  have hG0 : AnalyticAt ℂ G (x,0) := hfT.fun_comp_of_eq
    (f := fun p : E × ℂ => (p.1,T p.1+p.2))
    (analyticAt_fst.prod ((hT.comp (f := Prod.fst) analyticAt_fst).add analyticAt_snd)) (by simp)
  have hq := analyticAt_joint_dslope_zero hG hG0
  have hm : AnalyticAt ℂ (fun p : E × ℂ => (p.1,p.2-T p.1)) (x,t) :=
    analyticAt_fst.prod (analyticAt_snd.sub (hT.comp (f := Prod.fst) analyticAt_fst))
  have hh := hq.fun_comp_of_eq (f := fun p : E × ℂ => (p.1,p.2-T p.1)) hm rfl
  convert hh using 1
  funext p
  dsimp only [G,Function.comp_def]
  simpa only [add_sub_cancel] using (dslope_translate (fun s => F (p.1,s)) (T p.1) (p.2-T p.1)).symm


end
end IsingBulk.Preferred22
