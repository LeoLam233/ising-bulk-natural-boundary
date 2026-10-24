import IsingBulk.Anisotropic.NegativeNormalForm.Hadamard
import IsingBulk.Anisotropic.NegativeNormalForm.ProjectionLinear
import Mathlib.Analysis.Analytic.Constructions

/-! A concrete analytic mean factorization for a projected separable map.
The only denominator is the sum of reciprocal roots, nonzero at the center.
In particular, the complex quadratic form is never a denominator. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology BigOperators

def meanCoefficients {n : ℕ} (S : Config n) : Config n :=
  project (fun i => (1-(S i)⁻¹)/(∑ j, (S j)⁻¹))

theorem meanCoefficients_zeroMean {n : ℕ} (hn : n ≠ 0) (S : Config n) :
    ZeroMean (meanCoefficients S) := project_zeroMean hn _

@[simp] theorem meanCoefficients_one {n : ℕ} : meanCoefficients (1:Config n)=0 := by
  have he : (fun i : Fin n => (1-((1:Config n) i)⁻¹)/(∑ j, ((1:Config n) j)⁻¹))=0 := by
    ext i
    simp
  rw [meanCoefficients,he,← projectCLM_apply,map_zero]

theorem meanCoefficients_factorization {n : ℕ} (v w S : Config n)
    (hv : ZeroMean v) (hw : ZeroMean w) (hS : ∀ i, S i ≠ 0)
    (hden : (∑ j, (S j)⁻¹) ≠ 0)
    (hproj : project (fun i => v i*S i)=w) :
    pairing w (meanCoefficients S)=mean (fun i => v i*S i) := by
  let mu := mean (fun i => v i*S i)
  have hsum : (∑ i, w i*(S i)⁻¹) = -mu*(∑ i, (S i)⁻¹) := by
    calc
      _ = ∑ i, (v i-mu*(S i)⁻¹) := by
        apply Finset.sum_congr rfl
        intro i _
        have hw' := congrFun hproj i
        change v i*S i-mu=w i at hw'
        rw [← hw']
        field_simp [hS i]
      _ = _ := by
        rw [Finset.sum_sub_distrib,← Finset.mul_sum,show ∑ i, v i=0 from hv]
        ring
  rw [meanCoefficients,pairing_project_right w _ hw]
  change (∑ i, w i*((1-(S i)⁻¹)/(∑ j, (S j)⁻¹)))=mu
  simp_rw [← mul_div_assoc,mul_sub,mul_one]
  rw [← Finset.sum_div,Finset.sum_sub_distrib,show ∑ i, w i=0 from hw,hsum]
  simp [hden]

theorem meanCoefficients_analyticAt {n : ℕ} (hn : n ≠ 0)
    (S : Config n → Config n) (hS : AnalyticAt ℂ S 0) (hS0 : S 0=1) :
    AnalyticAt ℂ (fun w => meanCoefficients (S w)) 0 := by
  have hSi (i : Fin n) : AnalyticAt ℂ (fun w => S w i) 0 := analyticAt_pi_iff.mp hS i
  have hInv (i : Fin n) : AnalyticAt ℂ (fun w => (S w i)⁻¹) 0 :=
    (hSi i).inv (by simp [hS0])
  have hden : AnalyticAt ℂ (fun w => ∑ i, (S w i)⁻¹) 0 := Finset.analyticAt_fun_sum Finset.univ (fun i _ => hInv i)
  have hden0 : (∑ i, (S 0 i)⁻¹) ≠ 0 := by simp [hS0,hn]
  have hraw : AnalyticAt ℂ (fun w => fun i => (1-(S w i)⁻¹)/(∑ j, (S w j)⁻¹)) 0 := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (analyticAt_const.sub (hInv i)).div hden hden0
  have hp := ((projectCLM n).analyticAt _).comp hraw
  simpa only [Function.comp_def,projectCLM_apply,meanCoefficients] using hp

end
end IsingBulk.Anisotropic.NegativeNormalForm
