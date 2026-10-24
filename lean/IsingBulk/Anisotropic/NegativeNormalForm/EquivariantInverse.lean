import IsingBulk.Anisotropic.NegativeNormalForm.ProjectedExtension
import IsingBulk.Anisotropic.NegativeNormalForm.PermutationPole

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped Topology BigOperators

def equivariantAverage {n : ℕ} (V : Config n → Config n) (v : Config n) : Config n := fun i =>
  (∑ e : Equiv.Perm (Fin n), V (permute e v) (e.symm i))/Fintype.card (Equiv.Perm (Fin n))

theorem equivariantAverage_permute {n : ℕ} (V : Config n → Config n)
    (e : Equiv.Perm (Fin n)) (v : Config n) :
    equivariantAverage V (permute e v)=permute e (equivariantAverage V v) := by
  ext i
  unfold equivariantAverage
  change (∑ f : Equiv.Perm (Fin n), V (permute f (permute e v)) (f.symm i))/_ =
    (∑ f : Equiv.Perm (Fin n), V (permute f v) (f.symm (e i)))/_
  congr 1
  have hs (f : Equiv.Perm (Fin n)) : (e*f).symm (e i)=f.symm i := by
    apply (e*f).injective
    simp
  simpa [permute,Function.comp_def,hs] using Equiv.sum_comp (Equiv.mulLeft e)
    (fun f : Equiv.Perm (Fin n) => V (permute f v) (f.symm (e i)))

theorem equivariantAverage_eventuallyEq {n : ℕ} (V : Config n → Config n)
    (hV : ∀ e : Equiv.Perm (Fin n), ∀ᶠ v in 𝓝 (0:Config n), V (permute e v)=permute e (V v)) :
    equivariantAverage V =ᶠ[𝓝 (0:Config n)] V := by
  have hall := Filter.eventually_all.mpr hV
  filter_upwards [hall] with v hv
  ext i
  have hc : (Fintype.card (Equiv.Perm (Fin n)):ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [equivariantAverage,hv]
  simp [permute,hc]

theorem projectedExtension_permute {n : ℕ} (U : Config n → Config n)
    (hU : ∀ e : Equiv.Perm (Fin n), ∀ v, U (permute e v)=permute e (U v))
    (e : Equiv.Perm (Fin n)) (v : Config n) :
    projectedExtension U (permute e v)=permute e (projectedExtension U v) := by
  ext i
  simp only [projectedExtension,projectCLM_apply,project_permute,hU]
  change project (U (project v)) (e i)+meanCLM n (permute e v)=project (U (project v)) (e i)+meanCLM n v
  rw [meanCLM_apply,meanCLM_apply,mean_permute]

/-- Equivariance of the inverse germ is forced by the two genuine inverse
identities, before averaging is used to select a globally equivariant representative. -/
theorem inverse_eventually_permute {n : ℕ} (F V : Config n → Config n)
    (hV : ContinuousAt V 0) (hV0 : V 0=0)
    (hleft : ∀ᶠ v in 𝓝 (0:Config n), V (F v)=v)
    (hright : ∀ᶠ w in 𝓝 (0:Config n), F (V w)=w)
    (hF : ∀ e : Equiv.Perm (Fin n), ∀ v, F (permute e v)=permute e (F v))
    (e : Equiv.Perm (Fin n)) :
    ∀ᶠ w in 𝓝 (0:Config n), V (permute e w)=permute e (V w) := by
  have ht : Filter.Tendsto (fun w => permute e (V w)) (𝓝 0) (𝓝 0) := by
    simpa only [hV0,map_zero,permuteCLM_apply,Function.comp_def] using
      ((permuteCLM e).continuous.continuousAt.comp hV).tendsto
  filter_upwards [hright,ht.eventually hleft] with w hw hl
  rw [hF e,hw] at hl
  exact hl

theorem exists_equivariant_projected_inverse {n : ℕ} (hn : n ≠ 0) (U : Config n → Config n)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0=0)
    (hdU : HasFDerivAt U (ContinuousLinearMap.id ℂ (Config n)) 0)
    (hsym : ∀ e : Equiv.Perm (Fin n), ∀ v, U (permute e v)=permute e (U v)) :
    ∃ V : Config n → Config n, AnalyticAt ℂ V 0 ∧ V 0=0 ∧
      HasFDerivAt V (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
      (∀ e : Equiv.Perm (Fin n), ∀ v, V (permute e v)=permute e (V v)) ∧
      (∀ᶠ w in 𝓝 (0:Config n), projectedExtension U (V w)=w ∧
        (ZeroMean w → ZeroMean (V w) ∧ project (U (V w))=w)) := by
  obtain ⟨V,hV,hV0,hdV,hl,hr⟩ := exists_projected_inverse hn U hU hU0 hdU
  have hsymV := inverse_eventually_permute (projectedExtension U) V hV.continuousAt hV0 hl
    (hr.mono (fun _ h => h.1)) (projectedExtension_permute U hsym)
  have he := equivariantAverage_eventuallyEq V hsymV
  refine ⟨equivariantAverage V,hV.congr he.symm,(he.self_of_nhds).trans hV0,
    hdV.congr_of_eventuallyEq he,fun e v => equivariantAverage_permute V e v,?_⟩
  filter_upwards [hr,he] with w hw hew
  simpa only [hew] using hw

end
end IsingBulk.Anisotropic.NegativeNormalForm
