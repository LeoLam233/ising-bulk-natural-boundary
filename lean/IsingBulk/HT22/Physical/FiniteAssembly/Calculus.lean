import IsingBulk.HT22.Geometry.LocalizedSignedContour
import IsingBulk.HT22.Physical.WeightedAnalytic
namespace IsingBulk.HT22.Physical.FiniteAssembly
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

variable {X : Type*} [MeasurableSpace X]

theorem integrable_list_sum (μ : Measure X) (P : List (X → ℂ))
    (hP : ∀ f∈P,Integrable f μ) :
    Integrable (fun x => (P.map (fun f => f x)).sum) μ := by
  induction P with
  | nil => simp
  | cons f P ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hP f (by simp)).add (ih (by intro g hg;exact hP g (by simp [hg])))

theorem integral_list_sum (μ : Measure X) (P : List (X → ℂ))
    (hP : ∀ f∈P,Integrable f μ) :
    (∫ x,(P.map (fun f => f x)).sum ∂μ)=(P.map (fun f => ∫ x,f x ∂μ)).sum := by
  induction P with
  | nil => simp
  | cons f P ih =>
    have ht : ∀ g∈P,Integrable g μ := by intro g hg;exact hP g (by simp [hg])
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hP f (by simp)) (integrable_list_sum μ P ht),ih ht]

def weightedIntegral (μ : Measure X) (F : ℂ → X → ℂ) (ψ : X → ℝ) (t : ℂ) : ℂ :=
  ∫ x,(ψ x:ℂ)*F t x ∂μ

omit [MeasurableSpace X] in
theorem weight_partition (P : List (X → ℝ)) (rem : X → ℝ)
    (hpartition : ∀ x,(P.map (fun ψ => ψ x)).sum+rem x=1) (F : X → ℂ) (x : X) :
    F x=(P.map (fun ψ => (ψ x:ℂ)*F x)).sum+(rem x:ℂ)*F x := by
  have hsum : (P.map (fun ψ => (ψ x:ℂ)*F x)).sum=
      (((P.map (fun ψ => ψ x)).sum : ℝ):ℂ)*F x := by
    clear hpartition
    induction P with
    | nil => simp
    | cons ψ P ih => simp only [List.map_cons,List.sum_cons,Complex.ofReal_add,add_mul,ih]
  rw [hsum,←add_mul,←Complex.ofReal_add,hpartition,Complex.ofReal_one,one_mul]

theorem weighted_integral_partition (μ : Measure X) (F : ℂ → X → ℂ)
    (P : List (X → ℝ)) (rem : X → ℝ)
    (hpartition : ∀ x,(P.map (fun ψ => ψ x)).sum+rem x=1) (t : ℂ)
    (hP : ∀ ψ∈P,Integrable (fun x => (ψ x:ℂ)*F t x) μ)
    (hrem : Integrable (fun x => (rem x:ℂ)*F t x) μ) :
    (∫ x,F t x ∂μ)=(P.map (fun ψ => weightedIntegral μ F ψ t)).sum+weightedIntegral μ F rem t := by
  have hint : ∀ f∈P.map (fun ψ x => (ψ x:ℂ)*F t x),Integrable f μ := by
    intro f hf
    obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp hf
    exact hP ψ hψ
  have hi := integrable_list_sum μ (P.map (fun ψ x => (ψ x:ℂ)*F t x)) hint
  simp only [List.map_map,Function.comp_def] at hi
  conv_lhs => arg 2;ext x;rw [weight_partition P rem hpartition (F t) x]
  rw [integral_add hi hrem]
  congr 1
  have h := integral_list_sum μ (P.map (fun ψ x => (ψ x:ℂ)*F t x)) (by
    intro f hf
    obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp hf
    exact hP ψ hψ)
  simpa only [List.map_map,Function.comp_def,weightedIntegral] using h

end
end IsingBulk.HT22.Physical.FiniteAssembly
