import IsingBulk.HT22.Physical.FiniteAssembly.Calculus
namespace IsingBulk.HT22.Physical.FiniteAssembly
noncomputable section
open Set Filter
open scoped Topology BigOperators ContDiff

theorem analyticAt_list_sum (P : List (ℂ → ℂ)) (s : ℂ)
    (hP : ∀ f∈P,AnalyticAt ℂ f s) :
    AnalyticAt ℂ (fun t => (P.map (fun f => f t)).sum) s := by
  induction P with
  | nil => simpa only [List.map_nil,List.sum_nil] using (analyticAt_const (v := (0:ℂ)))
  | cons f P ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hP f (by simp)).add (ih (by intro g hg;exact hP g (by simp [hg])))

theorem iteratedDeriv_list_sum (P : List (ℂ → ℂ)) (s : ℂ)
    (hP : ∀ f∈P,AnalyticAt ℂ f s) (j : ℕ) :
    iteratedDeriv j (fun t => (P.map (fun f => f t)).sum) s=
      (P.map (fun f => iteratedDeriv j f s)).sum := by
  induction P with
  | nil => simp
  | cons f P ih =>
    have ht : ∀ g∈P,AnalyticAt ℂ g s := by intro g hg;exact hP g (by simp [hg])
    simp only [List.map_cons,List.sum_cons]
    rw [iteratedDeriv_fun_add (hP f (by simp)).contDiffAt (analyticAt_list_sum P s ht).contDiffAt,ih ht]

theorem iteratedDeriv_partition (F rem : ℂ → ℂ) (P : List (ℂ → ℂ)) (s : ℂ)
    (hpartition : F =ᶠ[𝓝 s] (fun t => (P.map (fun f => f t)).sum+rem t))
    (hP : ∀ f∈P,AnalyticAt ℂ f s) (hrem : AnalyticAt ℂ rem s) (j : ℕ) :
    iteratedDeriv j F s=(P.map (fun f => iteratedDeriv j f s)).sum+iteratedDeriv j rem s := by
  rw [hpartition.iteratedDeriv_eq,iteratedDeriv_fun_add (analyticAt_list_sum P s hP).contDiffAt hrem.contDiffAt,
    iteratedDeriv_list_sum P s hP]

/-- A finite list of genuinely bounded local terms has a common positive
radial interval and a finite uniform norm bound. -/
theorem list_sum_bounded_near_zero (P : List (ℝ → ℂ))
    (hP : ∀ f∈P,∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e → ‖f ε‖≤C) :
    ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e →
      ‖(P.map (fun f => f ε)).sum‖≤C := by
  induction P with
  | nil => exact ⟨1,1,by norm_num,by norm_num,by intros;simp⟩
  | cons f P ih =>
    obtain ⟨Cf,ef,hCf,hef,hf⟩ := hP f (by simp)
    obtain ⟨CP,eP,hCP,heP,hrest⟩ := ih (by intro g hg;exact hP g (by simp [hg]))
    refine ⟨Cf+CP,min ef eP,by positivity,lt_min hef heP,?_⟩
    intro ε hε hεe
    simp only [List.map_cons,List.sum_cons]
    exact (norm_add_le _ _).trans (add_le_add (hf ε hε (hεe.trans_le (min_le_left _ _)))
      (hrest ε hε (hεe.trans_le (min_le_right _ _))))

theorem finite_plus_log_bound (F rem : ℝ → ℂ) (P : List (ℝ → ℂ))
    (hP : ∀ f∈P,∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e → ‖f ε‖≤C)
    {CR eR : ℝ} (hCR : 0<CR) (heR : 0<eR)
    (hrem : ∀ ε : ℝ,0<ε → ε<eR → ‖rem ε‖≤CR*(1+|Real.log ε|))
    (hpartition : ∀ ε : ℝ,0<ε → ε<eR → F ε=(P.map (fun f => f ε)).sum+rem ε) :
    ∃ C e : ℝ,0<C ∧ 0<e ∧ ∀ ε : ℝ,0<ε → ε<e → ‖F ε‖≤C*(1+|Real.log ε|) := by
  obtain ⟨CP,eP,hCP,heP,hlocal⟩ := list_sum_bounded_near_zero P hP
  refine ⟨CP+CR,min eP eR,by positivity,lt_min heP heR,?_⟩
  intro ε hε hεe
  have hεR := hεe.trans_le (min_le_right eP eR)
  rw [hpartition ε hε hεR]
  have hh := (norm_add_le _ _).trans (add_le_add (hlocal ε hε (hεe.trans_le (min_le_left _ _)))
    (hrem ε hε hεR))
  exact hh.trans (by nlinarith [abs_nonneg (Real.log ε)])
end
end IsingBulk.HT22.Physical.FiniteAssembly
