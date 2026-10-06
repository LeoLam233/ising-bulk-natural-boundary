import IsingBulk.Tail.MixedActiveChartSmooth

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff

theorem mixedCoordinateTransport_freeze {N : ℕ} (S : Finset (Fin N)) (background : Fin N → ℝ)
    (V : ℂ → (Fin N → ℝ) → Fin N → ℂ) (A : ℂ → (Fin N → ℝ) → ℂ)
    (hV : ∀ i,i∉S → ∀ s x,V s x i=0) (s : ℂ) (x : Fin N → ℝ) :
    mixedCoordinateTransport (fun t y => V t (mixedFreeze S background y))
      (fun t y => A t (mixedFreeze S background y)) s x=
    mixedCoordinateTransport V A s (mixedFreeze S background x) := by
  unfold mixedCoordinateTransport
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [coordDeriv_mixedFreeze]
  by_cases hi : i∈S
  · simp only [hi,ite_true]
  · simp [hi,hV i hi]

theorem lieStep_mixedFreeze {n : ℕ} (S : Finset (Fin (n+1))) (background : Fin (n+1) → ℝ)
    (V : ℂ → (Fin (n+1) → ℝ) → Fin (n+1) → ℂ) (A : ℂ → (Fin (n+1) → ℝ) → ℂ)
    (hV : ∀ i,i∉S → ∀ s x,V s x i=0) (s : ℂ) (x : Fin (n+1) → ℝ)
    (hVA : ∀ i,DifferentiableAt ℝ (fun y => V s y i*A s y) (mixedFreeze S background x)) :
    IsingBulk.Lie.lieStep (fun t y => V t (mixedFreeze S background y))
      (fun t y => A t (mixedFreeze S background y)) s x=
    IsingBulk.Lie.lieStep V A s (mixedFreeze S background x) := by
  have hh := mixedCoordinateLie_freeze S background V A hV s x
  rw [mixedCoordinateLie_eq_lie _ _ _ _ (fun i => (hVA i).comp x
    ((mixedFreeze_contDiff S background).differentiable (by simp) x)),
    mixedCoordinateLie_eq_lie _ _ _ _ hVA] at hh
  exact hh

theorem ParameterSmoothOn.angular_differentiableAt {N : ℕ} {Ω : Set (ℂ × (Fin N → ℝ))}
    {F : ℂ → (Fin N → ℝ) → ℂ} (hF : ParameterSmoothOn Ω F)
    {s : ℂ} {x : Fin N → ℝ} (h : (s,x)∈Ω) : DifferentiableAt ℝ (F s) x := by
  exact (hF (s,x) h).1.differentiableAt (by simp) |>.comp x
    ((differentiableAt_const s).prodMk differentiableAt_id)

end
end IsingBulk.Tail
