import IsingBulk.Tail.SelectorHypotheses
import IsingBulk.Tail.SelectorSourcePiola
import IsingBulk.First.SourceAngularPeriodicity

/-! Exact periodic boundary identification for the source homotopy and
replacement-minor flux. No real cutoff is analytically continued. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

 theorem periodic_tuple_update {N : ℕ} {g : ℝ → ℝ} (hg : Function.Periodic g (2*Real.pi))
    (θ : Fin N → ℝ) (q : Fin N) :
    (fun i => g (Function.update θ q (θ q+2*Real.pi) i)) = (fun i => g (θ i)) := by
  funext i
  by_cases hi : i=q
  · subst i; simp only [Function.update_self]; exact hg (θ q)
  · rw [Function.update_of_ne hi]

 theorem shiftMap_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (τ : ℝ) (θ : Fin N → ℝ) (q : Fin N) :
    shiftMap f τ (Function.update θ q (θ q+2*Real.pi)) = shiftMap f τ θ := by
  unfold shiftMap
  rw [periodic_tuple_update hf.p_periodic,periodic_tuple_update hf.m_periodic]

 theorem angularJacobian_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (τ lam : ℝ) (θ : Fin N → ℝ) (q : Fin N) :
    angularJacobian f τ lam (Function.update θ q (θ q+2*Real.pi)) = angularJacobian f τ lam θ := by
  unfold angularJacobian
  rw [periodic_tuple_update hf.p_periodic,periodic_tuple_update hf.m_periodic,
    periodic_tuple_update (periodic_derivative hf.p_periodic),
    periodic_tuple_update (periodic_derivative hf.m_periodic)]

 theorem deformedPoint_eq_angle {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f r τ lam θ i = anglePoint r (θ i)*Complex.exp (lam*shiftMap f τ θ i:ℝ) := by
  simp only [deformedPoint,anglePoint,circleMap,zero_add,Complex.exp_add,shiftMap]
  rw [mul_comm Complex.I (θ i:ℂ)]
  ring

 theorem deformedPoint_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (r τ lam : ℝ) (θ : Fin N → ℝ) (q : Fin N) :
    deformedPoint f r τ lam (Function.update θ q (θ q+2*Real.pi)) = deformedPoint f r τ lam θ := by
  funext i
  rw [deformedPoint_eq_angle,deformedPoint_eq_angle,shiftMap_periodic f hf]
  have he := congrFun (angleTuple_update_period r θ q) i
  exact congrArg (fun z => z*Complex.exp (lam*shiftMap f τ θ i:ℝ)) he

 theorem angularSelector_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (θ : Fin N → ℝ) (q : Fin N) :
    angularSelector f (Function.update θ q (θ q+2*Real.pi)) = angularSelector f θ := by
  unfold angularSelector
  rw [periodic_tuple_update hf.a_periodic]

 theorem pulledDensity_periodic (N : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    (r τ lam : ℝ) (s : ℂ) : CoordinatePeriodic N (pulledDensity f r τ lam s) := by
  intro θ q
  unfold pulledDensity
  rw [angularJacobian_periodic f hf,deformedPoint_periodic f hf]

 theorem homotopyFlux_eq_contour {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0 < r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (q : Fin N) :
    homotopyFlux f r τ lam s θ q =
      (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
      (∏ i, deformedPoint f r τ lam θ i)*
      canceledReducedDensity (fun i => globalRoot s (deformedPoint f r τ lam θ i))
        (deformedPoint f r τ lam θ)*
      ((angularJacobian f τ lam θ).updateCol q (complexShift f τ θ)).det := by
  unfold homotopyFlux logDensity
  rw [show deformedPoint f r τ lam θ = (fun i => Complex.exp (logContour f r τ lam θ i)) from
    funext (deformedPoint_exp_log f hr τ lam θ)]

 theorem homotopyFlux_periodic (N : ℕ) (f : SelectorFunctions) (hf : RegularSelector f)
    {r : ℝ} (hr : 0 < r) (τ lam : ℝ) (s : ℂ) (q : Fin N) :
    CoordinatePeriodic N (fun θ => homotopyFlux f r τ lam s θ q) := by
  intro θ i
  dsimp only
  rw [homotopyFlux_eq_contour f hr,homotopyFlux_eq_contour f hr,
    deformedPoint_periodic f hf,angularJacobian_periodic f hf]
  have he : complexShift f τ (Function.update θ i (θ i+2*Real.pi)) = complexShift f τ θ := by
    unfold complexShift
    rw [shiftMap_periodic f hf]
  rw [he]

 theorem coordinatePeriodic_faces {n : ℕ} {g : (Fin (n+1) → ℝ) → ℂ}
    (hg : CoordinatePeriodic (n+1) g) (i : Fin (n+1)) (x : Fin n → ℝ) :
    g (i.insertNth (2*Real.pi) x) = g (i.insertNth 0 x) := by
  let x0 : Fin (n+1) → ℝ := i.insertNth 0 x
  have hh := hg x0 i
  have he : Function.update x0 i (x0 i+2*Real.pi) = i.insertNth (2*Real.pi) x := by
    funext j
    rcases i.eq_self_or_eq_succAbove j with rfl | ⟨j,rfl⟩
    · simp [x0]
    · simp [x0,Fin.succAbove_ne]
  rwa [he] at hh

end
end IsingBulk.Tail
