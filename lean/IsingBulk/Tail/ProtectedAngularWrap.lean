import IsingBulk.Tail.ProtectedSourceRoots

/-! The source uses signed angles, while the actual integration box is
[0,2π]^N. Periodic wrapping preserves the complete coupled contour, including
its occupancy, before any signed support estimate is applied. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set

def signedAngle (t : ℝ) : ℝ := if t ≤ Real.pi then t else t-2*Real.pi
def signedAngles {N : ℕ} (θ : Fin N → ℝ) : Fin N → ℝ := fun i => signedAngle (θ i)

theorem signedAngle_abs_le_pi {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2*Real.pi) :
    |signedAngle t| ≤ Real.pi := by
  unfold signedAngle
  split_ifs with h
  · rw [abs_of_nonneg ht0]
    exact h
  · rw [abs_of_nonpos (by linarith : t-2*Real.pi ≤ 0)]
    linarith

theorem signedAngles_mem_signed_box {N : ℕ} {θ : Fin N → ℝ} (hθ : θ ∈ angleBox N) :
    ∀ i, |signedAngles θ i| ≤ Real.pi := by
  intro i
  exact signedAngle_abs_le_pi (hθ.1 i) (hθ.2 i)

theorem periodic_signedAngle {E : Type*} (f : ℝ → E) (hf : Function.Periodic f (2*Real.pi))
    (t : ℝ) : f (signedAngle t)=f t := by
  unfold signedAngle
  split_ifs
  · rfl
  · exact hf.sub_eq t

theorem exp_signedAngle (t : ℝ) :
    Complex.exp (Complex.I*(signedAngle t:ℂ))=Complex.exp (Complex.I*(t:ℂ)) := by
  apply periodic_signedAngle (fun t : ℝ => Complex.exp (Complex.I*(t:ℂ))) _ t
  intro t
  change Complex.exp (Complex.I*((t+2*Real.pi:ℝ):ℂ))=Complex.exp (Complex.I*(t:ℂ))
  rw [show Complex.I*((t+2*Real.pi:ℝ):ℂ)=Complex.I*(t:ℂ)+2*(Real.pi:ℂ)*Complex.I by push_cast; ring,
    Complex.exp_periodic]

theorem sin_signedAngle (t : ℝ) : Real.sin (signedAngle t)=Real.sin t :=
  periodic_signedAngle Real.sin Real.sin_periodic t

theorem deformedPoint_signedAngles {N : ℕ} (f : SelectorFunctions)
    (hp : Function.Periodic f.p (2*Real.pi)) (hm : Function.Periodic f.m (2*Real.pi))
    (r τ lam : ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    deformedPoint f r τ lam (signedAngles θ) i = deformedPoint f r τ lam θ i := by
  simp only [deformedPoint,retractionShift,occupancy,signedAngles,
    periodic_signedAngle f.p hp,periodic_signedAngle f.m hm,Complex.exp_add,exp_signedAngle]

theorem occupancy_signedAngles {N : ℕ} (f : SelectorFunctions)
    (hp : Function.Periodic f.p (2*Real.pi)) (θ : Fin N → ℝ) :
    occupancy (fun i => f.p (signedAngles θ i))=occupancy (fun i => f.p (θ i)) := by
  simp only [occupancy,signedAngles,periodic_signedAngle f.p hp]

end
end IsingBulk.Tail
