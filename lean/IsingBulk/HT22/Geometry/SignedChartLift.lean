import IsingBulk.HT22.Geometry.SignedAffineCharts

namespace IsingBulk.HT22.Geometry
noncomputable section
open Set Filter Metric IsingBulk.Preferred22
open scoped Topology BigOperators

/-- Exact signed chart identity on the full original one-sided strip,
not just on a postulated support cell. -/
theorem signed_lift_eq_affine_of_strip {n : ℕ} (δ a : ℝ) (l : ℤ) (θ : Fin n → ℝ)
    (hw : ∀ i,constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ i∈
      Ioc (-Real.pi-δ) (-Real.pi-δ+2*Real.pi)) :
    preferredLiftedAngles δ (constrainedAtTotal a θ)=constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ := by
  let hp : 0<2*Real.pi := Real.two_pi_pos
  have hrep (i : Fin (n+1)) := (toIocMod_eq_self hp).mpr (hw i)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hh := hrep (Fin.last n)
    simp only [constrainedAtTotal,Fin.snoc_last] at hh
    have he : (a+2*Real.pi*(l:ℝ))-(∑ j,θ j)=(a-(∑ j,θ j))+l • (2*Real.pi) := by
      rw [zsmul_eq_mul]
      ring
    rw [he,toIocMod_add_zsmul] at hh
    simpa only [preferredLiftedAngles,constrainedAtTotal,Fin.snoc_last,he] using hh
  · simpa only [preferredLiftedAngles,constrainedAtTotal,Fin.snoc_castSucc] using hrep j.castSucc

/-- Every relevant equality center has a genuine open affine chart on
which the actual periodic lift agrees with the literal constrained chart. -/
theorem signed_equality_lift_chart (n : ℕ) (δ a : ℝ) (l : ℤ)
    (hc : (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)∈Ioo (-Real.pi-δ) (-Real.pi-δ+2*Real.pi)) :
    ∃ R : ℝ, 0<R ∧ ∀ θ : Fin n → ℝ,
      ‖θ-(fun _ => (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ))‖<R →
      preferredLiftedAngles δ (constrainedAtTotal a θ)=constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ := by
  let c := (a+2*Real.pi*(l:ℝ))/((n+1:ℕ):ℝ)
  let θ₀ : Fin n → ℝ := fun _ => c
  have he : constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ₀=(fun _ => c) := by
    have hh := constrainedAtTotal_translate_mean n (a+2*Real.pi*(l:ℝ)) (0:Fin n → ℝ)
    have hz : IsingBulk.First.shapeExtend (0:Fin n → ℝ)=0 := by
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [IsingBulk.First.shapeExtend]
    simpa only [hz,Pi.zero_apply,add_zero] using hh
  have hev : ∀ᶠ θ : Fin n → ℝ in 𝓝 θ₀, ∀ i,
      constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ i∈Ioo (-Real.pi-δ) (-Real.pi-δ+2*Real.pi) := by
    apply eventually_all.mpr
    intro i
    have hcont : Continuous (fun θ : Fin n → ℝ => constrainedAtTotal (a+2*Real.pi*(l:ℝ)) θ i) := by
      unfold constrainedAtTotal
      fun_prop
    apply hcont.continuousAt.eventually (Ioo_mem_nhds ?_ ?_)
    · simpa only [he] using hc.1
    · simpa only [he] using hc.2
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨R,hR,?_⟩
  intro θ hθ
  apply signed_lift_eq_affine_of_strip δ a l θ
  intro i
  have hh := hball (show θ∈ball θ₀ R by simpa only [mem_ball,dist_eq_norm] using hθ) i
  exact ⟨hh.1,hh.2.le⟩

end
end IsingBulk.HT22.Geometry
