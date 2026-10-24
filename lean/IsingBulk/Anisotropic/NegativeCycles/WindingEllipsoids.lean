import IsingBulk.Anisotropic.NegativeCycles.WindingPartition

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set
open scoped BigOperators

def windingAffine (n : ℕ) (k : Fin (n+2)) (v : Fin n→ℝ) : Fin (n+1)→ℝ :=
  Fin.snoc v ((2*(k.val:ℝ)-(n+1:ℕ))*Real.pi-∑i,v i)

@[simp] theorem windingAffine_sum (n : ℕ) (k : Fin (n+2)) (v : Fin n→ℝ) :
    (∑i,windingAffine n k v i)=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi := by
  rw [Fin.sum_univ_castSucc]
  simp [windingAffine]

theorem wrapAngle_eq_of_mem_Ioo {x : ℝ} (hx : x∈Ioo (-Real.pi) Real.pi) : wrapAngle x=x :=
  Real.Angle.toReal_coe_eq_self_iff.mpr ⟨hx.1,hx.2.le⟩

theorem negativeShiftedAngles_eq_windingAffine_of_small (n : ℕ) (k : Fin (n+2))
    (v : Fin n→ℝ) (hsmall : ∀i,windingAffine n k v i∈Ioo (-Real.pi) Real.pi) :
    negativeShiftedAngles n v=windingAffine n k v := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [negativeShiftedAngles_last]
    have he : -(∑j,v j)-(n+1:ℕ)*Real.pi=
        windingAffine n k v (Fin.last n)-(k.val:ℝ)*(2*Real.pi) := by
      simp only [windingAffine,Fin.snoc_last]
      ring
    rw [he]
    have hp := wrapAngle_sub_int_period (windingAffine n k v (Fin.last n)) (k.val:ℤ)
    push_cast at hp
    rw [hp]
    exact wrapAngle_eq_of_mem_Ioo (hsmall _)
  · rw [negativeShiftedAngles_castSucc]
    simpa [windingAffine] using wrapAngle_eq_of_mem_Ioo (hsmall j.castSucc)

theorem negativeShiftedAngles_eq_windingAffine_of_sector (n : ℕ) (k : Fin (n+2))
    (v : Fin n→ℝ) (hv : ∀i,v i∈Ioo (-Real.pi) Real.pi) (hk : v∈windingSector n k) :
    negativeShiftedAngles n v=windingAffine n k v := by
  have hc (i : Fin n) : negativeShiftedAngles n v i.castSucc=v i := by
    rw [negativeShiftedAngles_castSucc,wrapAngle_eq_of_mem_Ioo (hv i)]
  have hs := hk
  change (∑i,negativeShiftedAngles n v i)=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi at hs
  rw [Fin.sum_univ_castSucc] at hs
  simp only [hc] at hs
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [windingAffine,Fin.snoc_last]
    linarith
  · simpa [windingAffine] using hc j

theorem coordinate_mem_Ioo_of_energy {N : ℕ} (q : Fin N→ℝ)
    (hq : (∑i,q i^2)<Real.pi^2) (i : Fin N) : q i∈Ioo (-Real.pi) Real.pi := by
  have hi := Finset.single_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin N))) => sq_nonneg (q j)) (Finset.mem_univ i)
  constructor <;> nlinarith [Real.pi_pos]

/-- The actual inner winding sector is exactly the affine constrained ellipsoid.
In particular the odd sectors are not centered at zero in physical angles. -/
theorem actual_inner_winding_eq_ellipsoid (n : ℕ) (k : Fin (n+2)) (σ : ℝ)
    (hσ : σ≤Real.pi^2) :
    {v : Fin n→ℝ | v∈Icc (fun _ => -Real.pi) (fun _ => Real.pi) ∧
      v∈windingSector n k ∧ (∑i,(negativeShiftedAngles n v i)^2)<σ}=
    {v : Fin n→ℝ | (∑i,(windingAffine n k v i)^2)<σ} := by
  ext v
  constructor
  · rintro ⟨hbox,hk,hq⟩
    have hi : ∀i,v i∈Ioo (-Real.pi) Real.pi := by
      intro i
      have hδ := coordinate_mem_Ioo_of_energy (negativeShiftedAngles n v) (hq.trans_le hσ) i.castSucc
      have he := norm_wrapAngle_of_mem (show v i∈Icc (-Real.pi) Real.pi from ⟨hbox.1 i,hbox.2 i⟩)
      have hsq : (wrapAngle (v i))^2=(v i)^2 := by
        have hh := congrArg (fun r : ℝ => r^2) he
        simp only [Real.norm_eq_abs] at hh
        rw [_root_.sq_abs,_root_.sq_abs] at hh
        exact hh
      rw [negativeShiftedAngles_castSucc] at hδ
      constructor <;> nlinarith [hδ.1,hδ.2,Real.pi_pos]
    rwa [negativeShiftedAngles_eq_windingAffine_of_sector n k v hi hk] at hq
  · intro hq
    have hi := coordinate_mem_Ioo_of_energy (windingAffine n k v) (hq.trans_le hσ)
    have he := negativeShiftedAngles_eq_windingAffine_of_small n k v hi
    refine ⟨⟨?_,?_⟩,?_,?_⟩
    · intro i
      simpa [windingAffine] using (hi i.castSucc).1.le
    · intro i
      simpa [windingAffine] using (hi i.castSucc).2.le
    · change (∑i,negativeShiftedAngles n v i)=(2*(k.val:ℝ)-(n+1:ℕ))*Real.pi
      rw [he,windingAffine_sum]
    · rwa [he]

end IsingBulk.Anisotropic.NegativeCycles
