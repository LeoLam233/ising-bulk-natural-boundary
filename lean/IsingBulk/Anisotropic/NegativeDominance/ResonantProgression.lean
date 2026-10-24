import IsingBulk.Anisotropic.NegativeDominance.PhysicalMiddleSum

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

def resonantParticle (p k : ℕ) : ℕ := p*(2*k+1)

theorem odd_dvd_resonant_iff {p N : ℕ} (hp : Odd p) :
    Odd N ∧ p∣N ↔ ∃k,N=resonantParticle p k := by
  constructor
  · rintro ⟨ho,m,rfl⟩
    obtain ⟨k,hk⟩ := Nat.Odd.of_mul_right ho
    exact ⟨k,by rw [hk]; rfl⟩
  · rintro ⟨k,rfl⟩
    exact ⟨hp.mul ⟨k,rfl⟩,dvd_mul_right p _⟩

theorem resonantParticle_injective {p : ℕ} (hp : 0<p) :
    Function.Injective (resonantParticle p) := by
  intro a b hab
  unfold resonantParticle at hab
  have hh := Nat.eq_of_mul_eq_mul_left hp hab
  omega

theorem resonantParticle_forward (p c i : ℕ) (hci : c≤ i) :
    resonantParticle p c+2*p*(i-c)=resonantParticle p i := by
  calc
    _=p*(2*(c+(i-c))+1) := by unfold resonantParticle; ring
    _=_ := by rw [Nat.add_sub_of_le hci]; rfl

theorem resonantParticle_backward (p c i : ℕ) (hic : i≤c) :
    resonantParticle p c-2*p*(c-i)=resonantParticle p i := by
  have he : resonantParticle p c=resonantParticle p i+2*p*(c-i) :=
    (resonantParticle_forward p i c hic).symm
  rw [he,Nat.add_sub_cancel]

theorem resonantParticle_backward_le (p c i : ℕ) (hic : i≤c) :
    2*p*(c-i)≤resonantParticle p c := by
  rw [←resonantParticle_forward p i c hic]
  omega

/-- Reindexing a finite set of resonant particle orders around one peak
covers every other order, both above and below it. -/
theorem finite_resonant_sum_partition (p c : ℕ) (I : Finset ℕ) (hc : c∉I)
    (F : ℕ→ℝ) :
    (∑i∈I,F (resonantParticle p i))=
      (∑k∈(I.filter (fun i => c< i)).image (fun i => i-c),F (resonantParticle p c+2*p*k))+
      (∑k∈(I.filter (fun i => i<c)).image (fun i => c-i),F (resonantParticle p c-2*p*k)) := by
  classical
  rw [Finset.sum_image (by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    dsimp only at hab
    omega),Finset.sum_image (by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    dsimp only at hab
    omega)]
  have hf : (∑i∈I.filter (fun i => c< i),F (resonantParticle p c+2*p*(i-c)))=
      ∑i∈I.filter (fun i => c< i),F (resonantParticle p i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [resonantParticle_forward p c i (Nat.le_of_lt (Finset.mem_filter.mp hi).2)]
  have hb : (∑i∈I.filter (fun i => i<c),F (resonantParticle p c-2*p*(c-i)))=
      ∑i∈I.filter (fun i => i<c),F (resonantParticle p i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [resonantParticle_backward p c i (Nat.le_of_lt (Finset.mem_filter.mp hi).2)]
  rw [hf,hb]
  have hfilter : I.filter (fun i => ¬c< i)=I.filter (fun i => i<c) := by
    ext i
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨hi,hh⟩
    · refine ⟨hi,?_⟩
      have hic : i≠c := by intro he; subst i; exact hc hi
      omega
    · exact ⟨hi,by omega⟩
  rw [←hfilter,Finset.sum_filter_add_sum_filter_not]

end
end IsingBulk.Anisotropic.NegativeDominance
