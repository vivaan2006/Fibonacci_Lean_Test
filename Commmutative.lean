-- 25:6:error: rewrite tactic failed, lemma is not an equality nor a iff
-- state:
-- n : my_nat,
-- ih' : my_add my_nat.zero n = my_add n my_nat.zero
-- ⊢ my_nat.succ (my_add n my_nat.zero) = my_nat.succ n

inductive my_nat
| zero : my_nat
| succ : my_nat → my_nat

def my_add : my_nat → my_nat → my_nat
| m my_nat.zero     := m
| m (my_nat.succ n) := my_nat.succ (my_add m n)

theorem my_add_comm : ∀ (m n : my_nat), my_add m n = my_add n m :=

begin
  intros m n,
  induction m with m ih,
  { 
    induction n with n ih',
    
    {
      refl,
    },
    
    { 
      simp [my_add],
      rw [ih', my_nat.succ],
    },
  },
  
  { 
    intro n,
    simp [my_add, ih],
    induction n with n ih',
    
    {
      simp [my_add],
    },
    
    {
      simp [my_add],
      exact ih', 
    },
    
  },
  
end
