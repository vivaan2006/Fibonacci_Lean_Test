import data.nat.basic
import data.nat.fib
import data.nat.gcd
import data.nat.prime
import tactic

coinductive fib_seq : Type
| zero : fib_seq
| succ : fib_seq → fib_seq → fib_seq

cofix generate_fib : fib_seq :=
fib_seq.succ fib_seq.zero generate_fib

def fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := fib n + fib (n + 1)

-- somehow evaluate correctness?
lemma fibonacci_correct : ∀ n, fib_seq.nth n = fib n :=
begin
  intro n,
  induction n with d hd,
  { refl },
  { cases d,
    { refl },
    { rw [fib_seq.nth_succ_succ, hd (fib_seq.succ fib_seq.zero generate_fib)],
      simp only [fib, add_zero, add_comm] } }
end

 -- get the PNS
def is_prime (n : ℕ) : Prop :=
n ≥ 2 ∧ ∀ m : ℕ, m > 1 → m ∣ n → m = n

cofix generate_primes : fib_seq :=
if is_prime (fib_seq.nth 0) then
  fib_seq.succ fib_seq.zero generate_primes
else
  generate_primes

-- check?
lemma primes_correct : ∀ n, is_prime (fib_seq.nth n) :=
begin
-- start check ehre
end

def main : io unit :=
do
  io.put_str_ln "Fibonacci Sequence:"
  let seq := generate_fib,
  io.put_str_ln $ to_string $ fib_seq.nth 0 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 1 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 2 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 3 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 4 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 5 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 6 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 7 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 8 seq,
  io.put_str_ln $ to_string $ fib_seq.nth 9 seq,
  
  io.put_str_ln "Prime Numbers:"
  let primes_seq := generate_primes,
  io.put_str_ln $ to_string $ fib_seq.nth 0 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 1 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 2 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 3 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 4 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 5 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 6 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 7 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 8 primes_seq,
  io.put_str_ln $ to_string $ fib_seq.nth 9 primes_seq

def main_run : io unit :=
main io.env_args
#eval main_run
