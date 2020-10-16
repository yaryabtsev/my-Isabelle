theory hw2
imports Main
  "HOL-Hoare.Hoare_Logic"
 "HOL-Library.Permutation" 

begin

(*1*)
lemma DownFact: "VARS (z :: nat) (y :: nat) 
{True}
z:=x;
y:=1;
WHILE z>0
INV { fact x  = y * fact z }
DO
y := y * z; 
z := z-1
OD
{y = fact x}"
  apply vcg_simp
  by (auto simp add: fact_reduce)

(*2*)

function sum :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  where "sum i N = (if i > N then 0 else i + sum (Suc i) N)"
  by pat_completeness auto
termination sum
  apply (relation "measure (\<lambda>(i,N). N + 1 - i)")
  apply auto
  done

value "sum 1 2"

lemma SumLemma: "VARS (s :: nat) (i :: nat) 
{b\<ge>0}
s:=0;
i:=a;
WHILE i \<le> b
INV { sum a b = s + sum i b }
DO
s := s + i; 
i := i + 1
OD
{s = sum a b   }"
  apply vcg_simp
  done

(*3*)
(*5*)
fun itadd::"nat ⇒ nat ⇒ nat"  where 
 "itadd 0 n = n" |
 "itadd (Suc m) n = itadd m (n + 1) " 

fun add :: "nat ⇒ nat ⇒ nat" 
  where "add 0 n = n " |
  "add (Suc m) n = Suc (add m n)"

value "itadd 14 17"
value "add 14 17"

lemma cum_add[simp]: "add m (Suc n) = Suc (add m n)"
  apply (induction m)
   apply auto
  done

lemma addEquals : "itadd m n = add m n"
apply (induction m  arbitrary: n)
  apply (auto)
  done

end
