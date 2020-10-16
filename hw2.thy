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

function sum :: "nat ⇒ nat ⇒ nat"
  where "sum i N = (if i > N then 0 else i + sum (Suc i) N)"
  by pat_completeness auto
termination sum
  apply (relation "measure (λ(i,N). N + 1 - i)")
  apply auto
  done

value "sum 1 2"

lemma SumLemma: "VARS (s :: nat) (i :: nat) 
{b≥0}
s:=0;
i:=a;
WHILE i ≤ b
INV { sum a b = s + sum i b }
DO
s := s + i; 
i := i + 1
OD
{s = sum a b   }"
  apply vcg_simp
  done

(*3*)

function perm::"nat list ⇒ nat list ⇒ bool" 
  where "perm [] [] = True" |
"perm [] (y#ys) = False" |
"perm (x#xs) ys = (if length (x#xs) ≠ length ys then False 
                  else perm (removeAll x xs) (removeAll x ys))"
  apply (metis list.exhaust subset_eq_mset_impl.cases)
  apply (auto)
  done


(*4*)

datatype tree0 = Node tree0 tree0 | Nil

fun nodes :: "tree0 ⇒ nat" where
"nodes Nil = 0" |
"nodes (Node l r) = Suc(nodes l + nodes r)"

fun explode :: "nat ⇒ tree0 ⇒ tree0" where
"explode 0 t = t"|
"explode (Suc n) t = explode n (Node t t)"

value "nodes(explode 12 (Node Nil Nil))"
value "2^(12)*(Suc(nodes (Node Nil Nil)))-1"

lemma "nodes(explode n t) = 2^(n)*(Suc(nodes t)) - 1 "
  apply(induction n arbitrary: t)
  apply (auto)
  by (smt add.assoc  mult.assoc  mult.commute  mult_2_right)


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
