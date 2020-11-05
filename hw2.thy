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

value "sum 1 4"

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

lemma "VARS (s :: nat) (i :: nat)
{n \<ge> 1}
  s := 0; 
  i := 0;
WHILE i \<le> n
  INV {2 * s = ((i - 1) * i) \<and> (i \<le> n + 1)}
DO
  s := s + i;
  i := i + 1
OD
{2 * s = (n * (n + 1))}"
  apply vcg_simp
   apply (auto simp add: algebra_simps le_Suc_eq)
  done


(*fun sum_upto :: "nat \<Rightarrow> nat"
  where "sum_upto 0 = 0" |
"sum_upto (Suc a) = Suc a + (sum_upto (a))"

lemma eq_sum[simp]:"sum 0 n =sum_upto n"
  apply(induct n)
  oops


lemma nsum[simp]:  "(sum 0 (Suc(n))) = ((sum 0 n) + (sum (Suc(n)) (Suc(n))))"
  apply(induct n)
   apply (simp)
  oops*)
lemma   "(sum 0 n) = (n*(n+1))div 2"
proof(induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case sorry
qed


lemma qsum: "(sum 0 n) = (n*(n+1))div 2"
  apply(induct n)
   apply (simp)
  quickcheck  
                                                                                                     oops

(*3*)
lemma ll[simp]: "length (removeAll x xs) < Suc (length xs)"
  apply(induct xs)
   apply(auto)
  done

function perm::"nat list \<Rightarrow> nat list \<Rightarrow> bool" 
  where "perm [] [] = True" |
"perm [] (y#ys) = False" |
"perm (x#xs) ys = perm (removeAll x xs) (removeAll x ys)"
  apply (metis list.exhaust subset_eq_mset_impl.cases)
  by (auto)
termination perm
 apply (relation "measure (\<lambda>(xs,xy). length(xs) )")
   apply auto
  done

(*4*)

datatype tree0 = Node tree0 tree0 | Nil

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Nil = 0" |
"nodes (Node l r) = Suc(nodes l + nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t"|
"explode (Suc n) t = explode n (Node t t)"

value "nodes(explode 12 (Node Nil Nil))"
value "2^(12)*(Suc(nodes (Node Nil Nil)))-1"

lemma "nodes(explode n t) = 2^(n)*(Suc(nodes t)) - 1 "
  apply(induction n arbitrary: t)
  apply (auto)
  by (smt add.assoc  mult.assoc  mult.commute  mult_2_right)


(*5*)
fun itadd::"nat \<Rightarrow> nat \<Rightarrow> nat"  where 
 "itadd 0 n = n" |
 "itadd (Suc m) n = itadd m (n + 1) " 

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
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