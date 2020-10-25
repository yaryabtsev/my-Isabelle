theory hw1
imports Main
begin

(*1.*)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(*2.*)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" 
  where "add 0 n = n " |
  "add (Suc m) n = Suc (add m n)"

lemma null_add[simp]: "add y 0 = y"
  apply (induction y)
   apply auto
  done

lemma ass_add[simp]: "add (add x y) z = add x (add y z)"
  apply (induction x)
   apply auto
  done

lemma suc_ass[simp]: "Suc (add y x) = add y (Suc x)"
  apply (induction y)
   apply auto
  done

lemma cum_add[simp]: "add x y = add y x"
  apply (induction x)
   apply auto
  done

fun double  :: "nat \<Rightarrow> nat"
  where "double  0 =  0" |
"double (Suc x) = Suc (Suc (double x))"

lemma double_prop[simp] : "double x = add x x"
  apply (induction x)
   apply (auto)
  done

(*3.*)
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
  where  "count a [] = 0" |
"count a (x#xs) = (if a = x then add 1 (count a xs) else count a xs)"

value "count (2::nat) [2, 0, 2, 2, 1, 0, 1, 1, 2, 0, 2, 2, 1]"

lemma max_count[simp] : "count a xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

(*4.*)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
  where  "snoc [] a = [a]" |
"snoc (x#xs) a= x#snoc xs a"

value "snoc [2, 0, 2, 2, 1, 0, 1, 1, 2, 0, 2, 2, 1::int] 0"

fun reverse :: "'a list \<Rightarrow> 'a list"
  where "reverse [] = []" |
"reverse (x#xs) = snoc (reverse xs) x"

value "reverse [2, 0, 2, 2, 1, 0, 1, 1, 2, 0, 2, 2, 1::int]"

lemma about_reverse2[simp] : " reverse(snoc xs a) = (a # reverse(xs)) "
  apply (induction xs)
   apply (auto)
  done
lemma snoc_rev[simp] : " reverse (a # xs) = snoc (reverse xs) a "
  apply(induction xs)
  apply(auto)
  done

lemma rev_reverse[simp] : "reverse (reverse xs) = xs"
  apply(induction xs)
  apply auto
  done

(*5.*)
fun sum_upto :: "nat \<Rightarrow> nat"
  where "sum_upto 0 = 0" |
"sum_upto (Suc a) = Suc a + (sum_upto (a))"

value "sum_upto 10"

lemma auto_sum[simp] : "sum_upto a = ((a * (a + 1)) div 2)"
  apply(induction a)
  apply auto
  done

end