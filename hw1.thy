theory 1
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


lemma snoc_rev[simp] : "snoc (reverse xs) a = reverse (a # xs)"
  apply(induction xs)
  apply(auto)
  done

lemma rev_reverse[simp] : "reverse (reverse xs) = xs"
  apply(induction xs)
    apply(auto)
  done
  (*oops*)

(*5.*)
fun sum_upto :: "nat \<Rightarrow> nat"
  where "sum_upto 0 = 0" |
"sum_upto a = add a (sum_upto (a - 1))"

fun sum :: "nat list \<Rightarrow> nat"
  where "sum [] = 0" | 
"sum (x#xs) = add x (sum xs)"

fun mk_list :: "nat \<Rightarrow> nat list"
  where "mk_list 0 = []" |
"mk_list a = snoc (mk_list (a-1)) a"

fun sum_upto' :: "nat \<Rightarrow> nat"
  where "sum_upto' 0 = sum []" |
"sum_upto' a = sum (mk_list a)"

value "sum_upto 10"
value "sum_upto' 10"
value "sum_upto 6"
value " add 5 (Suc ((5 + 5 * 5) div 2))"
value "sum [0, 1, 2]"
value "mk_list 10"

lemma next_sum[simp] : "add (sum_upto a) (Suc(a)) = sum_upto(Suc(a))"
  apply(induction a)
   apply(auto)
  done

lemma next_sum'[simp] : "snoc (mk_list a) (Suc a) = mk_list(Suc a)"
  apply(induction a)
   apply(auto)
  done

lemma auto_sum[simp] : "sum_upto' a = ((a * (a + 1)) div 2)"
  apply(induction a)
    apply(auto)
  done
  (*oops*)

end
