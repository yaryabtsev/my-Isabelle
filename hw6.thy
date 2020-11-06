theory hw6
  imports 
Complex_Main
  "HOL-Library.Multiset"
begin
fun insert :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  where
 "insert a [] = [a]"
|"insert a (x#xs) = 
(if a \<le> x then a#x#xs else x#insert a xs)"

thm insert.elims
value "insert 7 [328,4,6,78]"
  
fun sort :: "nat list \<Rightarrow> nat list"
  where
  "sort [] = []"
| "sort (x#xs) = insert x (sort xs)"

value "sort [3,7,34,6,0,3,4]"

fun isort_key :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"isort_key f [] = []" |
"isort_key f (x # xs) = insort_key f x (isort_key f xs)"

fun find_eq :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  where
  "find_eq a [] = False"
| "find_eq a (x#xs) = (if (x=a) then True else find_eq a xs)"

fun equal :: "nat list \<Rightarrow> nat list \<Rightarrow> bool"
  where
 "equal [] [] = True" |
 "equal [] (y#ys) = False" |
 "equal (x#xs) ys = ( (find_eq x ys) \<and> equal xs (remove1 x ys))"

lemma "equal x x"
proof(induction x)
 case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case by simp
qed

lemma "equal x y = equal y x"
proof(induction x)
  case Nil
  then show ?case proof(induction y)
    case Nil
    then show ?case by simp
  next
    case (Cons a y)
    then show ?case by simp
  qed
next
  case (Cons a x)
  then show ?case proof(induction y)
    case Nil
    then show ?case  by simp
  next
    case (Cons a y)
    then show ?case   sorry

  qed
qed

lemma "(equal x y \<and> equal y z) \<Longrightarrow> equal x z"              
proof(induct x)
  case Nil
  then show ?case proof(induct z)
    case Nil
    then show ?case by simp
  next
    case (Cons a z)
    then show ?case
    proof -
      show ?thesis
        by (metis (no_types) Cons.prems equal.simps(2) sort.cases)
    qed
  qed
next
  case (Cons a x)
  then show ?case proof(induct z)
    case Nil
    then show ?case
    proof -
      show ?thesis
        by (metis (no_types) Nil.prems(2) equal.elims(2) find_eq.simps(1))
    qed
  next
    case (Cons a z)
    then show ?case sorry
  qed
qed

lemma "sort (sort x) = sort x"


proof(induct x)
  case Nil
  then show ?case by simp
next
  case (Cons a x)
  then show ?case sorry
qed

lemma sorted_isort_key: "sorted (map f (isort_key f xs))"
by(induction xs)(simp_all add: sorted_insort_key)
lemma filter_insort_key_neg:
  "\<not> P x \<Longrightarrow> filter P (insort_key f x xs) = filter P xs"
by (induction xs) simp_all

lemma filter_insort_key_pos:
  "sorted (map f xs) \<Longrightarrow> P x \<Longrightarrow> filter P (insort_key f x xs) = insort_key f x (filter P xs)"
  by (induction xs) (auto, subst insort_is_Cons, auto)

lemma sort_key_stable: "filter (\<lambda>y. f y = k) (isort_key f xs) = filter (\<lambda>y. f y = k) xs"
proof (induction xs)
  case Nil thus ?case by simp
next
  case (Cons a xs)
  thus ?case
  proof (cases "f a = k")
    case False thus ?thesis  by (simp add: Cons.IH filter_insort_key_neg)
  next
    case True
    have "filter (\<lambda>y. f y = k) (isort_key f (a # xs))
      = filter (\<lambda>y. f y = k) (insort_key f a (isort_key f xs))"  by simp
    also have "\<dots> = insort_key f a (filter (\<lambda>y. f y = k) (isort_key f xs))"
      by (simp add: True filter_insort_key_pos sorted_isort_key)
    also have "\<dots> = insort_key f a (filter (\<lambda>y. f y = k) xs)"  by (simp add: Cons.IH)
    also have "\<dots> = a # (filter (\<lambda>y. f y = k) xs)"  by(simp add: True insort_is_Cons)
    also have "\<dots> = filter (\<lambda>y. f y = k) (a # xs)" by (simp add: True)
    finally show ?thesis .
  qed
qed

lemma assumes T : "\<forall> x y. T x y \<or> T y x"
and A: "\<forall> x y. A x y \<and> A y x \<longrightarrow> x = y"
and TA: "\<forall> x y. T x y \<longrightarrow> A x y" and "A x y"
shows "T x y"
  using A T TA assms(4) by blast


lemma "\<exists> ys zs. xs = ys @ zs \<and>
(length ys = length zs \<or> length ys = length zs + 1)"
oops

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS : "ev n \<Longrightarrow> ev (Suc(Suc n))"

lemma assumes a: "ev (Suc(Suc n))" shows "ev n"
proof -
  obtain nn :: "nat \<Rightarrow> nat" where
    "Suc (Suc n) = Suc (Suc (nn (Suc (Suc n)))) \<and> ev (nn (Suc (Suc n)))"
    by (metis (no_types) assms ev.cases old.nat.distinct(2))
  then show ?thesis
    by (metis Suc_inject)
qed


lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof -
  have "\<forall>n na. Suc n \<noteq> Suc na \<or> n = na"
    by (meson Suc_inject)
then show ?thesis
by (metis (no_types) ev.simps old.nat.distinct(2))
qed
end

