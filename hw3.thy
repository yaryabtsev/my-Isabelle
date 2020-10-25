theory hw3
  imports  
  "HOL-Library.Countable_Set"
  abbrevs "|=0" = "\<Turnstile>\<^sub>\<emptyset>" and "||=0" = "\<TTurnstile>\<^sub>\<emptyset>" and ",," = "\<^sub>\<flat>"
begin
(*1*)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var v = v" |
  "eval (Const e) v = e" |
  "eval (Add e f) v = (eval e v) + (eval f v)" |
  "eval (Mult e f) v = (eval e v) * (eval f v)"

value "eval (Var) 6"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp Nil v = 0" |
  "evalp (Cons x xs) v = x + v * (evalp xs v)"

value "evalp [4, 2, -1, 3] 4"
fun add_coeff :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "add_coeff Nil Nil = Nil" |
  "add_coeff Nil ys = ys" |
  "add_coeff xs Nil = xs" |
  "add_coeff (x#xs) (y#ys) = (x+y)#(add_coeff xs ys)"

value "add_coeff [4, 2, -1, 3] [2,3]"

lemma evalp_add[simp] : "evalp (add_coeff xs ys) x = (evalp xs x) + (evalp ys x)"
  apply(induction xs rule: add_coeff.induct)
     apply(auto simp add: algebra_simps)
  done

fun mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "mult n Nil = Nil" |
  "mult n (x#xs) = (n*x)#(mult n xs)"

lemma evalp_mul[simp] : "evalp (mult n xs) v = n * (evalp xs v)"
  apply(induction xs)
   apply(auto simp add:algebra_simps)
  done

fun mult_coeff :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "mult_coeff Nil ys = Nil" |
  "mult_coeff (x#xs) ys = add_coeff (mult x ys) (0#(mult_coeff xs ys))"

lemma evalp_mult[simp] : "evalp (mult_coeff xs ys) x = (evalp xs x) * (evalp ys x)"
  apply(induction xs)
   apply(auto simp add: algebra_simps)
  done

fun coeff :: "exp \<Rightarrow> int list" where
"coeff Var = [0,1]" |
"coeff (Const i) = [i]" |
"coeff (Add e f) = add_coeff (coeff e) (coeff f)" |
"coeff (Mult e f) = mult_coeff (coeff e) (coeff f)"

value "coeff (Add (Mult (Const 2) Var) (Mult (Const (-1)) (Mult Var Var)))"

theorem preservation : "evalp (coeff e) x = eval e x"
  apply(induction e arbitrary: x)
  using [[simp_trace]]
     apply(auto)
  done

(*2*)

abbreviation vx ("\<^bold>x") where "\<^bold>x \<equiv> Var"
abbreviation add (infixl "\<^bold>+" 65) where "a \<^bold>+ b \<equiv> Add a b"
abbreviation mul (infixl "\<^bold>\<times>" 70) where "a \<^bold>\<times> b \<equiv> Mult a b"
abbreviation num ("\<^bold>_" [1000] 1000) where "\<^bold>a \<equiv> Const a"

no_notation  power2  ("(_\<^sup>2)" [1000] 999)

primrec pow :: "exp \<Rightarrow> nat \<Rightarrow> exp" ("_\<^sup>_" [1000, 1000] 80)  
  where
  "pow x 0       = \<^bold>1"
| "pow x (Suc n) = x \<^bold>\<times> (pow x n)"

value "eval( \<^bold>4 \<^bold>+ \<^bold>2\<^bold>\<times>\<^bold>x\<^sup>3 \<^bold>+ \<^bold>(-1) \<^bold>\<times> \<^bold>x\<^sup>2 \<^bold>+ \<^bold>3\<^bold>\<times>\<^bold>x\<^sup>3) 3"

(*3*)
datatype boolex = Const bool | Var nat | Neg boolex | And boolex boolex

primrec "value" :: "boolex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
"value (Const b) env = b" |
"value (Var x) env = env x" |
"value (Neg b) env = (\<not> value b env)" |
"value (And b c) env = (value b env \<and> value c env)"

datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex

primrec valif :: "ifex \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
"valif (CIF b) env = b" |
"valif (VIF x) env = env x" |
"valif (IF b t e) env = (if valif b env then valif t env else valif e env)"

primrec bool2if :: "boolex \<Rightarrow> ifex" where
"bool2if (Const b) = CIF b" |
"bool2if (Var x) = VIF x" |
"bool2if (Neg b) = IF (bool2if b) (CIF False) (CIF True)" |
"bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)"

lemma "valif (bool2if b) env = value b env"
  apply(induct_tac b)
  apply(auto)
  done

(*4*)
locale Geom =
  fixes on :: "'p \<Rightarrow> 'l \<Rightarrow> bool"
  assumes line_on_two_pts: "a \<noteq> b \<Longrightarrow> \<exists>l. on a l \<and> on b l" 
  and line_on_two_pts_unique: 
  "\<lbrakk> a \<noteq> b; on a l; on b l; on a m; on b m \<rbrakk> \<Longrightarrow> l = m"
  and two_points_on_line: "\<exists>a b. a \<noteq> b \<and> on a l \<and> on b l"
  and three_points_not_on_line: "\<exists>a b c. a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c \<and> \<not> (\<exists>l. on a l \<and> on b l \<and> on c l)"
begin
  

lemma three_points_not_on_line_alt:
  "\<exists>a b c. a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c \<and> (\<forall>l. on a l \<and> on b l \<longrightarrow> \<not> on c l)"
proof -
  obtain a b c 
    where distinct: "a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c" 
                    "\<not> (\<exists>l. on a l \<and> on b l \<and> on c l)" 
    using three_points_not_on_line by blast
  then have "\<forall>l. on a l \<and> on b l \<longrightarrow> \<not> on c l"
    by blast
  thus ?thesis using distinct by blast
qed        
  
lemma exists_pt_not_on_line: "\<exists>x. \<not> on x l"
proof -
   obtain a b c where l3: "\<not> (on a l \<and> on b l \<and> on c l)" using three_points_not_on_line by blast 
   thus ?thesis by blast 
 qed

lemma two_lines_unique_intersect_pt:
  assumes lm: "l\<noteq>m \<and> on x l \<and> on x m \<and> on y l \<and> on y m" shows "x=y"
proof(rule ccontr)
  assume "x\<noteq>y" then have "l=m" using line_on_two_pts_unique assms by blast
  thus False using lm by simp
qed

end

end