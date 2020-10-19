theory hw3
  imports  
  "HOL-Library.Countable_Set"
  abbrevs "|=0" = "⊨⇩∅" and "||=0" = "⊫⇩∅" and ",," = "⇩♭"
begin
(*1*)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp ⇒ int ⇒ int" where
  "eval Var v = v" |
  "eval (Const e) v = e" |
  "eval (Add e f) v = (eval e v) + (eval f v)" |
  "eval (Mult e f) v = (eval e v) * (eval f v)"

value "eval (Var) 6"

fun evalp :: "int list ⇒ int ⇒ int" where
  "evalp Nil v = 0" |
  "evalp (Cons x xs) v = x + v * (evalp xs v)"

value "evalp [4, 2, -1, 3] 4"
fun add_coeff :: "int list ⇒ int list ⇒ int list" where
  "add_coeff Nil Nil = Nil" |
  "add_coeff Nil ys = ys" |
  "add_coeff xs Nil = xs" |
  "add_coeff (x#xs) (y#ys) = (x+y)#(add_coeff xs ys)"

value "add_coeff [4, 2, -1, 3] [2,3]"

lemma evalp_add[simp] : "evalp (add_coeff xs ys) x = (evalp xs x) + (evalp ys x)"
  apply(induction xs rule: add_coeff.induct)
     apply(auto simp add: algebra_simps)
  done

fun mult :: "int ⇒ int list ⇒ int list" where
  "mult n Nil = Nil" |
  "mult n (x#xs) = (n*x)#(mult n xs)"

lemma evalp_mul[simp] : "evalp (mult n xs) v = n * (evalp xs v)"
  apply(induction xs)
   apply(auto simp add:algebra_simps)
  done

fun mult_coeff :: "int list ⇒ int list ⇒ int list" where
  "mult_coeff Nil ys = Nil" |
  "mult_coeff (x#xs) ys = add_coeff (mult x ys) (0#(mult_coeff xs ys))"

lemma evalp_mult[simp] : "evalp (mult_coeff xs ys) x = (evalp xs x) * (evalp ys x)"
  apply(induction xs)
   apply(auto simp add: algebra_simps)
  done

fun coeff :: "exp ⇒ int list" where
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

abbreviation vx ("❙x") where "❙x ≡ Var"
abbreviation add (infixl "❙+" 65) where "a ❙+ b ≡ Add a b"
abbreviation mul (infixl "❙×" 70) where "a ❙× b ≡ Mult a b"
abbreviation num ("❙_" [1000] 1000) where "❙a ≡ Const a"

no_notation  power2  ("(_⇧2)" [1000] 999)

primrec pow :: "exp ⇒ nat ⇒ exp" ("_⇧_" [1000, 1000] 80)  
  where
  "pow x 0       = ❙1"
| "pow x (Suc n) = x ❙× (pow x n)"

value "eval( ❙4 ❙+ ❙2❙×❙x⇧3 ❙+ ❙(-1) ❙× ❙x⇧2 ❙+ ❙3❙×❙x⇧3) 3"

(*3*)
          
(*4*)

end
