theory hw4
  imports Main
begin
(*1*)
lemma neg: "( A \<longrightarrow> False) \<Longrightarrow> \<not> A "
  by (auto)
lemma or: " ((A \<longrightarrow> False) \<longrightarrow> B) \<Longrightarrow>  A \<or> B "
  by (auto)
lemma eq: "((A \<longrightarrow> B) \<and> (B \<longrightarrow> A)) \<Longrightarrow> A = B"
  by(auto)

lemma"A\<or>((B\<and>C) = A)"
  apply(rule or)
  apply(rule impI)
  apply(rule eq)
  oops

(*1*)
lemma I: "A \<longrightarrow> A"
  apply(rule impI)
  apply(assumption)
  done

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply(rule impI)
  apply(rule conjE)
  apply(assumption)
  apply(rule conjI)
  apply(assumption)
  apply(assumption)
  done

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  apply(rule impI)
  apply(erule conjE)
  apply(rule disjI1)
  apply(assumption)
  done

lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
  apply(rule impI)
  apply(erule disjE)
   apply(erule disjE)
  apply(rule disjI1)
    apply(assumption)
   apply(rule disjI2)
   apply(rule disjI1)
   apply(assumption)
   apply(rule disjI2)
   apply(rule disjI2)
  apply(assumption)
  done

lemma K: "A \<longrightarrow> B \<longrightarrow> A"
  apply(rule impI)
 apply(rule impI)
  apply(assumption)
  done

lemma "(A \<or> A) = (A \<and> A)"
  apply(rule iffI)
  apply(rule conjI)
   apply(erule disjE)
    apply(assumption)
   apply(assumption)
  apply(erule disjE)
   apply(assumption)
  apply(assumption)
  apply(erule conjE)
  apply(rule disjI1)
  apply(assumption)
  done

lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  apply(rule impI)
  apply(rule impI)
  apply(rule impI)
  apply(erule impE)
   apply(erule impE)
    apply(assumption)
   apply(assumption)
  apply(erule impE)
   apply(assumption)
  apply(erule impE)
   apply(assumption)
  apply(assumption)
  done

lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
  apply(rule impI)
  apply(rule impI)
  apply(rule impI)
  apply(erule impE)
   apply(assumption)
  apply(erule impE)
   apply(assumption)
  apply(assumption)
  done



lemma "A \<longrightarrow> \<not> \<not> A"
  apply(rule impI)
  apply (rule notI)
  apply (erule notE)
  apply (assumption)
  done

lemma "A \<longrightarrow> \<not> \<not> A"(*using rev_notE*)
  apply(rule impI)
                                               apply (erule rev_notE)
  apply(rule classical)
  apply (erule notE)
  apply(assumption)
  done

lemma "A \<longrightarrow> \<not> \<not> A"
  apply(rule impI)
  apply (rule notI)
  apply (erule notE)
  apply (assumption)
  done


lemma "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
  apply(rule impI)
 apply(rule impI)
  apply(rule classical)
  apply(erule impE)
   apply (assumption)
  apply(erule notE)
  apply(assumption)
  done

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply(rule impI)
  apply(rule classical)
  apply(erule impE)
   apply(rule impI)
  apply(erule notE)
   apply(assumption+)
  done

lemma "A \<or> \<not> A"(*using disjCI*)
                                    apply(rule disjCI)
 apply (rule classical)
  apply (erule notE)
  apply(assumption)
  done

lemma "A \<or> \<not> A"
  apply(rule classical)
  apply(rule disjI1)
  apply(rule classical)
  apply(erule notE)
  apply(rule disjI2)
 apply(assumption)
  done


lemma "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"(*using de_Morgan_conj*)
                             apply(rule de_Morgan_conj)
  done

lemma "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
  apply (rule iffI)
  apply(rule classical)
   apply (erule notE)
  apply(rule conjI)
  apply(rule classical)
    apply (erule notE)
    apply(rule disjI1)
    apply(assumption)
 apply(rule classical)
    apply (erule notE)
    apply(rule disjI2)
    apply(assumption)
   apply (erule disjE)
    apply (rule notI)
    apply (erule notE)
    apply (erule conjE)
    apply (assumption)
   apply (rule notI)
   apply (erule notE)
   apply (erule conjE)
   apply( assumption)
  done
(*----*)

lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
  apply(rule impI)
  apply(rule allI)
  apply(erule exE)
  apply(erule_tac x = "y" in allE)
  apply(rule_tac x = "x" in exI)
  apply(assumption)
  done

lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"(*using rev_notE*)
  apply(rule iffI)
   apply(rule impI)
   apply(rule classical)
                                          apply(erule rev_notE)
   apply(rule notI)
   apply(erule notE)
   apply(erule rev_notE)
   apply(rule notI)
  apply(rule notE)
    apply(assumption)
   apply(erule notE)
   apply(erule exE)
   apply(erule_tac x="x" in allE)
  apply(erule impE)
    apply(assumption+)
  apply(rule allI)
  apply(rule impI)
                                           apply(erule rev_notE)
   apply(rule notI)
  apply(erule notE)
  apply(erule impE)
   apply(rule_tac x="x" in exI)
   apply(assumption+)
  done

lemma "(\<forall>x. P x \<longrightarrow> Q) = ((\<exists>x. P x) \<longrightarrow> Q)"
  apply(rule iffI)
   apply(rule impI)
   apply(erule exE)
   apply(erule allE)
   apply(erule impE)
    apply(assumption+)
  apply(rule allI)
  apply(rule impI)
  apply(erule impE)
   apply(rule exI)
   apply(assumption+)
done

lemma "((\<forall> x. P x) \<and> (\<forall> x. Q x)) = (\<forall> x. (P x \<and> Q x))"
  apply(rule iffI)
   apply(rule allI)
   apply(rule conjI)
    apply(erule conjE)
  apply(erule_tac x="x" in allE)
    apply(assumption)
 apply(erule conjE)
   apply(erule  allE)
  apply(erule_tac x="x" in allE)
   apply(assumption)
  apply(rule conjI)
   apply(rule allI)
   apply(erule_tac x="x" in allE)
   apply(erule conjE)
   apply(assumption)
   apply(rule allI)
 apply(erule_tac x="x" in allE)
   apply(erule conjE)
  apply(assumption)
  done
  

lemma "((\<forall> x. P x) \<or> (\<forall> x. Q x)) = (\<forall> x. (P x \<or> Q x))"
 quickcheck
apply(rule iffI)
   apply(rule allI)
   apply(erule disjE)
    apply(rule disjI1)
  apply(erule_tac x = "x" in allE)
    apply(assumption)
    apply(rule disjI2)
  apply(erule_tac x = "x" in allE)
   apply(assumption)
 (*\<forall>x. P x \<or> Q x \<Longrightarrow> (\<forall>x. P x) \<or> (\<forall>x. Q x)*)
 quickcheck
  oops


lemma "((\<exists> x. P x) \<or> (\<exists> x. Q x)) = (\<exists> x. (P x \<or> Q x))"
apply(rule iffI)
   apply(erule disjE)
    apply(erule exE)
    apply(rule_tac x="x" in exI)
    apply(rule disjI1)
  apply(assumption)
 apply(erule exE)
    apply(rule_tac x="x" in exI)
    apply(rule disjI2)
   apply(assumption)
  apply(erule exE)
  apply(erule disjE)
   apply(rule disjI1)
   apply(rule_tac x="x" in exI)
   apply(assumption)
 apply(rule disjI2)
   apply(rule_tac x="x" in exI)
  apply(assumption)
  done

lemma "(\<forall>x. \<exists>y. P x y) \<longrightarrow> (\<exists>y. \<forall>x. P x y)"
  quickcheck
  apply(rule impI)
  apply(rule_tac x = "y" in exI)
  apply(rule allI)
  apply(erule_tac x = "x" in allE)
       (* \<And>x. \<exists>y. P x y \<Longrightarrow> P x y*)
  apply(erule exE)
 quickcheck
 oops

lemma "(\<not> (\<forall> x. P x)) = (\<exists> x. \<not> P x)"
  apply(rule iffI)
  apply (rule classical)
   apply (erule notE)
   apply(rule allI)
  apply (rule classical)
   apply (erule notE)
  apply(rule_tac x="x" in exI)
   apply(assumption)
  apply(erule rev_notE)
  apply (rule classical)
  apply (erule notE)
  apply( rule notI) 
  apply (erule notE)
  apply (rule notI)
  apply(erule exE)
  apply(erule_tac x="x" in allE)
  apply (erule notE)
   apply(assumption)
  done

end