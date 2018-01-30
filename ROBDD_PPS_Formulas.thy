subsection\<open>ROBDDs and Formulas\<close>
theory ROBDD_PPS_Formulas
imports "ROBDD.Level_Collapse" "Propositional_Proof_Systems.Sema"
begin

primrec frm_to_bdd where
"frm_to_bdd \<bottom> s = fci s" |
"frm_to_bdd (Atom a) s = litci a s" |
"frm_to_bdd (Not F) s = do {
  (n,s) \<leftarrow> frm_to_bdd F s;
  notci n s
}" |
"frm_to_bdd (And F G) s = do {
  (f,s) \<leftarrow> frm_to_bdd F s;
  (g,s) \<leftarrow> frm_to_bdd G s;
  andci f g s
}" |
"frm_to_bdd (Or F G) s = do {
  (f,s) \<leftarrow> frm_to_bdd F s;
  (g,s) \<leftarrow> frm_to_bdd G s;
  orci f g s
}" |
"frm_to_bdd (Imp F G) s = do {
  (f,s) \<leftarrow> frm_to_bdd F s;
  (n,s) \<leftarrow> notci f s;
  (g,s) \<leftarrow> frm_to_bdd G s;
  orci n g s
}"

lemma frm_to_bdd_sep[sep_heap_rules]: "
<bdd_relator R s> 
  frm_to_bdd F s
<\<lambda>(r,s'). bdd_relator (insert (\<lambda>\<A>. \<A> \<Turnstile> F, r) R) s'>\<^sub>t"
  by(induction F arbitrary: R s; sep_auto simp add: fun_eq_iff bf_lit_def)  

theorem "<emp> do {
  s \<leftarrow> emptyci;
  (f,s) \<leftarrow> frm_to_bdd F s;
  tautci f s
} <\<lambda>r. \<up>(r \<longleftrightarrow> \<Turnstile> F)>\<^sub>t"
  by(sep_auto simp add: fun_eq_iff)

end